module TypeChecker

open Ast
open Ast_util
open Parse
open Microsoft.FSharp.Math
open System.Collections.Generic
open System.IO
open System
open Microsoft.FSharp.Text.Lexing

let string_of_typ = Emit_vale_text.string_of_typ
let t_int = TInt (NegInf, Inf)
let t_bool = TName (Id "bool")
let t_prop = TName (Id "prop")

let tvar_count = ref 0
let reset_type_vars () =
  tvar_count := 0
let next_type_var ():typ =
  let tvar = "u" + string (!tvar_count) in
  incr tvar_count;
  TVar (Id tvar, None)

type norm_typ = {norm_typ:typ}

type typ_constraint =
| TcEqual of typ * typ // t1 = t2
| TcSubtype of typ * typ // t1 <: t2
type typ_constraints = typ_constraint list
type substitutions = Map<id, typ>

type decl_type =
  {
    tformals:pformal list;
    targs:typ list;
    trets:typ list;
    ret_name:id option;
    specs:(loc * spec) list;
    attrs:attrs;
  }

type id_info = StateInfo of string | OperandLocal of typ | InlineLocal

type name_info =
| Info of typ * id_info option
| Func_decl of decl_type
| Proc_decl of decl_type // second proc_decl is for raw_proc
| Type_info of (tformal list * kind * typ option)
| Name of id

type scope_mod =
| Include_module of (string * bool)
| Module_abbrev of (string * string)
| Variable of (id * typ * id_info option)
| Func of (id * decl_type)
| Proc of (id * decl_type)
| Type of (id * tformal list * kind * typ option)
| Const of (id * typ)
| Unsupported of id

type transform_kind =
| EvalOp
| OperandTyp
| StateGet
| EvalState of (string * string)
| Coerce of (string * string)
| ConstOp of string
| EApplyCode

type env =
  {
    declsmap:Map<id, name_info>; // map id to the decl info
    scope_mods:list<scope_mod>; // a STACK of scope modifiers
    ghost:bool; // HACK: used for transform parameter types. Won't need it if transform is done before typechecker.
  }

let empty_env:env= {declsmap = Map.empty; scope_mods=[]; ghost = false}

// type annotated expression
// annotated with the inferred type and expected type
// If these two types are not equal, insert a cast
type aexp_t =
| AE_Loc of loc * aexp
| AE_Exp of exp
| AE_Op of op * aexp list
| AE_Apply of id * aexp list
| AE_Bind of bindOp * aexp list * formal list * triggers * aexp
| AE_Cast of aexp * typ
and aexp = aexp_t * (typ * typ) option

let name_of_id x =
  let s = match x with Id s | Reserved s | Operator s -> s in
  let es = s.Split ([|'.'|])  |> Array.toList in
  let rec aux s l =
    match l with
    | hd :: [] -> (s, hd)
    | hd :: tl -> aux (if (s = "") then hd else (s ^ "." ^ hd)) tl
    | _ -> failwith "Empty list." in
  let (mn, sn) = aux "" es in
  match x with
  | Id _ -> (mn, Id sn)
  | Reserved _ -> (mn, Reserved sn)
  | Operator _ -> (mn, Operator sn)

let lookup_name (env:env) (x:id) (include_import:bool):(name_info option * id) =
  let find = function
  | Variable (s, t, info) when s = x -> (Some (Info (t, info)), x)
  | Func (s, decl) when s = x -> (Some (Func_decl decl), x)
  | Proc (s, decl) when s = x -> (Some (Proc_decl decl), x)
  | Type (s, ts, kind, t) when s = x -> (Some (Type_info (ts, kind, t)), x)
  | Const (s, t) when s = x -> (Some (Info (t, None)), x)
  | Unsupported (s) when s = x -> (Some (Name s), x)
  | Include_module (s, opened) when include_import ->
    let r = Map.tryFind x env.declsmap in
    match r with
    | Some r -> (Some r, x)
    | _ ->
      // for non-qualified reference, the module has to be opened
      let qx = Id (s + "." + (string_of_id x)) in
      match Map.tryFind qx env.declsmap with
      | Some r -> if opened then (Some r, qx) else err (sprintf "module %s needs to be opened to reference %A" s x)
      | _ -> (None, x)
  | _ -> (None, x)
  let rec aux = function
  | a :: q ->
    match (find a) with
    | (Some r, x) -> (Some r, x)
    | _ -> aux q
  | [] ->
    (None, x)
  aux env.scope_mods

let push_scope_mod env scope_mod =
 {env with scope_mods = scope_mod :: env.scope_mods}

let try_lookup_id (env:env) (x:id):(typ * id_info option) option =
  match lookup_name env x true with
  | (Some (Info (t, info)), _) -> Some (t, info)
  | (Some (Name x), _) -> unsupported ("unsupported '" + (err_id x) + "'")
  | _ -> None

let lookup_id (env:env) (x:id):(typ * id_info option) =
  match try_lookup_id env x with
  | Some (t, info) -> (t, info)
  | _ -> err ("cannot find id '" + (err_id x) + "'")

let try_lookup_type (env:env) (x:id):((typ option * kind) option * id) =
  let (t, qx) = lookup_name env x true in
  match t with
  | Some (Type_info (ts, k, t)) -> (Some (t, k), qx)
  | Some (Name x) -> unsupported ("unsupported '" + (err_id x) + "'")
  | _ -> (None, x)

let lookup_type (env:env) (x:id):(typ option * kind) =
  match try_lookup_type env x with
  | (Some info, x) -> info
  | _ -> err ("cannot find type '" + (err_id x) + "'")

let try_lookup_proc (env:env) (x:id):(decl_type option * bool) =
  match lookup_name env x true with
  | (Some (Proc_decl t), _) -> (Some t, false)
  | (Some (Func_decl t), _) -> (Some t, true)
  | (Some (Name x), _) -> unsupported ("unsupported '" + (err_id x) + "'")
  | _ -> (None, false)

let lookup_proc (env:env) (x:id):(decl_type * bool) =
  let x = if x = Id "not" then Id "Prims.l_not" else x in
  match try_lookup_proc env x with
  | (Some t, b) -> (t, b)
  | _ -> err ("cannot find fun/proc '" + (err_id x) + "'")

let rec normalize_type_rec (env:env) (t:typ):typ =
  let r = normalize_type_rec env in
  match t with
  | TName id ->
    match try_lookup_type env id with
    | (Some (typ, k), x)  ->
      match typ with | Some t -> r t | None -> TName x
    | _ ->
      err ("cannot find type '" + (err_id id) + "'")
  | TVar _ -> t
  | TInt _ -> t
  | TTuple ts -> TTuple (List.map r ts)
  | TArrow (ts, t) -> TArrow (List.map r ts, r t)
  | TApp (t, ts) -> TApp (r t, List.map r ts)
let normalize_type (env:env) (t:typ):norm_typ =
  {norm_typ = normalize_type_rec env t}

// HACK: mangle the parameter types. This will not be needed if transform is performed before typechecker.
let rec normalize_type_with_transform (env:env) (t:typ) (tr:transform_kind option):norm_typ =
  let get_type env x t =
    match try_lookup_proc env x with
    | (Some p, _) ->
      match p.trets with
      | [t] -> normalize_type env t
      | _ -> err "more than one return type"
    | _ ->
      match t with
      | TName id ->
        match try_lookup_type env id with
        | (Some (typ, k), x)  ->
          match typ with | Some t -> normalize_type env t | None -> {norm_typ = TName x}
        | _ -> err ("cannot find type '" + (err_id id) + "'")
      | _ -> normalize_type env t
  match (t, tr) with
  | (_, Some (EvalState (s, x))) ->
    let vx = Id (qprefix "va_op_" x + "_" + s) in
    get_type env vx t
  | (_, Some (ConstOp s)) ->
    let vx = Id (qprefix "va_const_" s) in
    get_type env vx t
  | (_, Some (Coerce (xo, xoDst))) ->
    let vx = Id (qprefix "va_coerce_" xo + "_to_" + xoDst) in
    get_type env vx t
  | (TName (Id x), Some EvalOp) ->
    let vx = Id (qprefix "va_eval_" x) in
    get_type env vx t
  | (TName (Id x), Some OperandTyp) ->
    let vx = Id (qprefix "va_operand_" x) in
    match try_lookup_type env vx with
    | (Some (typ, k), x)  ->
      match typ with | Some t -> normalize_type env t | None -> {norm_typ = TName x}
    | _ ->
      match try_lookup_type env (Id x) with
      | (Some (typ, k), x)  ->
        match typ with | Some t -> normalize_type env t | None -> {norm_typ = TName x}
      | _ -> err ("cannot find type '" + x + "'")
  | (TName (Id x), Some StateGet) ->
    let vx = Id (qprefix "va_get_" x) in
    get_type env vx t
  | (TName id, None) ->
    match try_lookup_type env id with
    | (Some (typ, k), x)  ->
      match typ with | Some t -> normalize_type env t | None -> {norm_typ = TName x}
    | _ -> err ("cannot find type '" + (err_id id) + "'")
  | (TApp (t, ts), _) ->
    let t = normalize_type env t in
    let ts = List.map (fun t -> (normalize_type env t).norm_typ) ts in
    {norm_typ = TApp (t.norm_typ, ts)}
  | _ -> normalize_type env t

let push_unsupported (env:env) (id:id):env =
  let env = push_scope_mod env (Unsupported id)
  {env with declsmap = Map.add id (Name id) env.declsmap}

let push_include_module (env:env) (m:string) (b:bool):env =
  push_scope_mod env (Include_module (m, b))

let push_id (env:env) (id:id) (t:typ):env =
  push_scope_mod env (Variable (id, t, None))

let push_id_with_info (env:env) (id:id) (t:typ) (info:id_info option):env =
  push_scope_mod env (Variable (id, t, info))

let push_func (env:env) (id:id) (t:decl_type):env =
  let env = push_scope_mod env (Func (id, t));
  {env with declsmap = Map.add id (Func_decl t) env.declsmap}

let push_proc (env:env) (id:id) (t:decl_type):env =
  push_scope_mod env (Proc (id, t))

let push_typ (env:env) (id:id) (ts:tformal list) (k:kind) (t:typ option):env =
  let env = push_scope_mod env (Type (id, ts, k, t))
  {env with declsmap = Map.add id (Type_info (ts, k, t)) env.declsmap}

let push_const (env:env) (id:id) (t:typ):env =
  let t = normalize_type env t in
  let env = push_scope_mod env (Const (id, t.norm_typ)) in
  {env with declsmap = Map.add id (Info (t.norm_typ, None)) env.declsmap}

let push_rets (env:env) (rets:pformal list):env =
  let f s (x, t, g, io, a) =
    let info =
      match g with
      | XOperand -> Some (OperandLocal t)
      | XInline -> Some InlineLocal
      | _ -> None in
    Variable (x, (normalize_type env t).norm_typ, info)::s in
  {env with scope_mods = List.fold f env.scope_mods rets}

let push_params_without_rets (env:env) (args:pformal list) (rets:pformal list):env =
  let arg_in_rets arg l = List.exists (fun elem -> elem = arg) l in
  let rec aux s l =
    match l with
    | [] -> s
    | a::q ->
    let (x, t, g, _, _) = a in
    let info =
      match g with
      | XOperand -> Some (OperandLocal t)
      | XInline -> Some InlineLocal
      | _ -> None
    let s = if arg_in_rets a rets then s else Variable (x, t, info)::s in
    aux s q in
  {env with scope_mods = aux env.scope_mods args}

let push_lhss (env:env) (lhss:lhs list):env =
  let push_lhs s (x,dOpt) =
    match dOpt with
    | Some (tOpt, _) ->
      let t = match tOpt with Some t -> t | None -> next_type_var () in
      Variable (x, t, None)::s
    | None -> s
  {env with scope_mods = List.fold push_lhs env.scope_mods lhss }

let push_formals (env:env) (formals:formal list):env =
  {env with scope_mods = List.fold (fun s (x, t) -> let t = match t with Some t-> t | _->next_type_var () in Variable (x, t, None)::s) env.scope_mods formals}

let compute_proc_typ (env:env) (p:proc_decl):decl_type =
  let args = List.map (fun (_, t, _, _, _) -> (normalize_type_with_transform env t (Some OperandTyp)).norm_typ) p.pargs in
  let outs =
    List.fold
      (fun l (_, t, _, io, _) ->
        match io with | Out | InOut -> l @ [(normalize_type_with_transform env t (Some OperandTyp)).norm_typ] | _ -> l)
      []
      p.pargs
      in
  let rets = List.map (fun (_, t, _, _, _) -> (normalize_type_with_transform env t (Some OperandTyp)).norm_typ) p.prets in
  {tformals = p.pargs; targs = args; trets = outs @ rets; ret_name = None; specs = p.pspecs; attrs = p.pattrs}

let compute_func_typ (env:env) (f:fun_decl):decl_type =
  let targs = List.map (fun (id, kind, _) -> TVar (id, Some kind)) f.ftargs in
  let rec replace_typ_arg t =
    match t with
    | TName id ->
      match List.tryFind (fun tv -> match tv with | TVar (x, _) -> id=x | _ -> false) targs with
      | Some tv -> tv
      | None -> t
    | TApp (t, ts) -> TApp (replace_typ_arg t, List.map replace_typ_arg ts)
    | TVar (_, _) -> err ("unexpected type variable in function type")
    | TInt (_, _) -> t
    | TTuple ts -> TTuple (List.map replace_typ_arg ts)
    | TArrow (ts, t) -> TArrow (List.map replace_typ_arg ts, replace_typ_arg t)
  let arg_typ l t =
    match t with
    | TName (Id "Prims.unit") -> l
    | _ -> l @ [(normalize_type_with_transform env (replace_typ_arg t) (Some OperandTyp)).norm_typ]
  let args =
    List.fold
      (fun l (id, t) -> let t = match t with | Some t -> t | None -> next_type_var () in arg_typ l t)
      []
      f.fargs
      in
  let rets = arg_typ [] f.fret in
  {tformals = []; targs = args; trets = rets; ret_name = f.fret_name; specs = f.fspecs; attrs = f.fattrs}

let bnd_le (x:bnd) (y:bnd):bool =
  match (x, y) with
  | (NegInf, _) -> true
  | (_, Inf) -> true
  | (Int i1, Int i2) when i1 <= i2 -> true
  | _ -> false

let bnd_add (x:bnd) (y:bnd):bnd list =
  match (x, y) with
  | (NegInf, Inf) | (Inf, NegInf) -> [] // undefined
  | (NegInf, _) | (_, NegInf) -> [NegInf]
  | (Inf, _) | (_, Inf) -> [Inf]
  | (Int x, Int y) -> [Int (x + y)]

let bnd_neg (x:bnd):bnd = match x with Int i -> Int (-i) | Inf -> NegInf | NegInf -> Inf
let bnd_abs (x:bnd):bnd = match x with Int i -> Int (abs i) | Inf | NegInf -> Inf
let bnd_sub (x:bnd) (y:bnd):bnd list = bnd_add x (bnd_neg y)

let rec bnd_mul (x:bnd) (y:bnd):bnd =
  match (x, y) with
  | (NegInf, _) -> bnd_mul Inf (bnd_neg y)
  | (Inf, Inf) -> Inf
  | (Inf, NegInf) -> NegInf
  | (Inf, Int x) when x > bigint.Zero -> Inf
  | (Inf, Int x) when x < bigint.Zero -> NegInf
  | (Inf, Int x) (*when x = bigint.Zero*) -> Int bigint.Zero
  | (_, Inf) | (_, NegInf) -> bnd_mul y x
  | (Int x, Int y) -> Int (x * y)

let bnd_div (x:bnd) (y:bnd):bnd list =
  match (x, y) with
  | (_, NegInf) -> [] // TODO
  | (_, Int y) when y <= bigint.Zero -> [] // TODO: negative y
  | ((Inf | NegInf), Inf) -> []
  | ((Inf | NegInf), Int _) -> [x]
  | (Int _, Inf) -> [Int bigint.Zero]
  | (Int x, Int y) -> [Int (x / y)]

let bnd_ge (x:bnd) (y:bnd):bool = bnd_le y x
let bnd_lt (x:bnd) (y:bnd):bool = not (bnd_ge x y)
let bnd_gt (x:bnd) (y:bnd):bool = not (bnd_le x y)
let bnd_min (x:bnd) (y:bnd):bnd = if bnd_le x y then x else y
let bnd_max (x:bnd) (y:bnd):bnd = if bnd_ge x y then x else y
let bnd_zero = Int bigint.Zero
let bnd_one = Int bigint.One

let compute_bound (l1:bnd) (h1:bnd) (l2:bnd) (h2:bnd) (op:bop):(bnd * bnd) =
  let s =
    let all_pairs f = f l1 l2 @ f h1 l2 @ f l1 h2 @ f h1 h2 in
    match op with
    | BAdd -> all_pairs bnd_add
    | BSub -> all_pairs bnd_sub
    | BMul -> all_pairs (fun x y -> [bnd_mul x y])
    | BDiv when (bnd_gt l2 bnd_zero) (* TODO || (bnd_lt h2 bnd_zero) *) -> all_pairs bnd_div
    | BMod when (bnd_gt l2 bnd_zero) || (bnd_lt h2 bnd_zero) ->
      [bnd_zero] @ bnd_sub (bnd_abs l2) bnd_one @ bnd_sub (bnd_abs h2) bnd_one
    | _ -> err (sprintf "cannot find new bound for '(%A, %A) %A (%A, %A)'" l1 h1 op l2 h2) in
  (List.fold bnd_min Inf s, List.fold bnd_max NegInf s)

let unify_int_bound (t1:typ) (t2:typ) (op:bop):typ =
  match (t1, t2) with
  | (TInt (l1, h1), TInt (l2, h2)) ->
    let (l, h) = compute_bound l1 h1 l2 h2 op in
    TInt (l, h)
  | _ -> err (sprintf "expected two integer types, found '%A' and '%A'" (string_of_typ t1) (string_of_typ t2))

let neg_int_bound (t:typ):typ =
  match t with
  | TInt (b1, b2) -> TInt (bnd_neg b2, bnd_neg b1)
  | _ -> err ("int type is expected with neg operator")

let rec typ_equal env (t1:typ) (t2:typ):bool =
  normalize_type env t1 = normalize_type env t2

// Check t1 <: t2
let is_subtype (env:env) (t1:norm_typ) (t2:norm_typ):bool =
  match (t1.norm_typ, t2.norm_typ) with
  | (TName (Id "bool"), TName (Id "prop")) -> true
  | (TInt (l1, h1), TInt (l2, h2)) -> bnd_le l2 l1 && bnd_le h1 h2
  | _ -> t1 = t2

let isArithmeticOp op = match op with | BAdd | BSub | BMul | BDiv | BMod -> true | _ -> false
let isLogicOp op = match op with | BEquiv | BImply | BExply | BAnd _ | BOr _ -> true | _ -> false
let isIcmpOp op = match op with | BLt | BGt | BLe | BGe -> true | _ -> false

let lookup_evar env x =
  match x with
  | Id "False" -> lookup_id env (Id "Prims.l_False")
  | Id "True" -> lookup_id env (Id "Prims.l_True")
  | _ -> lookup_id env x

let compute_transform_info env (formal:pformal) (e:exp) =
  // if env.ghost=true, then it is always Ghost None
  let (g, opr, io) =
    if env.ghost then (Ghost, None, In) else
    match formal with
    | (_, (TName (Id x)), XOperand, io, _) -> (NotGhost, Some x,  io)
    | (_, t, XInline, io, _) -> (Ghost, None, io)
    | (_, t, XAlias _, io, _) -> (NotGhost, None, io)  // XAlias is dropped
    | (_, t, XGhost, In, []) -> (Ghost, None, In)
    | (_, t, XGhost, _, []) -> err ("out/inout ghost parameters are not supported")
    | (x, _, _, _, _) -> err ("unexpected argument for parameter " + (err_id x)) in
  match (g, skip_loc e) with
  | (_, EVar x) ->
    let (t, info) = lookup_evar env x in
    match info with
    | Some InlineLocal ->
      match (g, opr) with
      | (NotGhost, Some xo) -> Some (ConstOp xo)
      | _ -> None
    | Some (OperandLocal (TName (Id xo))) ->
      match (g, opr) with
      | (Ghost, _) -> Some EvalOp
      | (NotGhost, Some xoDst) ->
        if xo <> xoDst then Some (Coerce (xo, xoDst)) else Some (OperandTyp)
      | _ -> None
    | Some (StateInfo s) ->
      match (g, opr) with
      | (Ghost, _) -> Some StateGet
      | (NotGhost, Some xo) -> Some (EvalState (s, xo))
      | (NotGhost, None) -> err "this expression can only be passed to a ghost parameter or operand parameter"
    | _ -> None
  | (NotGhost, EOp (Uop UConst, _)) -> match opr with | Some xo -> Some (ConstOp xo) | _ -> None
  | (NotGhost, EInt _) -> match opr with | Some xo -> Some (ConstOp xo) | _ -> None
  | (NotGhost, EApply (x, _)) ->
    let operandProc (xa:id) (io:inout):id =
      let xa = string_of_id xa in
      match io with
      | In | InOut -> Id (xa + "_in")
      | Out -> Id (xa + "_out")
    let (proc, _) = try_lookup_proc env (operandProc x io) in
    if (opr <> None && Option.isSome proc) then Some (EApplyCode) else None
  | _ -> None

let check_not_local env x =
  match lookup_name env x false with
  | (Some (Info (t, info)), _) -> err ("formal: " + (err_id x) + " is a local variable")
  | _ -> ()

let check_no_duplicates xs =
  let ls = List.map fst xs in
  let ss = List.sort ls in
  let rec f ss =
    match ss with
    | [] -> ()
    | h1::h2::_ when h1 = h2 ->
        err ("duplicate formal: " + (err_id h1))
    | _::t -> f t
    in
  f ss

let constrain_equal (src_typ:typ) (expected_typ:typ) (cl:typ_constraints) : typ_constraints =
  if src_typ = expected_typ then cl
  else TcEqual (src_typ, expected_typ) :: cl

let constrain_subtype (src_typ:typ) (expected_typ:typ) (cl:typ_constraints) : typ_constraints =
  if src_typ = expected_typ then cl
  else TcSubtype (src_typ, expected_typ) :: cl

let constrain_subtype_opt (src_typ:typ) (expected_typ:typ option) (cl:typ_constraints) : typ_constraints =
  match expected_typ with
  | None -> cl
  | Some et -> constrain_subtype src_typ et cl

(*
let rec infer_arg_typ (env:env) (args:(exp * pformal option * typ option) list):(typ list * aexp list * typ_constraints) =
  let infer_arg_typ_fold env (ts, ae, s) ((e:exp), (formal:pformal option), (et:typ option)):(typ list * aexp list * typ_constraints) =
    let (t, ae1, s1) =
      let tr =
        match formal with
        | Some f ->
          compute_transform_info env f (e:exp)
        | _ -> if env.ghost then Some EvalOp else None
      match skip_loc e with
      | EVar x when (x <> Reserved "this") ->
        let (t, info) = lookup_evar env x in
        let t = normalize_type_with_transform env t tr in
        let et = match et with | None -> t | Some t -> t in
        (t, AEVar (x, t, et), [])
      | EInt i ->
        let t = TInt (Int i, Int i) in
        let t = normalize_type_with_transform env t tr in
        let et = match et with | None -> t | Some t -> t
        (t, AEInt (i, t, et), [])
      | EOp (Uop UConst, [e]) ->
        match tr with
        | Some (ConstOp s) ->
          let tv = next_type_var () in
          let et = match et with | None -> tv | Some t -> t in
          let t = normalize_type_with_transform env tv tr in
          let (_, ae, s) = infer_exp env e (Some et) in
          let ae = AE_Op (Uop UConst, [ae], t, et) in
          (t, ae, s)
        | _ -> infer_exp env e et
      | EApply (x, es) ->
        match tr with
        | Some EApplyCode ->
          let vx = Id (qprefix ("va_opr_code_") (string_of_id x)) in
          let ecs = List.collect (fun e -> match e with EOp (Uop UGhostOnly, [e]) -> [] | _ -> [e]) es in
          let ea = EApply (vx, ecs) in
          let (t, ae, s) = infer_exp env ea et in
          let ae =
            match ae with
            | AEApply (_, es, t, et) -> AEApply (x, es, t, et)
            | _ -> internalErr ("EApply expected") in
          (t, ae, s)
        | _ -> infer_exp env e et
      | _ -> infer_exp env e et in
    let t = normalize_type env t in
    (ts @ [t], ae @ [ae1], s @ s1)
  in
  List.fold (infer_arg_typ_fold env) ([], [], []) args
*)
let rec infer_exps (env:env) (args:(exp * typ option) list):(norm_typ list * aexp list * typ_constraints) =
  let infer_exps_fold env (ts, ae, s) ((e:exp), (et:typ option)):(norm_typ list * aexp list * typ_constraints) =
    let (t, ae1, s1) = infer_exp env e et in
    (t::ts, ae1::ae, (List.rev s1) @ s)
  in
  let (ts_rev, aes_rev, s_rev) = List.fold (infer_exps_fold env) ([], [], []) args in
  (List.rev ts_rev, List.rev aes_rev, List.rev s_rev)
and infer_exp_multi (env:env) (e:exp) (expected_typ:typ option list):(typ list * aexp * typ_constraints) =
  match e with
(* TODO
  | EOp (Uop UReveal, [e]) ->
    let (t, ae, s) =
      match e with
      | EVar x ->
        lookup_proc env x |> ignore
        ([], AEVar(x, TName (Id "unit"), TName (Id "unit")), [])
      | EApply _ -> infer_exp_multi env e [None];
      | _ -> err (sprintf "unexpected UReveal %A" e)
    let ae = AE_Op (Uop UReveal, [ae], TName (Id "unit"), TName (Id "unit")) in
    ([], ae, [])
  | EApply (x, es) ->
    let (p, isExtern) = lookup_proc env x in
    if List.length p.targs <> List.length es then err (sprintf "number of args doesn't match number of parameters, expected %i, got %i" (List.length p.targs) (List.length es));
    let param_typs = p.targs in
    let ret_typs = p.trets in
    let param_arg_typs =
      if p.tformals <> [] then List.map2 (fun t1 t2 -> (Some t1, t2)) p.tformals param_typs
      else List.map (fun t -> (None, t)) param_typs in
    let env = if isExtern then {env with ghost = true} else env in
    let (arg_typs, aes, s) = infer_arg_typ env (List.map2 (fun e (tf, t) -> (e, tf, Some t)) es param_arg_typs) in
    let et = List.map2 (fun et rt -> match et with | None -> rt | Some t -> t) expected_typ ret_typs in
    let ae = AEApply (x, aes, ret_typs, et) in
    let s = List.fold2 (fun l t1 t2 -> l @ [(t1, t2)]) s param_typs arg_typs in
    (ret_typs, ae, s)
*)
  | _ -> err (sprintf "missing typechecker for exp %A" e)
and infer_exp (env:env) (e:exp) (expected_typ:typ option):(norm_typ * aexp * typ_constraints) =
  let ret (t:norm_typ) (ae:aexp_t) (s:typ_constraints) =
    let coerce =
      match expected_typ with
      | None -> None
      | Some et -> if t = normalize_type env et then None else Some (t.norm_typ, et)
      in
    (t, (ae, coerce), constrain_subtype_opt t.norm_typ expected_typ s)
    in
  let norm_ret (t:typ) (ae:aexp_t) (s:typ_constraints) =
    ret (normalize_type env t) ae s
    in
  match e with
  | ELoc (loc, e) ->
    let (t, ae, s) = infer_exp env e expected_typ in
    (t, (AE_Loc (loc, ae), None), s)
  | EVar (Reserved "this") -> norm_ret (TName (Id "state")) (AE_Exp e) []
  | EVar x ->
    let (t, _) = lookup_evar env x in
    let t = normalize_type_with_transform env t (Some EvalOp) in
    ret t (AE_Exp e) []
  | EInt i -> norm_ret (TInt (Int i, Int i)) (AE_Exp e) []
  | EReal r -> norm_ret (TName (Id "real")) (AE_Exp e) []
//    | EBitVector (n, i) -> TODO
  | EBool b -> norm_ret t_bool (AE_Exp e) []
  | EString s -> norm_ret (TName (Id "string")) (AE_Exp e) []
  | EOp (Uop (UConst | UOld) as op, [e]) ->
    let (t, ae, s) = infer_exp env e expected_typ in
    ret t (AE_Op (op, [ae])) s
  | EOp (Uop UNeg, [e]) ->
    let (t, ae, s) = infer_exp env e None in
    let t = neg_int_bound t.norm_typ in
    norm_ret t (AE_Op (Uop UNeg, [ae])) s
  | EOp (Uop (UNot _) as op, [e]) ->
    let tv = next_type_var () in
    let et = match expected_typ with | None -> tv | Some t -> t in
    let (_, ae, s) = infer_exp env e (Some et) in
    let s = constrain_subtype tv t_prop s in
    let s = constrain_subtype tv et s in
    ({norm_typ = tv}, (AE_Op (op, [ae]), Some (tv, et)), s) // Some (tv, et) used to resolve overload
(* TODO
  | EOp (Uop (UIs x), [e]) ->
    let ix = Id ("uu___is_"+ (string_of_id x)) in
    let e = EApply (ix, [e]) in
    let (t, ae, s) = infer_exp env e expected_typ in
    let ae =
      match ae with
      | AEApply (_, es, [t], [et]) -> AE_Op (Uop (UIs x), es, t, et)
      | _ -> err ("'UIs' should be converted to 'EApply' first before typechecking") in
    (t, ae, s)
  | EOp (Uop (UCustom op), l) ->
    let (p, _) = lookup_proc env (Operator op) in
    let e = EApply (attrs_get_id (Reserved "alias") p.attrs, l) in
    let (t, ae, s) = infer_exp env e expected_typ in
    let ae =
      match ae with
      | AEApply (x, es, [t], [et]) -> AE_Op (Uop (UCustom op), es, t, et)
      | _ -> err ("'UCustom' should be converted to 'EApply' first before typechecking") in
    (t, ae, s)
  | EOp (Uop UToOperand, _) ->
    err (sprintf "missing typing rule for Uop UToOperand")
  | EOp (Uop op, _) ->
    err (sprintf  "unsupported Uop '%A' in typechecker" op)
*)
  | EOp (Bop op, [e1; e2]) when isArithmeticOp op ->
    // op in {+, -, *, /, %}
    let (t1, ae1, s1) = infer_exp env e1 None in
    let (t2, ae2, s2) = infer_exp env e2 None in
    let t = unify_int_bound t1.norm_typ t2.norm_typ op in
    norm_ret t (AE_Op (Bop op, [ae1; ae2])) (s1 @ s2)
  | EOp (Bop (BAnd _ | BOr _) as op, [e1; e2]) ->
    let tv = next_type_var () in
    let et = match expected_typ with | None -> tv | Some t -> t in
    let (_, ae1, s1) = infer_exp env e1 (Some et) in
    let (_, ae2, s2) = infer_exp env e2 (Some et) in
    let s = s1 @ s2 in
    let s = constrain_subtype tv t_prop s in
    let s = constrain_subtype tv et s in
    ({norm_typ = tv}, (AE_Op (op, [ae1; ae2]), Some (tv, et)), s) // Some (tv, et) used to resolve overload
  | EOp (Bop (BEquiv | BImply | BExply) as op, [e1; e2]) ->
    let (_, ae1, s1) = infer_exp env e1 (Some t_prop) in
    let (_, ae2, s2) = infer_exp env e2 (Some t_prop) in
    norm_ret t_prop (AE_Op (op, [ae1; ae2])) (s1 @ s2)
  | EOp (Bop op, [e1; e2]) when isIcmpOp op ->
    // op in {<, > , <=, >=} and it can be chained
    match (op, skip_loc e1) with
    | (op, EOp (Bop op1, [e11; e12])) when isIcmpOp op1 ->
        // Convert (a <= b) < c into (a <= b) && (b < c)
        let e2 = EOp (Bop op, [e12; e2]) in
        let e = EOp (Bop (BAnd OpBool), [e1; e2]) in
        infer_exp env e expected_typ
    | _ ->
      let (_, ae1, s1) = infer_exp env e1 (Some t_int) in
      let (_, ae2, s2) = infer_exp env e2 (Some t_int) in
      norm_ret t_bool (AE_Op (Bop op, [ae1; ae2])) (s1 @ s2)
  | EOp (Bop (BEq opt | BNe opt) as op, [e1; e2]) ->
    let (t1, ae1, s1) = infer_exp env e1 None in
    let (t2, ae2, s2) = infer_exp env e2 None in
    let s = s1 @ s2 in
    let s = constrain_equal t1.norm_typ t2.norm_typ s in
    let t = match opt with OpBool -> t_bool | OpProp -> t_prop in
    norm_ret t (AE_Op (op, [ae1; ae2])) s
(*
  | EOp (Bop BIn, [e1; e2]) ->
    err ("BIn not supported in TypeChecker")
  | EOp (Bop BOldAt, [e1; e2]) ->
    let tv = next_type_var () in
    let et = match expected_typ with | None -> tv | Some t -> t in
    let (t1, ae1, s1) = infer_exp env e1 None in
    let (t2, ae2, s2) = infer_exp env e2 None in
    let ae = AE_Op (Bop BOldAt, [ae1;ae2], tv, et) in
    (tv, ae, s1 @ s2 @ [(t1, TName(Id "state"));(t2, tv)])
  | EOp (Bop (BCustom op), l) ->
    let (p, _) = lookup_proc env (Operator op) in
    let e = EApply (attrs_get_id (Reserved "alias") p.attrs, l) in
    let (t, ae, s) = infer_exp env e expected_typ in
    let ae =
      match ae with
      | AEApply (x, es, [t], [et]) -> AE_Op (Bop (BCustom op), es, t, et)
      | _ -> err ("'BCustom' should be converted to 'EApply' first before typechecking") in
    (t, ae, s)
  | EOp (Subscript, [e1; e2]) ->
    let e = EApply ((Id "subscript"), [e1; e2]) in
    let (t, ae, s) = infer_exp env e expected_typ in
    let ae =
      match ae with
      | AEApply (x, es, [t], [et]) -> AE_Op (Subscript, es, t, et)
      | _ -> err ("'Subscript' should be converted to 'EApply' first before typechecking") in
    (t, ae, s)
  | EOp (Update, [e1; e2; e3]) ->
    let e = EApply ((Id "update"), [e1; e2; e3]) in
    let (t, ae, s) = infer_exp env e expected_typ in
    let ae =
      match ae with
      | AEApply (x, es, [t], [et]) -> AE_Op (Update, es, t, et)
      | _ -> err ("'Update' should be converted to 'EApply' first before typecheckings") in
    (t, ae, s)
*)
  | EOp (Cond, [e1; e2; e3]) ->
    let tv = next_type_var () in
    let et = match expected_typ with | None -> tv | Some t -> t in
    let (t1, ae1, s1) = infer_exp env e1 (Some t_bool) in
    let (t2, ae2, s2) = infer_exp env e2 (Some et) in
    let (t3, ae3, s3) = infer_exp env e3 (Some et) in
    let s = s1 @ s2 @ s3 in
    let s = constrain_subtype t2.norm_typ tv s in
    let s = constrain_subtype t3.norm_typ tv s in
    norm_ret tv (AE_Op (Cond, [ae1; ae2; ae3])) s
(*TODO
  | EOp (FieldOp x, [e]) ->
    let (t1, _, _) = infer_exp env e None in
    let (t, ae, s) =
      match (t1,x) with
      | (TApp(TName x,_), (Id f)) ->
        let (mn, t) = name_of_id x in
        let s = if mn = "" then "" else mn + "." in
        let s = s + "__proj__" + "Mk" + string_of_id t + "__item__" + f in
        let e = EApply (Id s, [e]) in
        infer_exp env e expected_typ
      | _ -> err (sprintf "unknown field type %A for field %s" t1 (err_id x)) in
    let ae =
      match ae with
      | AEApply (_, es, [t], [et]) -> AE_Op (FieldOp x, es, t, et)
      | _ -> err ("'FieldOp' should be converted to 'EApply' before typechecking") in
    (t, ae, s)
  | EOp (FieldUpdate x, [e1; e2]) ->
    let (t1, _, _) = infer_exp env e1 None in
    let (t2, ae2, s2) = infer_exp env e2 None in
    let (t, ae, s) =
      match (t1,x) with
      | (TName (Id t), (Id f)) ->
        let s = "__proj" + t + "__item__" + f in
        let e = EApply (Id s, [e1]) in
        infer_exp env e expected_typ
      | _ -> err (sprintf "unknown field type %A for field %s" t1 (err_id x)) in
    let ae =
      match ae with
      | AEApply (_, es, [t], [et]) -> AE_Op (FieldUpdate x, es @ [ae2], t, et)
      | _ -> err ("'FieldUpdate' should be converted to 'EApply' before typechecking") in
    (t, ae, s @ s2 @ [(t2, t)])
  | EOp (op, es) ->
    err (sprintf "unsupported Eop %A in typechecking" op)
  | EApply (Id "list", es) ->
    let tv = next_type_var () in
    let arg_typ = next_type_var () in
    let (arg_typs, aes, s) = infer_arg_typ env (List.map (fun e -> (e, None, Some arg_typ)) es) in
    let et = TApp (TName (Id "list"), [arg_typ]) in
    let ae = AEApply (Id "list", aes, [tv], [et]) in
    let s = List.fold (fun l t -> l @ [(t, arg_typ)]) s arg_typs in
    (tv, ae, [(tv, et)] @ s)
*)
  | EApply (Id "tuple", es) ->
    let ts =
      match expected_typ with
      | Some (TTuple ts) -> ts
      | _ -> List.map (fun _ -> next_type_var ()) es
      in
    let t = TTuple ts in
    let (_, aes, s) = infer_exps env (List.map2 (fun e t -> (e, Some t)) es ts) in
    norm_ret t (AE_Apply (Id "tuple", aes)) s
  | EApplyTyped (x, ts, es) ->
    err ("EApplyTyped not implemented in typechecking")
  | EBind (BindLet, [ex], [(x, t)], [], e) ->
    // let x:t := ex in e
    check_not_local env x;
    let (t1, ae1, s1) = infer_exp env ex t in
    let xt = match t with | Some t -> t | _ -> t1.norm_typ in
    let env = push_id env x xt in
    let (t2, ae2, s2) = infer_exp env e expected_typ in
    ret t2 (AE_Bind (BindLet, [ae1], [(x, t)], [], ae2)) (constrain_subtype t1.norm_typ xt (s1 @ s2))
  | EBind (((Forall | Exists) as b), [], fs, ts, e) ->
    // fs list of formals, that are distinct and are not local variables
    // ts: triggers
    // e: prop
    let env = List.fold (fun env (x, t) -> let t = match t with Some t -> t | None -> next_type_var () in push_id env x t) env fs in
    let (t, ae, s) = infer_exp env e expected_typ in
    ret t (AE_Bind (b, [], fs, ts, ae)) (constrain_subtype t.norm_typ t_prop s)
  | EBind (Lambda, [], xs, ts, e) ->
    let xs = List.map (fun (x, t) -> match t with Some t -> (x, t) | None -> (x, next_type_var ())) xs in
    let env = List.fold (fun env (x, t) -> push_id env x t) env xs in
    let (t, ae, s) = infer_exp env e None in
    let ae = AE_Bind (Lambda, [], List.map (fun (x, t) -> (x, Some t)) xs, ts, ae) in
    norm_ret (TArrow (List.map snd xs, t.norm_typ)) ae s
  | ECast (e, tc) ->
    let (t, ae, s) = infer_exp env e None in
    let ae = AE_Cast (ae, tc) in
    let tc_norm = normalize_type env tc in
    // TODO: move this check to after inference:
    if (is_subtype env t tc_norm || is_subtype env tc_norm t) then norm_ret tc ae s
    else err (sprintf "cannot cast between types %A and %A that do not have subtype relationship" t tc)
  | _ -> infer_exp_one env e expected_typ
and infer_exp_one (env:env) (e:exp) (et:typ option):(norm_typ * aexp * typ_constraints) =
  match infer_exp_multi env e [et] with
  | ([t], ae, s) -> (normalize_type env t, ae, s)
  | (ts, _, _) -> err (sprintf "%A can have only one inferred type, got %i" e (List.length ts))
and infer_exp_many (env:env) (e:exp) (et:(typ option) list):(norm_typ list * aexp * typ_constraints) =
  match et with
  | [et] -> let (t, ae, s) = infer_exp env e et in ([t], ae, s)
  | _ ->
    let (ts, ae, s) = infer_exp_multi env e et in
    (List.map (normalize_type env) ts, ae, s)

let kind_equal k1 k2 =
  match (k1, k2) with
  | (KType i1, KType i2) -> i1=i2

let rec resolve_type (env:env) (t:typ):kind =
  match t with
  | TName id -> let (t, k) = lookup_type env id in k
  | TVar (_, Some k) -> k
  | TInt (_, _) -> KType bigint.Zero
  | TTuple ts -> KType bigint.Zero // TODO: check ts
  | TArrow (ts, t) -> KType bigint.Zero // TODO: check ts, t
  | TApp (t, ts) -> resolve_type env t
  | _ -> err (sprintf "cannot find the kind of the type '%A'" t)
and resolve_types env ts = List.map (resolve_type env) ts;

let match_kind env (t:typ) (k:kind option) =
  match k with
  | Some k ->
    match t with
    | TVar (_, None) -> true
    | _ ->
      kind_equal (resolve_type env t) k
  | None -> true

// substitute all occurrences of x in t with s
let rec subst env (x:id) (s:typ) (t:typ):(typ * bool) =
  match t with
  | TVar (y, k) ->
    if x = y then
      if match_kind env s k then
       let b = if typ_equal env s t then false else true in
       (s, b)
      else err (sprintf "kind of type '%A' and type '%A' does not match" s t)
    else (t,  false)
  | TApp (t, ts) ->
    let (t1, b1) = subst env x s t in
    let (ts, b2) = subst_typs env x s ts in
    (TApp (t1, ts), b1 || b2)
  | TArrow (ts, t) ->
    let (ts, b1) = subst_typs env x s ts in
    let (t2, b2) = subst env x s t in
    (TArrow (ts, t2), b1 || b2)
  | TTuple ts -> let (ts, b) = subst_typs env x s ts in ((TTuple ts), b)
  | _ -> (t, false)
and subst_typs env (x:id) (s:typ) (ts:typ list):(typ list * bool) =
  let (ts_rev, b) =
    List.fold (fun (rs, b) t -> let (t, b1) = subst env x s t in (t::rs, b1 || b)) ([], false) ts
    in
  (List.rev ts_rev, b)

let substitute env (m:substitutions) (t:typ):typ =
  let s = Map.toList m in
  let changed = true in
  let rec aux t b =
    if b = true then
      let (t, b) = List.foldBack (fun (x, s) (t, b) -> let (t, b1) = subst env x s t in (t, b||b1)) s (t, false) in
      aux t b
    else t in
  aux t true

let rec occurs (x:id) (t:typ):bool =
  let rec aux (acc:bool) l =
    match l with
    | hd :: tl ->
      if acc = false then
        let acc = occurs x hd in
        aux acc tl
      else acc
    | _ -> acc in
  match t with
  | TVar (y, _) -> x = y
  | TApp (u, l) ->   occurs x u || aux false l
  | TArrow (l, u) -> aux false l || occurs x u
  | _ -> false

let bind (m:substitutions) (x:id) (t:typ):substitutions =
  match t with
  | TVar (y, k) -> if (x = y) then m else Map.add x t m
  | _ -> if occurs x t then err ("circular type constraint" + err_id x + " " + string_of_typ t) else Map.add x t m

let bind_typ (m:substitutions) (s:typ) (t:typ):substitutions =
  match s with
  | TVar (x, _) -> bind m x t
  | _ -> m

let rec unify_one (env:env) (exact:bool) (m:substitutions) (s:typ) (t:typ):substitutions =
  if s = t then m else
  let typ_err () =
    if exact then err ("type '" + string_of_typ s + "' is not equal to type '" + string_of_typ t + "'")
    else err ("cannot coerce type '" + string_of_typ s + "' to type '" + string_of_typ t + "'")
    in
  let t1 = normalize_type env (substitute env m s) in
  let t2 = normalize_type env (substitute env m t) in
  match (t1.norm_typ, t2.norm_typ) with
  // TODO: TVar cases for exact = false
  | (TVar (x, _), _) -> bind m x t2.norm_typ
  | (_, TVar (x, _)) -> bind m x t1.norm_typ
  | (TInt _, TInt _) when not exact && is_subtype env t1 t2 -> m
  | (TName (Id "bool"), TName (Id "prop")) when not exact -> m
  | (TTuple ts, TTuple us) when List.length ts = List.length us ->
    let tc = List.fold2 (fun l t1 t2 -> constrain_equal t1 t2 l) [] ts us in
    unify env m tc
  | (TArrow (xs, y), TArrow (us, v)) when List.length xs = List.length us ->
    let tc = List.fold2 (fun l t1 t2 -> constrain_equal t1 t2 l) [] xs us in
    unify env m (constrain_equal y v tc)
  | (TApp (x, ys), TApp (u, vs)) when List.length ys = List.length vs ->
    if x = u then
      let tc = List.fold2 (fun (l:typ_constraints) t1 t2 -> constrain_equal t1 t2 l) [] ys vs in
      unify env m tc
    else
      let t1 = normalize_type env x in
      let t2 = normalize_type env u in
      if t1 = t2 then m else typ_err ()
  | _ when t1 = t2 -> m
  | _ -> typ_err ()

and unify env (m:substitutions) (tc:typ_constraints):substitutions =
  match tc with
  | [] -> m
  | (TcEqual (x, y)) :: t ->
    let m = unify_one env true m x y in
    unify env m t
  | (TcSubtype (x, y)) :: t ->
    let m = unify_one env false m x y in
    unify env m t

let insert_cast (e:exp) (t:typ) (et:typ):exp =
  // cast from type 't' to 'et' and it is checked by SMT solver
  ECast (e, et)

let rec subst_exp env (s:substitutions) ((e, coerce):aexp):exp =
  let coerce = Option.map (fun (t, et) -> (substitute env s t, substitute env s et)) coerce in
  let e =
    match e with
    | AE_Loc (loc, ae) -> ELoc (loc, subst_exp env s ae)
    | AE_Exp e -> e
    | AE_Op (op, aes) ->
      let es = List.map (subst_exp env s) aes in
      let bool_prop f =
        match coerce with
        | Some (TName (Id "bool"), _) -> EOp (f OpBool, es)
        | Some (TName (Id "prop"), _) -> EOp (f OpProp, es)
        | _ -> internalErr "subst_exp UNot"
      match op with
(* TODO
      let (op, t, et) =
        match op with
        | Bop p ->
          if isArithmeticOp p then
            match (t, et) with
            | (TInt (_, _), _) -> (op, t, et)
            | (TVar (_, _), TVar(_,_)) ->
              // still unknown due to unsupported import types, resolve it to int type.
              (op, TInt(NegInf, Inf), TInt(NegInf, Inf))
            | _ -> err (sprintf "%A expected int type, got %A" op t)
          else (op, t, et)
*)
        | Bop (BAnd _) -> bool_prop (fun opt -> Bop (BAnd opt))
        | Bop (BOr _) -> bool_prop (fun opt -> Bop (BOr opt))
        | Uop (UNot _) -> bool_prop (fun opt -> Uop (UNot opt))
        | _ -> EOp (op, es)
//      let e = EOp (op, es) in
//      if (typ_equal env t et) then e else insert_cast e t et
(*
    | AEApply (Id "list", aes, ts, ets) ->
      let es = List.map (fun ae -> subst_exp env s ae) aes  in
      let t = (List.map (fun t -> substitute env s t) ts).Head in
      let et = (List.map (fun t -> substitute env s t) ets).Head in
      let e = EApply (Id "list", es) in
      match (t, et) with
      | (TApp (TName (Id "list"), [x]), TApp (TName (Id "list"), [y])) ->
        if typ_equal env x y then
          if (kind_equal (resolve_type env x) (KType bigint.Zero)) then e
          else err ("Only 'Type0' is allowed in list")
        else
          err (sprintf "inferred list type %s does not match expected list type %s" (string_of_typ t) (string_of_typ et))
      | _ -> err (sprintf "list type %A expected but got %A" (string_of_typ et) (string_of_typ t))
    | AEApply (Id "tuple", aes, ts, ets) ->
      let es = List.map (fun ae -> subst_exp env s ae) aes  in
      let t = (List.map (fun t -> substitute env s t) ts).Head in
      let et = (List.map (fun t -> substitute env s t) ets).Head in
      let e = EApply (Id "tuple", es) in
      match (t, et) with
      | (TTuple xs, TTuple ys) ->
        List.iter2 (fun t1 t2 -> if (not (typ_equal env t1 t2)) then err (sprintf "inferred tuple type %s does not match expected tuple type %s" (string_of_typ et) (string_of_typ t))) xs ys;
        List.iter (fun t -> if (not (kind_equal (resolve_type env t) (KType bigint.Zero))) then err "Only 'Type0' is allowed in tuple") xs;
        e
      | _ -> err (sprintf "tuple type %s expected but got %s" (string_of_typ et) (string_of_typ t))734
    | AEApply (x, aes, ts, ets) ->
      let es = List.map (fun ae -> subst_exp env s ae) aes  in
      let t = List.map (fun t -> substitute env s t) ts in
      let et = List.map (fun t -> substitute env s t) ets in
      let e = EApply (x, es) in
      let equal = List.fold2 (fun b t1 t2 -> b&&typ_equal env t1 t2) true t et
      if equal then e else
        if(List.length t <> 1) then err ("cast for more than one return types not implemented");
        else insert_cast e t.Head et.Head
*)
    | AE_Apply (x, aes) ->
      let es = List.map (subst_exp env s) aes in
      EApply (x, es)
    | AE_Bind (bOp, aes, xs, ts, ae) ->
      let es = List.map (subst_exp env s) aes in
      let e = subst_exp env s ae in
      EBind(bOp, es, xs, ts, e)
    | AE_Cast (ae, t) ->
      ECast ((subst_exp env s ae), t)
  in
  match coerce with
  | None -> e
  | Some (t, et) -> if typ_equal env t et then e else insert_cast e t et

let tc_exp (env:env) (e:exp) (et:typ option):(typ * exp) =
  try
    let (t, ae, cl) = infer_exp env e et in
    let s = unify env Map.empty cl in
    let t = substitute env s t.norm_typ in
    let es = subst_exp env s ae in
//    printfn "e = %A  es = %A" (Emit_vale_text.string_of_exp e) (Emit_vale_text.string_of_exp es);
//    printfn "e = %A\n  ae = %A\n  t = %A\n  es = %A" e ae t es;
    (t, es)
  with
    | UnsupportedErr s -> printfn "%s" s; (TTuple [], e)
    | err -> (match locs_of_exp e with [] -> raise err | loc::_ -> raise (LocErr (loc, err)))

let tc_exp_many (env:env) (e:exp) (et:typ option list):(typ list * exp) =
  try
    let (ts, ae, cl) = infer_exp_many env e et in
    let s = unify env Map.empty cl in
    let ts = List.map (fun t -> substitute env s t.norm_typ) ts in
    let es = subst_exp env s ae in
    (ts, es)
  with
    | UnsupportedErr s -> printfn "%s" s; ([], e)
    | err -> (match locs_of_exp e with [] -> raise err | loc::_ -> raise (LocErr (loc, err)))

let rec update_env_stmt (env:env) (s:stmt):env =
  match s with
  | SLoc (loc, s) -> update_env_stmt env s
  | SLabel _ | SGoto _ | SReturn | SAssume _ | SAssert _ | SCalc _ -> env
  | SVar (x, t, m, g, a, eOpt) ->
    (
      let t = match t with Some t -> t | None -> next_type_var () in
      push_id env x t
    )
  | SAlias (x, y) ->
    let (t, _) = lookup_id env y in
    push_id env x t
  | SAssign (xs, e) ->
    push_lhss env xs
  | SLetUpdates _ | SBlock _ | SQuickBlock _ | SIfElse _ | SWhile _ -> env
  | SForall (xs, ts, ex, e, b) ->
    List.fold (fun env (x, t)-> let t = match t with Some t -> t | None -> next_type_var () in push_id env x t) env xs
  | SExists (xs, ts, e) ->
    List.fold (fun env (x, t)-> let t = match t with Some t -> t | None -> next_type_var () in push_id env x t) env xs


let resolve_id env id:unit =
  match id with
  | Reserved _ -> ()
  | _ ->
    match lookup_name env id true with
    | (None, _) -> err ("Identifier not found " + (err_id id))
    | (Some r, _) -> ()

let rec tc_stmt (env:env) (s:stmt):stmt =
  // TODO: need typing rules for statements
  match s with
  | SLoc (loc, s) -> SLoc (loc, tc_stmt env s)
  | SLabel x -> resolve_id env x; s
  | SGoto x -> resolve_id env x; s
  | SReturn -> s
  | SAssume e -> let (t, e) = tc_exp env e None in SAssume e
  | SAssert (attrs, e) -> let (t, e) = tc_exp env e None in SAssert (attrs, e)
  | SCalc (oop, contents) -> SCalc (oop, tc_calc_contents env contents)
  | SVar (x, t, m, g, a, eOpt) ->
    let kind = match t with | Some t -> Some (resolve_type env t) | None -> None
    let eOpt = match eOpt with | Some e -> let (t, e) = tc_exp env e t in Some e | _ -> None in
    SVar (x, t, m, g, a, eOpt)
  | SAlias (x, y) -> resolve_id env y; s
  | SAssign (xs, e) ->
    let et =
      match xs with
      | [(x, Some (Some t, _))] -> Some t
      | [(x, _)] -> let r = try_lookup_id env x in match r with | Some (t, _) -> Some t | _ -> None
      | _ -> None in
    let (t, e) = tc_exp env e et in SAssign (xs, e)
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SBlock b -> let (env, b) = tc_stmts env b in SBlock b
  | SQuickBlock (x, b) -> let (env, b) = tc_stmts env b in SQuickBlock (x, b)
  | SIfElse (g, e, b1, b2) ->
    let et = t_bool in
    let (t, e) = tc_exp env e (Some et) in
    let (env, b1) = tc_stmts env b1 in
    let (env, b2) = tc_stmts env b2 in
    SIfElse(g, e, b1, b2)
  | SWhile (e, invs, ed, b) ->
    let (t, e) = tc_exp env e None in
    let invs = List_mapSnd (fun e -> let (t,e) = tc_exp env e None in e) invs in
    let ed = mapSnd (List.map (fun e -> let (t,e) = tc_exp env e None in e)) ed in
    let (env, b) = tc_stmts env b in
    SWhile (e, invs, ed, b)
  | SForall (xs, ts, ex, e, b) ->
    let env1 = update_env_stmt env s in
    let (t, ex) = tc_exp env1 ex None in
    let (t, e) = tc_exp env1 e None in
    let (env, b) = tc_stmts env1 b in
    SForall (xs, ts, ex, e, b)
  | SExists (xs, ts, e) ->
    let env1 = update_env_stmt env s in
    let (t, e) = tc_exp env1 e None in
    SExists (xs, ts, e)
and tc_stmts (env:env) (ss:stmt list):(env * stmt list) =
  let (env, ss_rev) =
    List.fold
      (fun (env, l) s ->
        let (ts:stmt) = tc_stmt env s in (update_env_stmt env s, ts::l))
      (env, [])
      ss
    in
  (env, List.rev ss_rev)
and tc_calc_content (env:env) (cc:calcContents):calcContents =
  let {calc_exp = e; calc_op = oop; calc_hints = hints} = cc in
  let (t, e) = tc_exp env e None in
  let hints = List.map (fun h -> let (env, ss) = tc_stmts env h in ss) hints in
  {calc_exp = e; calc_op = oop; calc_hints = hints}
and tc_calc_contents (env:env) (contents:calcContents list):calcContents list = List.map (fun c -> tc_calc_content env c) contents

let tc_spec (env:env) (loc:loc, s:spec):(env * (loc * spec) list) =
  match s with
  | Requires (r, e) -> let (t, e) = tc_exp env e None in (env, [(loc, Requires (r, e))])
  | Ensures (r, e) -> let (t, e) = tc_exp env e None in (env, [(loc, Ensures (r, e))])
  | Modifies (m, e) -> let (t, e) = tc_exp env e None in (env, [(loc, Modifies (m, e))])
  | SpecRaw (RawSpec (r, es)) ->
    let rec tc_spec_exp (env:env) (es:(loc * spec_exp) list):(env * (loc * spec_exp) list) =
      match es with
      | [] -> (env, [])
      | (loc, SpecExp e)::es ->
        let (t, e) = tc_exp env e None in
        let (env, es) = tc_spec_exp env es in
        (env, (loc, SpecExp e) :: es)
      | (loc, SpecLet (x, t, e))::es ->
        let typ = match t with Some t -> t | None -> next_type_var () in
        let env = push_id env x typ in
        let (tc, e) = tc_exp env e t in
        let (env, es) = tc_spec_exp env es in
        (env, (loc, SpecLet (x, t, e)) :: es)
    let (env, es) = tc_spec_exp env es in
    (env, [(loc, SpecRaw (RawSpec (r, es)))])
  | SpecRaw (Lets ls) ->
    let tc_spec_let (env:env) (loc:loc, l:lets):(env * (loc * lets)) =
      match l with
      | LetsVar (x, t, e) ->
        let typ = match t with Some t -> t | None -> next_type_var () in
        let env = push_id env x typ in
        let (tc, e) = tc_exp env e t in (env, (loc,  LetsVar (x, t, e)))
      | LetsAlias (x, y) ->
        let (t, info) = lookup_id env y in
        let env = push_id_with_info env x t info in
        (env, (loc, LetsAlias (x, y))) in
    let (env, ls) = List.fold (fun (env, lets) l -> let (env, l) = tc_spec_let env l in (env, lets @ [l])) (env,[]) ls in
    (env, [(loc, SpecRaw (Lets ls))])

let tc_specs (env:env) (specs:(loc * spec) list):(env * (loc * spec) list) =
  let (env, specs) = List_mapFoldFlip tc_spec env specs in
  (env, List.concat specs)

let tc_proc (env:env) (p:proc_decl):(env * proc_decl) =
  try
    let isRecursive = attrs_get_bool (Id "recursive") false p.pattrs in
    let ptyp = compute_proc_typ env p in
    let env = if isRecursive then push_proc env p.pname ptyp else env in
    let globals = ref env.scope_mods in
    let env = push_params_without_rets env p.pargs p.prets in
    let env = push_rets env p.prets in
    let env = {env with ghost = true}
    let (env, pspecs) = tc_specs env p.pspecs in
    let env = {env with ghost = false}
    let (env, body) =
      match p.pbody with
      | None -> (env, None)
      | Some ss -> let (env, ss) = tc_stmts env ss in (env, Some ss)
    let pNew = {p with pbody = body; pspecs = pspecs} in
    let env = {env with scope_mods = !globals } in
    let env = if isRecursive then env else push_proc env p.pname ptyp in
    (env, pNew)
  with
    | UnsupportedErr s ->
      printfn "%s" s;
      let env = push_unsupported env p.pname in
      (env, p)

let tc_decl (env:env) (decl:((loc * decl) * bool)):(env * ((loc * decl) * bool) list) =
  let ((l, d), b) = decl in
  try
    match d with
    | DType (x, ts, k, t) ->
      let env = push_typ env x ts k t
      (env, [decl])
    | DVar (x, t, XAlias (AliasThread, e), _) ->
      // TODO: type check t and e
      let env = push_id env x t in
      (env, [decl])
    | DVar (x, tt, XState e, _) ->
      (
        match skip_loc e with
        | EApply (Id id, es) ->
          let t = normalize_type_with_transform env tt (Some StateGet) in
          let env = push_id_with_info env x t.norm_typ (Some (StateInfo id))  in
          (env, [decl])
        | _ -> err ("declaration of state member " + (err_id x) + " must provide an expression of the form f(...args...)")
      )
    | DConst (x, t) ->
      let env = push_const env x t in
      (env, [decl])
    | DFun ({fbody = None} as f) ->
      let isTypeChecked = (attrs_get_bool (Id "typecheck") false f.fattrs) && not (attrs_get_bool (Id "notypecheck") false f.fattrs) in
      let env =
        if isTypeChecked then
          let ftyp = compute_func_typ env f in
          push_func env f.fname ftyp
        else
          push_unsupported env f.fname in
      (env, [decl])
    | DProc p ->
      let isTypeChecked = (Option.isSome p.pbody) && (attrs_get_bool (Id "typecheck") false p.pattrs) && not (attrs_get_bool (Id "notypecheck") false p.pattrs) in
      let isTestShouldFail = attrs_get_bool (Id "testShouldFail") false p.pattrs in
      let (env, ps) =
        if isTypeChecked then
          if isTestShouldFail then
            let success = try let _ = tc_proc env p in true with _ -> false in
            if success then err "{:testShouldFail} procedure unexpectedly succeeded"
            else (env, [])
          else
            let (env, p) = tc_proc env p in
            (env, [p])
        else
          let env = push_unsupported env p.pname in (env, [p])
        in
      (env, List.map (fun p -> ((l, DProc p), b)) ps)
    | DUnsupported x ->
      let env = push_unsupported env x in
      (env, [decl])
    | DPragma (ModuleName s) ->
      let env = push_include_module env s true in
      (env, [decl])
    | _ -> (env, [decl])
  with
    | UnsupportedErr s -> printfn "%s" s; (env, [decl])
    | err -> raise (LocErr (l, err))

let tc_include env (inc:string * bool * (((loc * decl) * bool) list)):env =
  let (s, b, ds) = inc in
  let env = push_include_module env s b in
  let globals = ref env.scope_mods in
  let env =
    List.fold (fun env d ->
      let (env, ds) = tc_decl env d in env)
      env
      ds
    in
  let env = {env with scope_mods = !globals} in
  env

let tc_decls (include_modules:(string * bool * (((loc * decl) * bool) list)) list) (ds:((loc * decl) * bool) list):((loc * decl) * bool) list =
  // Prims is included and prop is defined by default
  let env = push_include_module empty_env "Prims" true in
  let env = {env with declsmap = Map.add (Id "prop") (Type_info ([], (KType bigint.One), None)) env.declsmap} in
  let env = List.fold (fun env inc -> tc_include env inc) env include_modules in
  let (env, dss_rev) =
    List.fold (fun (env:env, l:((loc * decl) * bool) list) d ->
      let (env, ds) = tc_decl env d in (env, (List.rev ds) @ l))
      (env, [])
      ds
    in
  List.rev dss_rev
