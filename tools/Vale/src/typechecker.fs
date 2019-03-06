module TypeChecker

open Ast
open Ast_util
open Parse
open Microsoft.FSharp.Math
open System.Collections.Generic
open System.IO
open System
open Microsoft.FSharp.Text.Lexing

let fstar = ref false;
let do_typecheck = ref false;

let string_of_kind = Emit_vale_text.string_of_kind
let string_of_typ = Emit_vale_text.string_of_typ

type typ_constraint =
| TcEqual of typ * typ // t1 = t2
| TcSubtype of typ * typ // t1 <: t2
//type typ_constraints = typ_constraint list
type substitutions = Map<id, typ>

// fun_decl instantiated with type arguments
type fun_instance = {
  f_args:typ list;
  f_targs:typ list;
  f_ret:typ;
//  f_ret_name:id option;
//  f_specs:(loc * spec) list;
//  f_attrs:attrs;
}

type proc_instance = {
  p_args:pformal list;
  p_targs: typ list
  p_rets:pformal list;
//  p_specs:(loc * spec) list;
//  p_attrs:attrs;
}

type id_info =
| StateInfo of id * typ
| OperandLocal of inout * typ
| InlineLocal
| MutableGhostLocal
| ConstGlobal

type name_info =
| Info of typ * id_info option
| Func_decl of fun_decl
| Proc_decl of proc_decl
| Type_info of tformal list option * kind * typ option
| OperandType_info of pformal list option * typ * typ option * operand_typ list
| UnsupportedName of id * loc * string option
//| Include_module of string * bool
| Module_abbrev of string * string

type include_module = string * string option option

//type scope_mod =
//| Variable of id * typ * id_info option
//| Func of id * fun_decl_type
//| Proc of id * decl_type
//| Type of id * tformal list * kind * typ option
//| Const of id * typ
//| Unsupported of id
//| No_scope

type transform_kind =
| EvalOp
| OperandTyp
| StateGet
| EvalState of string * string
| Coerce of string * string
| ConstOp of string
| EApplyCode

// Declaring 'type{:primitive} x:k' for where x is one of:
//   in F*: state, string, list
//   in Dafny: state, string, seq, set
// tells the Vale type checker that this type should be used for the following
// built-in type checking rules:
type primitive_type =
| PT_State // type of 'this'
| PT_String // type of string literals
| PT_List // type of list literals (F*)
| PT_Seq // type of seq literals (Dafny)
| PT_Set // type of set literals (Dafny)
// Note that x also goes in the ordinary type environment and can be used as an ordinary type,
// subject to standard name resolution rules.

type env = {
  decls_map:Map<id, name_info>; // map id to the decl info
  primitives_map:Map<primitive_type, id>;
  include_modules:list<include_module>;
  inline_only:bool;
//    scope_mods:list<scope_mod>; // a STACK of scope modifiers
//    ghost:bool; // HACK: used for transform parameter types. Won't need it if transform is done before typechecker.
}

let empty_env:env = {
  decls_map = Map.empty;
  primitives_map = Map.empty;
  include_modules = [];
  inline_only = false;
}

// type annotated expression
// annotated with the inferred type and expected type
// If these two types are not equal, insert a cast
type aexp_t =
| AE_Loc of loc * aexp
| AE_Exp of exp
| AE_Op of op * aexp list
| AE_ApplyX of id * typ list * aexp list
| AE_ApplyE of aexp * aexp list
| AE_Bind of bindOp * aexp list * formal list * triggers * aexp
| AE_Cast of aexp * typ
and aexp = aexp_t * typ * (typ * typ) option

let lookup_name (env:env) (x:id) (include_import:bool):(name_info option * id) =
  match (x, Map.tryFind x env.decls_map) with
  | (_, Some info) -> (Some info, x)
  | (Id x, None) ->
    (
      let rec f includes =
        match includes with
        | [] -> (None, Id x)
        | (s, None)::includes -> f includes
        | (s, Some (Some m))::includes ->
          (
            if x.StartsWith(m + ".") then
              let x = x.Substring(m.Length) in
              let qx = Id (s + x) in
              match Map.tryFind qx env.decls_map with
              | Some info -> (Some info, qx)
              | None -> (None, qx)
            else f includes
          )
        | (s, Some None)::includes ->
          (
            let qx = Id (s + "." + x) in
            match Map.tryFind qx env.decls_map with
            | Some info -> (Some info, qx)
            | None -> f includes
          )
        in
      f env.include_modules
    )
  | (_, None) -> (None, x)
(*
  match Map.tryFind x env.decls_map with
  | None -> (None, x)
  | Some ((Info _ | Func_decl _ | Proc_decl _ | Type_info _ | UnsupportedName _) as info) -> (Some info, x)
  | Some info ->
    (
      match info with
//      | Variable (s, t, info) when s = x -> (Some (Info (t, info)), x)
//      | Func (s, decl) when s = x -> (Some (Func_decl decl), x)
//      | Proc (s, decl) when s = x -> (Some (Proc_decl decl), x)
//      | Type (s, ts, kind, t) when s = x -> (Some (Type_info (ts, kind, t)), x)
//      | Const (s, t) when s = x -> (Some (Info (t, None)), x)
//      | Unsupported (s) when s = x -> (Some (UnsupportedName s), x)
      | Include_module (s, opened) when include_import ->
        match Some info with
        | Some r -> (Some r, x)
        | _ ->
        // TODO:
          // for non-qualified reference, the module has to be opened
          let qx = Id (s + "." + (string_of_id x)) in
          match Map.tryFind qx env.decls_map with
          | Some r -> if opened then (Some r, qx) else err (sprintf "module %s needs to be opened to reference %A" s x)
          | _ -> (None, x)
      | _ -> (None, x)
    )
*)
(*
  let find = function
  | Variable (s, t, info) when s = x -> (Some (Info (t, info)), x)
  | Func (s, decl) when s = x -> (Some (Func_decl decl), x)
  | Proc (s, decl) when s = x -> (Some (Proc_decl decl), x)
  | Type (s, ts, kind, t) when s = x -> (Some (Type_info (ts, kind, t)), x)
  | Const (s, t) when s = x -> (Some (Info (t, None)), x)
  | Unsupported (s) when s = x -> (Some (UnsupportedName s), x)
  | Include_module (s, opened) when include_import ->
    let r = Map.tryFind x env.decls_map in
    match r with
    | Some r -> (Some r, x)
    | _ ->
      // for non-qualified reference, the module has to be opened
      let qx = Id (s + "." + (string_of_id x)) in
      match Map.tryFind qx env.decls_map with
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
*)

//let push_scope_mod env x scope_mod =
// {env with decls_map = Map.add x (No_info, scope_mod) env.decls_map}

let try_lookup_id (env:env) (x:id):(typ * id_info option) option =
  match lookup_name env x true with
  | (Some (Info (t, info)), _) -> Some (t, info)
  | (Some (UnsupportedName (x, loc, msg)), _) -> unsupported loc msg ("identifier '" + (err_id x) + "' is declared 'unsupported')")
  | _ -> None

let lookup_id (env:env) (x:id):(typ * id_info option) =
  match try_lookup_id env x with
  | Some (t, info) -> (t, info)
  | _ -> err ("cannot find id '" + (err_id x) + "'")

// TODO: type arguments for collections
let lookup_primitive (env:env) (pt:primitive_type):id =
  match (Map.tryFind pt env.primitives_map, pt) with
  | (None, PT_State) -> Id "state"
  | (Some x, _) -> x
  | _ ->
      let s =
        match pt with
        | PT_State -> internalErr "PT_State"
        | PT_String -> "string"
        | PT_List -> "list"
        | PT_Seq -> "seq"
        | PT_Set -> "set"
        in
      err (sprintf "Could not find declaration 'type{:primitive} %s' (needed by type checker to check %s literals)" s s)

let try_lookup_type (env:env) (x:id):((tformal list option * kind * typ option) option * id) =
  let (t, qx) = lookup_name env x true in
  match t with
  | Some (Type_info (tfs, k, t)) -> (Some (tfs, k, t), qx)
  | Some (UnsupportedName (x, loc, msg)) -> unsupported loc msg ("type '" + (err_id x) + "' is declared 'unsupported'")
  | _ -> (None, x)

let lookup_type (env:env) (x:id):(tformal list option * kind * typ option) =
  match try_lookup_type env x with
  | (Some info, x) -> info
  | _ -> err ("cannot find type '" + (err_id x) + "'")

type fun_or_proc = FoundFunDecl of fun_decl | FoundFunExpr of fun_typ | FoundProc of proc_decl

let try_lookup_fun_or_proc (env:env) (x:id):fun_or_proc option =
  match lookup_name env x true with
  | (Some (Proc_decl p), _) -> Some (FoundProc p)
  | (Some (Func_decl f), _) -> Some (FoundFunDecl f)
  | (Some (Info (TFun f, _)), _) -> Some (FoundFunExpr f)
  | (Some (UnsupportedName (x, loc, msg)), _) -> unsupported loc msg ("function or procedure '" + (err_id x) + "' is declared 'unsupported'")
  | _ -> None

let lookup_fun_or_proc (env:env) (x:id):fun_or_proc =
//  let x = if x = Id "not" then Id "Prims.l_not" else x in
  match try_lookup_fun_or_proc env x with
  | Some t -> t
  | _ -> err ("cannot find function/procedure '" + (err_id x) + "'")

let lookup_fun_decl (env:env) (x:id):fun_decl =
  match try_lookup_fun_or_proc env x with
  | Some (FoundFunDecl f) -> f
  | _ -> err ("cannot find function '" + (err_id x) + "'")

let try_lookup_fun_decl (env:env) (x:id):fun_decl option =
  match try_lookup_fun_or_proc env x with
  | Some (FoundFunDecl f) -> Some f
  | _ -> None

let lookup_operand_type (env:env) (x:id):(pformal list option * typ * typ option * operand_typ list) =
  match lookup_name env x true with
  | (Some (OperandType_info (pformals, t, opr, os)), _) -> (pformals, t, opr, os)
  | _ -> err ("cannot find operand type '" + (err_id x) + "'")

// Substitute for TName x in t
let rec subst_typ_name (m:substitutions) (t:typ):typ =
  match t with
  | TName x ->
    (
      match Map.tryFind x m with
      | None -> t
      | Some t2 -> t2
    )
  | TBool _ | TInt _ -> t
  | TDependent x -> t // Since x is an expression name, not a type name, we never attempt substitution for it
  | TApply (xapp, ts) -> TApply (xapp, subst_typs_name m ts)
  | TFun (ts, t) -> TFun (subst_typs_name m ts, subst_typ_name m t)
  | TTuple ts -> TTuple (subst_typs_name m ts)
  | TVar (x, _) -> internalErr "subst_typ_name: TVar"
and subst_typs_name (m:substitutions) (ts:typ list):typ list =
  List.map (subst_typ_name m) ts

// Substitute for TVar x in t
let rec subst_typ (m:substitutions) (t:typ):typ =
  match t with
  | TName _ | TBool _ | TInt _ -> t
  | TDependent x -> t // Since x is an expression name, not a type name, we never attempt substitution for it
  | TApply (xapp, ts) -> TApply (xapp, subst_typs m ts)
  | TFun (ts, t) -> TFun (subst_typs m ts, subst_typ m t)
  | TTuple ts -> TTuple (subst_typs m ts)
  | TVar (x, _) ->
    (
      match Map.tryFind x m with
      | None -> t
      | Some t2 -> t2
    )
and subst_typs (m:substitutions) (ts:typ list):typ list =
  List.map (subst_typ m) ts

let rec normalize_type (env:env) (t:typ):typ =
  let r = normalize_type env in
  // REVIEW: do local variables interfere with name lookups here?
  match t with
  | TName x ->
    (
      match try_lookup_type env x with
      | (Some (_, _, tOpt), x)  ->
        (
          match tOpt with | Some t -> r t | None -> TName x // TODO: TName x might mean different things in different modules
        )
      | _ -> err ("cannot find type '" + (err_id x) + "'")
    )
  | TVar _ -> t
  | TBool _ -> t
  | TInt _ -> t
  | TTuple ts -> t
  | TFun (ts, t) -> t
  | TDependent x ->
      let (_, x) = lookup_name env x true in
      TDependent x
  | TApply (x, ts) ->
    (
      match try_lookup_type env x with
      | (Some (Some _, _, None), xt)  ->
        (
          TApply (xt, ts)
        )
      | (Some (Some tfs, _, Some t), x)  ->
        (
          let m = Map.ofList (List.map2 (fun (xf, _, _) tf -> (xf, tf)) tfs ts) in
          let t = subst_typ_name m t in
          r t
        )
      | _ -> err ("cannot find type '" + (err_id x) + "'")
    )

// HACK: mangle the parameter types. This will not be needed if transform is performed before typechecker.
let rec normalize_type_with_transform (env:env) (t:typ) (tr:transform_kind option):typ =
  normalize_type env t
(*
  let get_type env x t =
    match try_lookup_fun_or_proc env x with
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
  | (TApply (x, ts), _) ->
    let ts = List.map (fun t -> (normalize_type env t).norm_typ) ts in
    {norm_typ = TApply (x, ts)}
  | _ -> normalize_type env t
*)

let push_unsupported (env:env) (id:id) (loc:loc) (msg:string option):env =
//  let env = push_scope_mod env (Unsupported id)
  {env with decls_map = Map.add id (UnsupportedName (id, loc, msg)) env.decls_map}

let push_name_info (env:env) (id:id) (info:name_info):env =
//  let env = push_scope_mod env (Unsupported id)
  {env with decls_map = Map.add id info env.decls_map}

let push_include_module (env:env) (m:string) (b:string option option):env =
//  push_scope_mod env (Include_module (m, b))
//  push_name_info env (Id m) (Include_module (m, b))
  {env with include_modules = (m, b)::env.include_modules}

let push_id (env:env) (id:id) (t:typ):env =
//  push_scope_mod env id (Variable (id, t, None))
  push_name_info env id (Info (t, None))

let push_id_with_info (env:env) (id:id) (t:typ) (info:id_info option):env =
//  push_scope_mod env id (Variable (id, t, info))
  push_name_info env id (Info (t, info))

let push_func (env:env) (id:id) (f:fun_decl):env =
//  let env = push_scope_mod env (Func (id, t));
  {env with decls_map = Map.add id (Func_decl f) env.decls_map}

let push_proc (env:env) (id:id) (t:proc_decl):env =
  push_name_info env id (Proc_decl t)

let push_typ (env:env) (x:id) (ts:tformal list option) (k:kind) (t:typ option) (attrs:attrs):env =
//  let env = push_scope_mod env (Type (x, ts, k, t))
  let env =
    if attrs_get_bool (Id "primitive") false attrs then
      let pt =
        match x with
        | Id "state" -> PT_State
        | Id "string" -> PT_String
        | Id "list" -> PT_List
        | Id "seq" -> PT_Seq
        | Id "set" -> PT_Set
        | _ -> err (sprintf "unknown primitive type name %s" (err_id x))
        in
      {env with primitives_map = Map.add pt x env.primitives_map} // TODO: resolve x to fully-qualified name
    else env
    in
  {env with decls_map = Map.add x (Type_info (ts, k, t)) env.decls_map}

let push_const (env:env) (id:id) (t:typ):env =
  //  let env = push_scope_mod env (Const (id, t.norm_typ)) in
  {env with decls_map = Map.add id (Info (t, Some ConstGlobal)) env.decls_map}

let push_lhss (env:env) (lhss:lhs list):env =
  let push_lhs s (x,dOpt) =
    match dOpt with
    | Some (tOpt, _) ->
      let t = match tOpt with Some t -> t | None -> internalErr "push_lhss" in
      Map.add x (Info (t, None)) s
    | None -> s
  {env with decls_map = List.fold push_lhs env.decls_map lhss }

//let push_formals (env:env) (formals:formal list):env =
//  {env with decls_map = List.fold (fun s (x, t) -> let t = match t with Some t-> t | _-> next_type_var () in Map.add x (Info (t, None)) s) env.decls_map formals}

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

let unify_int_bound (env:env) (t1:typ) (t2:typ) (op:bop):typ =
  let t1 = normalize_type env t1 in
  let t2 = normalize_type env t2 in 
  match (t1, t2) with
  | (TInt (l1, h1), TInt (l2, h2)) ->
      let (l, h) = compute_bound l1 h1 l2 h2 op in
      TInt (l, h)
  | _ -> err (sprintf "expected two integer types, found '%A' and '%A'" (string_of_typ t1) (string_of_typ t2))

let neg_int_bound (t:typ):typ =
  match t with
  | TInt (b1, b2) -> TInt (bnd_neg b2, bnd_neg b1)
  | _ -> err ("int type is expected with neg operator")

let typ_equal env (t1:typ) (t2:typ):bool =
  normalize_type env t1 = normalize_type env t2

// Check t1 <: t2
let is_subtype (env:env) (t1:typ) (t2:typ):bool =
  let t1 = normalize_type env t1 in
  let t2 = normalize_type env t2 in
  match (t1, t2) with
  | (TBool BpBool, TBool BpProp) -> true
  | (TInt (l1, h1), TInt (l2, h2)) -> bnd_le l2 l1 && bnd_le h1 h2
  | _ -> t1 = t2

let isArithmeticOp op = match op with | BAdd | BSub | BMul | BDiv | BMod -> true | _ -> false
let isLogicOp op = match op with | BEquiv | BImply | BExply | BAnd _ | BOr _ -> true | _ -> false
let isIcmpOp op = match op with | BLt | BGt | BLe | BGe -> true | _ -> false

//let lookup_evar (env:env) (x:id):(typ * id_info option) =
//  match x with
//  | Id "False" -> lookup_id env (Id "Prims.l_False")
//  | Id "True" -> lookup_id env (Id "Prims.l_True")
//  | _ -> lookup_id env x

let compute_transform_info env (formal:pformal) (e:exp) =
  None
(*
  // if env.ghost=true, then it is always Ghost None
  let (g, opr, io) =
    (Ghost, None, In)
(*
    if env.ghost then (Ghost, None, In) else
    match formal with
    | (_, (TName (Id x)), XOperand, io, _) -> (NotGhost, Some x,  io)
    | (_, t, XInline, io, _) -> (Ghost, None, io)
    | (_, t, XAlias _, io, _) -> (NotGhost, None, io)  // XAlias is dropped
    | (_, t, XGhost, In, []) -> (Ghost, None, In)
    | (_, t, XGhost, _, []) -> err ("out/inout ghost parameters are not supported")
    | (x, _, _, _, _) -> err ("unexpected argument for parameter " + (err_id x)) in
*)
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
  | (NotGhost, EApply (x, _, _)) ->
    let operandProc (xa:id) (io:inout):id =
      let xa = string_of_id xa in
      match io with
      | In | InOut -> Id (xa + "_in")
      | Out -> Id (xa + "_out")
    let (proc, _) = try_lookup_fun_or_proc env (operandProc x io) in
    if (opr <> None && Option.isSome proc) then Some (EApplyCode) else None
  | _ -> None
*)

// TODO: more checking of variable name distinctness
let check_not_local env x =
  match lookup_name env x false with
  | (Some (Info (t, info)), _) -> err ("formal: " + (err_id x) + " is a local variable")
  | _ -> ()

// TODO: more checking of variable name distinctness
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

(*
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
*)

let kind_equal k1 k2 =
  // TODO: for KDependent, we have to resolve names to fully-qualified names
  k1 = k2

let rec check_type (env:env) (t:typ):kind =
  match t with
  | TName x ->
    (
      match lookup_type env x with
      | (None, k, _) -> k
      | (Some _, _, _) -> err (sprintf "type '%s' must be applied to type arguments" (err_id x))
    )
  | TApply (x, ts) ->
    (
      match lookup_type env x with
      | (None, _, _) -> err (sprintf "type '%s' cannot be applied to type arguments" (err_id x))
      | (Some ks, k, _) ->
        let nks = List.length ks in
        let nts = List.length ts in
        if (nks <> nts) then err (sprintf "expected %A type argument(s), found %A type argument(s)" nks nts) else
        List.iter2 (fun t (_, k, _) -> check_type_as env t k) ts ks;
        k
    )
  | TVar (_, Some k) -> k
  | TVar (_, None) -> internalErr "check_type: TVar"
  | TBool BpBool -> ktype0
  | TBool BpProp -> ktype1
  | TInt (_, _) -> ktype0
  | TTuple ts -> check_types_as env ts ktype0; ktype0
  | TFun (ts, t) -> check_types_as env ts ktype0; check_type_as env t ktype0; ktype0
  | TDependent x ->
    (
      match lookup_id env x with
      | (TName xt, Some ConstGlobal) -> KDependent xt
      | _ -> err (sprintf "variable '%s' must be a global constant whose type is a simple named type" (err_id x))
    )
and check_type_as (env:env) (t:typ) (k:kind):unit =
  let kt = check_type env t in
  if kt <> k then err (sprintf "expected type of kind %s, found type '%s' of kind %s" (string_of_kind k) (string_of_typ t) (string_of_kind kt))
and check_types_as (env:env) (ts:typ list) (k:kind):unit =
  List.iter (fun t -> check_type_as env t k) ts

let match_kind env (t:typ) (k:kind option) =
  match k with
  | Some k ->
    match t with
    | TVar (_, None) -> true
    | _ ->
      kind_equal (check_type env t) k
  | None -> true

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
  | TApply (_, l) -> aux false l
  | TTuple l -> aux false l
  | TFun (l, u) -> aux false l || occurs x u
  | _ -> false

(*
let bind (m:substitutions) (x:id) (t:typ):substitutions =
  match t with
  | TVar (y, k) -> if (x = y) then m else Map.add x t m
  | _ -> if occurs x t then err ("circular type constraint" + err_id x + " " + string_of_typ t) else Map.add x t m

let bind_typ (m:substitutions) (s:typ) (t:typ):substitutions =
  match s with
  | TVar (x, _) -> bind m x t
  | _ -> m
*)

let join2 (env:env) (t1:typ) (t2:typ):typ option =
  let t1 = normalize_type env t1 in
  let t2 = normalize_type env t2 in
  match (t1, t2) with
  | (TBool BpBool, TBool BpBool) -> Some (TBool BpBool)
  | (TBool BpProp, TBool BpBool) | (TBool BpBool, TBool BpProp) | (TBool BpProp, TBool BpProp) -> Some (TBool BpProp)
  | (TInt (b1l, b1h), TInt (b2l, b2h)) -> Some (TInt (bnd_min b1l b2l, bnd_max b1h b2h))
  | _ -> None

let meet2 (env:env) (t1:typ) (t2:typ):typ option =
  let t1 = normalize_type env t1 in
  let t2 = normalize_type env t2 in
  match (t1, t2) with
  | (TBool BpBool, TBool BpBool) | (TBool BpProp, TBool BpBool) | (TBool BpBool, TBool BpProp) -> Some (TBool BpBool)
  | (TBool BpProp, TBool BpProp) -> Some (TBool BpProp)
  | (TInt (b1l, b1h), TInt (b2l, b2h)) -> Some (TInt (bnd_max b1l b2l, bnd_min b1h b2h))
  | _ -> None

let rec join (env:env) (ts:typ list):typ option =
 match ts with
 | [] -> internalErr "join"
 | [t1] -> Some t1
 | t1::t2::ts -> match join2 env t1 t2 with None -> None | Some t -> join env (t::ts)

let rec meet (env:env) (ts:typ list):typ option =
 match ts with
 | [] -> internalErr "meet"
 | [t1] -> Some t1
 | t1::t2::ts -> match meet2 env t1 t2 with None -> None | Some t -> meet env (t::ts)

// If join fails, pick an arbitrary element of ts
let join_fallback (env:env) (ts:typ list):typ option =
  match ts with
  | [] -> None
  | t::_ -> match join env ts with None -> Some t | Some t -> Some t

let join_fallback2 (env:env) (t1:typ) (t2:typ):typ option =
  match join env [t1; t2] with None -> Some t1 | Some t -> Some t

// If meet fails, pick an arbitrary element of ts
let meet_fallback (env:env) (ts:typ list):typ option =
  match ts with
  | [] -> None
  | t::_ -> match meet env ts with None -> Some t | Some t -> Some t

type unifier =
  {
    u_env:env;
    mutable u_loc:loc option;
    mutable u_tvar_count:int;
    mutable u_tvars:Map<id, id>; // all tvars, mapped from internal names to user-friendly names
    mutable u_substs:substitutions;
    mutable u_equalities:(typ * typ * loc option) list; // t1 = t2
    // Invariant: The maps below never contain an empty list or set
    // Note: any subtype constraint t1 <: t2 that doesn't fit into the maps below is turned into an equality t1 = t2
    mutable ut_lowers:Map<id, (typ * loc option) list>; // t1 <: x ... tn <: x where t1...tn are integral or bool or prop
    mutable ut_uppers:Map<id, (typ * loc option) list>; // x <: t1 ... x <: tn where t1...tn are integral or bool or prop
    mutable ux_lowers:Map<id, Set<id>>; // x1 <: x ... xn <: x
    mutable ux_uppers:Map<id, Set<id>>; // x <: x1 ... x <: xn
    mutable ux_locs:Map<id * id, loc option>;
  }

let u_next_type_var_id (u:unifier) (x:id) (k:kind option):typ =
  let tvar = Id ("?" + (string_of_id x) + string (u.u_tvar_count)) in
  u.u_tvar_count <- u.u_tvar_count + 1;
  u.u_tvars <- Map.add tvar (match x with Id "" -> tvar | _ -> x) u.u_tvars
  TVar (tvar, k)

let u_next_type_var (u:unifier):typ =
  u_next_type_var_id u (Id "") None

let map_list_get (x:'a) (m:Map<'a, 'b list>):'b list =
  match Map.tryFind x m with
  | None -> []
  | Some l -> l

let map_set_get (x:'a) (m:Map<'a, Set<'b>>):Set<'b> =
  match Map.tryFind x m with
  | None -> Set.empty
  | Some s -> s

let map_list_add (x:'a) (y:'b) (m:Map<'a, 'b list>):Map<'a, 'b list> =
  Map.add x (y::(map_list_get x m)) m

let map_set_add (x:'a) (y:'b) (m:Map<'a, Set<'b>>):Map<'a, Set<'b>> =
  Map.add x (Set.add y (map_set_get x m)) m

let map_set_remove (x:'a) (y:'b) (m:Map<'a, Set<'b>>):Map<'a, Set<'b>> =
  if Map.containsKey x m then
    let s = Set.remove y (map_set_get x m) in
    if Set.isEmpty s then Map.remove x m else Map.add x s m
  else m

let rec collect_sub_or_super_types (u:unifier) (super:bool) (reached:Set<id>) (x:id):typ list * Set<id> =
  if Set.contains x reached then ([], reached) else
  let reached = Set.add x reached in
  let (tMap, succMap) = if super then (u.ut_uppers, u.ux_uppers) else (u.ut_lowers, u.ux_lowers) in
  let ts = List.map fst (map_list_get x tMap) in
  let succs = map_set_get x succMap in
  Set.fold (fun (ts, reached) x -> collect_sub_or_super_types u super reached x) (ts, reached) succs

(*
Algorithm and heuristics to resolve type constraints:

Phase 1: Process u_equalities until u_equalities = []:
  - Move any x = t or t = x in u_equalities into u_substs and substitute t for x in all fields of unifier
    - Note that substitution may move constraints among fields of unifier
  - Reduce any other t1 = t2 in u_equalities based on the structure of t1 and t2
Phase 2: Resolve any remaining variables in the subtype graph
  - For any variable x, let:
    - Sub(x) be the set of all non-variable subtypes of x in the graph
    - Super(x) be the set of all non-variable supertypes of x in the graph
    (Both Sub and Super are computed recursively walking through the graph)
  - For any x that we want to resolve:
    - If Sub(x) is non-empty, substitute meet(Sub(x)) for x
    - Otherwise, if Super(x) is non-empty, substitute meet(Super(x)) for x
    - Otherwise, x is underconstrained, and we consider this a type error
Note that we need not resolve all variables at once.  Because of overloading,
we sometimes need to resolve some variables early to disambiguate the overloading,
but we delay resolving other variables.
*)

let new_unifier (env:env) (loc:loc option):unifier =
  {
    u_env = env;
    u_loc = loc;
    u_tvar_count = 0;
    u_tvars = Map.empty;
    u_substs = Map.empty;
    u_equalities = [];
    ut_lowers = Map.empty;
    ut_uppers = Map.empty;
    ux_lowers = Map.empty;
    ux_uppers = Map.empty;
    ux_locs = Map.empty;
  }

// t1 = t2
let u_constrain_equal_loc (u:unifier) (loc:loc option) (t1:typ) (t2:typ):unit =
  let env = u.u_env in
  if typ_equal env t1 t2 then () else
  // printfn "constrain %A = %A at %A" t1 t2 (match loc with None -> "None" | Some loc -> string_of_loc loc);
  u.u_equalities <- (t1, t2, loc)::u.u_equalities

let u_constrain_equal (u:unifier) (t1:typ) (t2:typ):unit =
  u_constrain_equal_loc u u.u_loc t1 t2

// t1 <: t2
let u_constrain_subtype_loc (u:unifier) (loc:loc option) (t1:typ) (t2:typ):unit =
  if t1 = t2 then () else
  let env = u.u_env in
  let t1 = subst_typ u.u_substs t1 in
  let t2 = subst_typ u.u_substs t2 in
  if t1 = t2 then () else
  // printfn "constrain %A <: %A at %A" t1 t2 (match loc with None -> "None" | Some loc -> string_of_loc loc);
  let t1_norm = normalize_type env t1 in
  let t2_norm = normalize_type env t2 in
  match (t1_norm, t2_norm) with
  | (TVar (x1, _), TVar (x2, _)) ->
    u.ux_uppers <- map_set_add x1 x2 u.ux_uppers;
    u.ux_lowers <- map_set_add x2 x1 u.ux_lowers;
    u.ux_locs <- Map.add (x1, x2) loc u.ux_locs;
  | (TVar (x1, _), (TInt _ | TBool _)) ->
    u.ut_uppers <- map_list_add x1 (t2, u.u_loc) u.ut_uppers
  | ((TInt _ | TBool _), TVar (x2, _)) ->
    u.ut_lowers <- map_list_add x2 (t1, u.u_loc) u.ut_lowers
  | (TInt _, TInt _) when is_subtype env t1 t2 -> ()
  | (TBool BpBool, TBool BpProp) -> ()
  | _ -> u_constrain_equal_loc u loc t1 t2

let u_constrain_subtype (u:unifier) (t1:typ) (t2:typ):unit =
  u_constrain_subtype_loc u u.u_loc t1 t2

let u_constrain_subtype_opt (u:unifier) (src_typ:typ) (expected_typ:typ option):unit =
  match expected_typ with
  | None -> ()
  | Some et -> u_constrain_subtype u src_typ et

let u_add_subst (u:unifier) (x:id) (t:typ):unit =
  //printfn "begin add_subst %A %A" x t;
  let cs = ref [] in
  u.u_substs <- Map.add x t u.u_substs;
  let ft m f_apply =
    match Map.tryFind x m with
    | None -> m
    | Some ts -> List.iter f_apply ts; Map.remove x m
    in
  u.ut_lowers <- ft u.ut_lowers (fun (t2, loc) -> cs := (t2, t, loc)::!cs); // t2 <: x --> t2 <: t
  u.ut_uppers <- ft u.ut_uppers (fun (t2, loc) -> cs := (t, t2, loc)::!cs); // x <: t2 --> t <: t2
  let fx m1 m2 f_apply =
    match Map.tryFind x m1 with
    | None -> (m1, m2)
    | Some xs ->
        Set.iter f_apply xs;
        (Map.remove x m1, Set.fold (fun m2 x2 -> map_set_remove x2 x m2) m2 xs)
    in
  let find_loc (x1:id) (x2:id):loc option = Option.bind (fun x -> x) (Map.tryFind (x1, x2) u.ux_locs) in
  let (ml, mu) = (u.ux_lowers, u.ux_uppers) in
  let (ml, mu) = fx ml mu (fun x2 -> cs := (TVar (x2, None), t, find_loc x2 x)::!cs) in // x2 <: x --> x2 <: t
  let (mu, ml) = fx mu ml (fun x2 -> cs := (t, TVar (x2, None), find_loc x x2)::!cs) in // x <: x2 --> t <: x2
  u.ux_lowers <- ml;
  u.ux_uppers <- mu;
  //printfn "end add_subst %A %A %A %A" x t !cs u;
  List.iter (fun (t1, t2, loc) -> u_constrain_subtype_loc u loc t1 t2) !cs

let u_apply_subst (u:unifier):unit =
  let subs (t:typ):typ = subst_typ u.u_substs t in
  u.u_substs <- Map.map (fun _ t -> subs t) u.u_substs;
  u.u_equalities <- List.map (fun (t1, t2, loc) -> (subs t1, subs t2, loc)) u.u_equalities
  // Note that the types in ut_* cannot have type variables, so we don't substitute in them

let u_bind (u:unifier) (x:id) (t:typ):unit =
  match t with
  | TVar (y, _) when x = y -> ()
  | TVar (y, _) -> u_add_subst u x t
  | _ ->
    if occurs x t then
      err ("circular type constraint" + err_id x + " " + string_of_typ t)
    else u_add_subst u x t

let rec u_unify_one (u:unifier) (loc:loc option) (t1:typ) (t2:typ):unit =
  let r = u_unify_one u loc in
  if t1 = t2 then () else
  let env = u.u_env in
  let t1 = subst_typ u.u_substs t1 in
  let t2 = subst_typ u.u_substs t2 in
  if t1 = t2 then () else
  let typ_err () = err ("cannot coerce type '" + string_of_typ t1 + "' to type '" + string_of_typ t2 + "'") in
  match (t1, t2) with
  | (TVar (x, _), _) -> u_bind u x t2
  | (_, TVar (x, _)) -> u_bind u x t1
  | (TTuple ts1, TTuple ts2) when List.length ts1 = List.length ts2 ->
      List.iter2 (fun t1 t2 -> u_constrain_equal_loc u loc t1 t2) ts1 ts2
  | (TFun (ts1, t1), TFun (ts2, t2)) when List.length ts1 = List.length ts2 ->
      List.iter2 (fun t1 t2 -> u_constrain_equal_loc u loc t1 t2) ts1 ts2;
      u_constrain_equal_loc u loc t1 t2
  | (TApply (x1, ts1), TApply (x2, ts2)) when x1 = x2 && List.length ts1 = List.length ts2 ->
      List.iter2 (fun t1 t2 -> u_constrain_equal_loc u loc t1 t2) ts1 ts2
  | _ when typ_equal env t1 t2 -> () 
  | _ -> 
    let norm1 = normalize_type env t1 in
    let norm2 = normalize_type env t2 in
    if norm1 = t1 && norm2 = t2 then typ_err() else
    r norm1 norm2

let rec u_unify_equalities (u:unifier):unit =
  match u.u_equalities with
  | [] -> ()
  | _ ->
      let eqs = u.u_equalities in
      u.u_equalities <- [];
      List.iter (fun (t1, t2, loc) -> try u_unify_one u loc t1 t2 with err -> locErrOpt loc err) eqs;
      u_apply_subst u;
      u_unify_equalities u

let u_unify (u:unifier) (xs_opt:Set<id> option):unit =
  // phase 1
  u_unify_equalities u;
  // phase 2
  let xs =
    match xs_opt with
    | None -> Set.unionMany [map_domain_set u.ut_lowers; map_domain_set u.ut_uppers; map_domain_set u.ux_lowers; map_domain_set u.ux_uppers]
    | Some xs -> xs
    in
  let subs = ref [] in
  let err_no_infer (x:id):unit =
    err (sprintf "cannot infer type for type variable '%s' (you may need to add more type annotations to variables or type arguments to functions)" (err_id x))
    in
  Set.iter (fun x ->
      //printfn "processing %A" x;
      if Map.containsKey x u.u_substs then () else
      let (sub_ts, _) = collect_sub_or_super_types u false Set.empty x in
      let (super_ts, _) = collect_sub_or_super_types u true Set.empty x in
      match meet_fallback u.u_env super_ts with
      | Some t -> subs := (x, t)::!subs
      | None ->
        (
          match join_fallback u.u_env sub_ts with
          | Some t -> subs := (x, t)::!subs
          | None -> err_no_infer x
        )
    )
    xs;
  List.iter (fun (x, t) -> u_add_subst u x t) !subs;
  // Handle any remaining bool/prop/int constraints:
  u_unify_equalities u;
  // Check that all tvars are resolved:
  let check_resolved (x:id) (x_nice):unit =
    if not (Map.containsKey x u.u_substs) then err_no_infer x_nice
    in
  (match xs_opt with Some _ -> () | None -> Map.iter check_resolved u.u_tvars);
  ()

(*
// exact = true ==> s = t
// exact = false ==> s <: t
let rec unify_one (env:env) (exact:bool) (m:substitutions) (s:typ) (t:typ):substitutions =
  if s = t then m else
  let s = subst_typ m s in
  let t = subst_typ m t in
  if s = t then m else
  let typ_err () =
    if exact then err ("type '" + string_of_typ s + "' is not equal to type '" + string_of_typ t + "'")
    else err ("cannot coerce type '" + string_of_typ s + "' to type '" + string_of_typ t + "'")
    in
  let t1 = normalize_type env s in
  let t2 = normalize_type env t in
  match (t1.norm_typ, t2.norm_typ) with
  // TODO: TVar cases for exact = false
  | (TVar (x, _), _) -> bind m x t2.norm_typ
  | (_, TVar (x, _)) -> bind m x t1.norm_typ
  | (TInt _, TInt _) when not exact && is_subtype env t1 t2 -> m
  | (TBool BpBool, TBool BpProp) when not exact -> m
  | (TTuple ts, TTuple us) when List.length ts = List.length us ->
    let tc = List.fold2 (fun l t1 t2 -> constrain_equal t1 t2 l) [] ts us in
    unify env m tc
  | (TFun (xs, y), TFun (us, v)) when List.length xs = List.length us ->
    let tc = List.fold2 (fun l t1 t2 -> constrain_equal t1 t2 l) [] xs us in
    unify env m (constrain_equal y v tc)
  | (TApply (x, ys), TApply (u, vs)) when x = u && List.length ys = List.length vs ->
    let tc = List.fold2 (fun (l:typ_constraints) t1 t2 -> constrain_equal t1 t2 l) [] ys vs in
    unify env m tc
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
*)

let compute_type_arguments (env:env) (u:unifier) (tparams:tformal list) (ts_opt:typ list option): substitutions =
  let targOpts =
    match ts_opt with
    | None -> List.map (fun _ -> None) tparams
    | Some ts -> List.map Some ts
    in
  let nts = List.length targOpts in
  let nks = List.length tparams in
  if nts <> nks then err (sprintf "expected %A type argument(s), found %A type argument(s)" nks nts) else
  List.iter2 (fun tOpt (_, k, _) -> match tOpt with Some t -> check_type_as env t k | None -> ()) targOpts tparams;
  let ft tOpt (x, k, _) =
    match tOpt with
    | None -> (x, u_next_type_var_id u x (Some k))
    | Some t -> (x, t)
    in
  let targMap = Map.ofList (List.map2 ft targOpts tparams) in
  targMap

let compute_instance (env:env) (u:unifier) (targMap:substitutions):(typ -> typ) =
  let replace_typ_arg (t:typ):typ = subst_typ_name targMap t in
  let arg_typ t = replace_typ_arg t in
  arg_typ

let compute_fun_instance (env:env) (u:unifier) (f:fun_decl) (ts_opt:typ list option):fun_instance =
  let targMap = compute_type_arguments env u f.ftargs ts_opt in
  let targs = Map.fold (fun l x t -> l@[t]) [] targMap in
  let arg_typ = compute_instance env u targMap in
  let args =
    List.fold
      (fun l (id, t) -> let t = match t with | Some t -> t | None -> u_next_type_var_id u id None in l @ [arg_typ t])
      []
      f.fargs
      in
  let ret = arg_typ f.fret in
  {f_args = args; f_targs = targs; f_ret = ret (*; f_ret_name = f.fret_name; f_specs = f.fspecs; f_attrs = f.fattrs*)}

let compute_proc_instance (env:env) (u:unifier) (p:proc_decl) (ts_opt:typ list option):proc_instance =
  let targMap = compute_type_arguments env u p.ptargs ts_opt in
  let targs = Map.fold (fun l x t -> l@[t]) [] targMap in
  let arg_typ = compute_instance env u targMap in
  let fformal (x, t, storage, io, attrs):pformal =
    let t =
      match storage with
      | XGhost | XInline -> arg_typ t
      | XOperand -> t
      | _ -> notImplemented (sprintf "compute_proc_instance: %A" storage)
      in
    (x, t, storage, io, attrs) in
  {p_args = List.map fformal p.pargs; p_targs = targs; p_rets = List.map fformal p.prets}

let insert_cast (e:exp) (et:typ):exp =
  // cast from type 't' to 'et' and it is checked by SMT solver
  ECast (e, et)

let rec subst_exp env (s:substitutions) ((e, t, coerce):aexp):exp =
  let coerce = Option.map (fun (t, et) -> (subst_typ s t, subst_typ s et)) coerce in
  let e =
    match e with
    | AE_Loc (loc, ae) -> ELoc (loc, subst_exp env s ae)
    | AE_Exp e -> e
    | AE_Op (op, aes) ->
      (
        let es = List.map (subst_exp env s) aes in
        let bool_prop f =
          match coerce with
          | Some (TBool BpBool, _) -> EOp (f BpBool, es, Some t)
          | Some (TBool BpProp, _) -> EOp (f BpProp, es, Some t)
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
        | _ -> EOp (op, es, Some t)
      )
//      let e = EOp (op, es) in
//      if (typ_equal env t et) then e else insert_cast e t et
(*
    | AEApply (Id "list", aes, ts, ets) ->
      let es = List.map (fun ae -> subst_exp env s ae) aes  in
      let t = (List.map (fun t -> subst_typ s t) ts).Head in
      let et = (List.map (fun t -> subst_typ s t) ets).Head in
      let e = EApply (Id "list", Some ts, es) in
      match (t, et) with
      | (TList [x], TList [y]) ->
        if typ_equal env x y then
          if (kind_equal (check_type env x) (KType bigint.Zero)) then e
          else err ("Only 'Type0' is allowed in list")
        else
          err (sprintf "inferred list type %s does not match expected list type %s" (string_of_typ t) (string_of_typ et))
      | _ -> err (sprintf "list type %A expected but got %A" (string_of_typ et) (string_of_typ t))
    | AEApply (Id "tuple", aes, ts, ets) ->
      let es = List.map (fun ae -> subst_exp env s ae) aes  in
      let t = (List.map (fun t -> subst_typ s t) ts).Head in
      let et = (List.map (fun t -> subst_typ s t) ets).Head in
      let e = EOp (TupleOp (Some ts), es) in
      match (t, et) with
      | (TTuple xs, TTuple ys) ->
        List.iter2 (fun t1 t2 -> if (not (typ_equal env t1 t2)) then err (sprintf "inferred tuple type %s does not match expected tuple type %s" (string_of_typ et) (string_of_typ t))) xs ys;
        List.iter (fun t -> if (not (kind_equal (check_type env t) (KType bigint.Zero))) then err "Only 'Type0' is allowed in tuple") xs;
        e
      | _ -> err (sprintf "tuple type %s expected but got %s" (string_of_typ et) (string_of_typ t))734
    | AEApply (x, aes, ts, ets) ->
      let es = List.map (fun ae -> subst_exp env s ae) aes  in
      let t = List.map (fun t -> subst_typ s t) ts in
      let et = List.map (fun t -> subst_typ s t) ets in
      let e = EApply (x, Some ts, es) in
      let equal = List.fold2 (fun b t1 t2 -> b&&typ_equal env t1 t2) true t et
      if equal then e else
        if(List.length t <> 1) then err ("cast for more than one return types not implemented");
        else insert_cast e t.Head et.Head
*)
    | AE_ApplyX (x, ts, aes) ->
        let es = List.map (subst_exp env s) aes in
        let ts = List.map (subst_typ s) ts in
        EApply (EVar (x, None), Some ts, es, Some t)
    | AE_ApplyE (ae, aes) ->
        let e = subst_exp env s ae in
        let es = List.map (subst_exp env s) aes in
        EApply (e, None, es, Some t)
    | AE_Bind (bOp, aes, xs, ts, ae) ->
        let es = List.map (subst_exp env s) aes in
        let e = subst_exp env s ae in
        EBind(bOp, es, xs, ts, e, Some t)
    | AE_Cast (ae, t) ->
        ECast ((subst_exp env s ae), t)
  in
  let annotate_exp e t =
    match e with
    | EVar (x, _) -> EVar (x, Some t)
    | EOp (op, es, _) -> EOp (op, es, Some t)
    | EApply (e, ts, es, _) -> EApply (e, ts, es, Some t)
    | EBind (bop, es, fs, ts, e, _) -> EBind (bop, es, fs, ts, e, Some t)
    | _ -> e
  in
  match coerce with
  | None -> annotate_exp e t
  | Some (t, et) -> if typ_equal env t et then annotate_exp e et else insert_cast (annotate_exp e t) et

let rec infer_arg_typ (env:env) (u:unifier) (args:(exp * typ option) list):(typ list * aexp list) =
  let infer_arg_typ_fold (ts, ae) ((e:exp), (et:typ option)):(typ list * aexp list) =
    let (t, ae1) =
(*
      let tr =
        match formal with
        | Some f ->
          compute_transform_info env f (e:exp)
        | _ -> if env.ghost then Some EvalOp else None
*)
      match skip_loc e with
(*
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
      | EApply (x, ts, es) ->
        match tr with
        | Some EApplyCode ->
          let vx = Id (qprefix ("va_opr_code_") (string_of_id x)) in
          let ecs = List.collect (fun e -> match e with EOp (Uop UGhostOnly, [e]) -> [] | _ -> [e]) es in
          let ea = EApply (vx, ts, ecs) in
          let (t, ae, s) = infer_exp env ea et in
          let ae =
            match ae with
            | AEApply (_, es, t, et) -> AEApply (x, es, t, et)
            | _ -> internalErr ("EApply expected") in
          (t, ae, s)
        | _ -> infer_exp env e et
*)
      | _ -> infer_exp env u e et in
    (t::ts, ae1::ae)
  in
  let (ts_rev, aes_rev) = List.fold infer_arg_typ_fold ([], []) args in
  (List.rev ts_rev, List.rev aes_rev)

and infer_exps (env:env) (u:unifier) (args:(exp * typ option) list):(typ list * aexp list) =
  let infer_exps_fold (ts, ae) ((e:exp), (et:typ option)):(typ list * aexp list) =
    let (t, ae1) = infer_exp env u e et in
    (t::ts, ae1::ae)
  in
  let (ts_rev, aes_rev) = List.fold infer_exps_fold ([], []) args in
  (List.rev ts_rev, List.rev aes_rev)
and infer_exp (env:env) (u:unifier) (e:exp) (expected_typ:typ option):(typ * aexp) =
  // printfn "infer_exp %A at %A" e (match u.u_loc with None -> "None" | Some loc -> string_of_loc loc);
  let ret (t:typ) (ae:aexp_t) =
    let coerce =
      match expected_typ with
      | None -> None
      | Some et -> if typ_equal env t et then None else Some (t, et)
      in
    u_constrain_subtype_opt u t expected_typ;
    (t, (ae, t, coerce))
    in
  let check_collection_literal (e:exp) (pt:primitive_type) (ts_opt:typ list option) (es:exp list) =
    let tv = u_next_type_var u in
    let () =
      match ts_opt with
      | None -> ()
      | Some [t] -> u_constrain_subtype u tv t
      | Some _ -> err "collection type literal requires exactly one type argument"
      in
    let aes = List.map (fun e -> snd (infer_exp env u e (Some tv))) es in
    let xt = lookup_primitive env pt in
    let t = tapply xt [tv] in
    ret t (AE_ApplyX (id_of_exp e, [tv], aes))
  match e with
  | ELoc (loc, e) ->
      try
        let old_loc = u.u_loc in
        u.u_loc <- Some loc;
        let (t, ae) = infer_exp env u e expected_typ in
        u.u_loc <- old_loc;
        (t, (AE_Loc (loc, ae), t, None))
      with err -> locErr loc err
  | EVar (x, _) ->
      let (t, info) = lookup_id env x in
      let () =
        match (env.inline_only, info) with
        | (false, _) -> ()
        | (_, Some (InlineLocal | ConstGlobal)) -> ()
        | _ -> err "only inline variables and global const variables are allowed in inline expressions"
        in
      ret t (AE_Exp e)
  | EInt i -> ret (TInt (Int i, Int i)) (AE_Exp e)
  | EReal r -> ret (TName (Id "real")) (AE_Exp e)
//    | EBitVector (n, i) -> TODO
  | EBool b -> ret tBool (AE_Exp e)
  | EString s -> ret (TName (Id "string")) (AE_Exp e)
  | EOp (Uop (UConst | UOld) as op, [e], _) ->
      let (t, ae) = infer_exp env u e expected_typ in
      ret t (AE_Op (op, [ae]))
  | EOp (Uop UNeg, [e], _) ->
      let (t, ae) = infer_exp env u e None in
      let t = neg_int_bound t in
      ret t (AE_Op (Uop UNeg, [ae]))
  | EOp (Uop (UNot _) as op, [e], _) ->
      let tv = u_next_type_var u in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (_, ae) = infer_exp env u e (Some et) in
      u_constrain_subtype u tv tProp;
      u_constrain_subtype u tv et;
      (tv, (AE_Op (op, [ae]), tv, Some (tv, et))) // Some (tv, et) used to resolve overload
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
*)
  | EOp (Uop (UCustom op), es, _) ->
    (
      let f = lookup_fun_decl env (Operator op) in
      let e = eapply (attrs_get_id (Reserved "alias") f.fattrs) es in
      let (t, ae) = infer_exp env u e expected_typ in
      match ae with
      | (AE_ApplyX (_, _, es), _,  _) -> ret t (AE_Op (Uop (UCustom op), es))
      | _ -> internalErr "UCustom"
    )
(*
  | EOp (Uop UToOperand, _) ->
    err (sprintf "missing typing rule for Uop UToOperand")
  | EOp (Uop op, _) ->
    err (sprintf  "unsupported Uop '%A' in typechecker" op)
*)
  | EOp (Bop op, [e1; e2], _) when isArithmeticOp op ->
    // op in {+, -, *, /, %}
      let (t1, ae1) = infer_exp_force env u e1 None in
      let (t2, ae2) = infer_exp_force env u e2 None in
      let t = unify_int_bound env t1 t2 op in
      ret t (AE_Op (Bop op, [ae1; ae2]))
  | EOp (Bop (BAnd _ | BOr _) as op, [e1; e2], _) ->
      let tv = u_next_type_var u in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (_, ae1) = infer_exp env u e1 (Some et) in
      let (_, ae2) = infer_exp env u e2 (Some et) in
      u_constrain_subtype u tv tProp;
      u_constrain_subtype u tv et;
      (tv, (AE_Op (op, [ae1; ae2]), tv, Some (tv, et))) // Some (tv, et) used to resolve overload
  | EOp (Bop (BEquiv | BImply | BExply) as op, [e1; e2], _) ->
      let (_, ae1) = infer_exp env u e1 (Some tProp) in
      let (_, ae2) = infer_exp env u e2 (Some tProp) in
      ret tProp (AE_Op (op, [ae1; ae2]))
  | EOp (Bop op, [e1; e2], _) when isIcmpOp op ->
    (
      // op in {<, > , <=, >=} and it can be chained
      match (op, skip_loc e1) with
      | (op, EOp (Bop op1, [e11; e12], _)) when isIcmpOp op1 ->
          // Convert (a <= b) < c into (a <= b) && (b < c)
          let e2 = eop (Bop op) [e12; e2] in
          let e = eop (Bop (BAnd BpBool)) [e1; e2] in
          infer_exp env u e expected_typ
      | _ ->
        let (_, ae1) = infer_exp env u e1 (Some tInt) in
        let (_, ae2) = infer_exp env u e2 (Some tInt) in
        ret tBool (AE_Op (Bop op, [ae1; ae2]))
    )
  | EOp (Bop (BEq opt | BNe opt) as op, [e1; e2], _) ->
      let tv = u_next_type_var u in
      let (t1, ae1) = infer_exp env u e1 (Some tv) in
      let (t2, ae2) = infer_exp env u e2 (Some tv) in
      u_constrain_subtype u t1 tv;
      u_constrain_subtype u t2 tv;
      let t =
        // REVIEW: do we want different treatment of == between Dafny and F*?
        match (!fstar, opt, expected_typ) with
        | (false, _, _) -> tBool
        | (true, BpBool, _) -> tBool
        | (true, BpProp, Some (TBool BpBool)) -> tBool
        | (true, BpProp, _) -> tProp
        in
      ret t (AE_Op (op, [ae1; ae2]))
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
*)
  | EOp (Bop (BCustom op), es, _) ->
    (
      let f = lookup_fun_decl env (Operator op) in
      let e = eapply (attrs_get_id (Reserved "alias") f.fattrs) es in
      let (t, ae) = infer_exp env u e expected_typ in
      match ae with
      | (AE_ApplyX (_, _, es), _, _) -> ret t (AE_Op (Bop (BCustom op), es))
      | _ -> internalErr "BCustom"
    )
  | EOp (Subscript, [e1; e2], _) ->
    (
      let (t1, ae1) = infer_exp_force env u e1 expected_typ in
      let x =
        match t1 with
        | TName (Id x) | TApply (Id x, _) -> x
        | _ -> err (sprintf "cannot find overloaded operator([]) function for collection of type %s" (string_of_typ t1))
        in
      let e = eapply (Operator (x + "[]")) [e1; e2] in
      let (t, ae) = infer_exp env u e expected_typ in
      match ae with
      | (AE_ApplyX (_, _, es), _, _) -> ret t (AE_Op (Subscript, es))
      | _ -> internalErr ("EOp Subscript")
    )
  | EOp (Update, [e1; e2; e3], _) ->
    (
      let (t1, ae1) = infer_exp_force env u e1 expected_typ in
      let x =
        match t1 with
        | TName (Id x) | TApply (Id x, _) -> x
        | _ -> err (sprintf "cannot find overloaded operator([:=]) function for collection of type %s" (string_of_typ t1))
        in
      let e = eapply (Operator (x + "[:=]")) [e1; e2; e3] in
      let (t, ae) = infer_exp env u e expected_typ in
      match ae with
      | (AE_ApplyX (_, _, es), _, _) -> ret t (AE_Op (Update, es))
      | _ -> internalErr ("EOp Update")
    )
  | EOp (Bop BIn, [e1; e2], _) ->
    (
      let (t2, ae2) = infer_exp_force env u e2 expected_typ in
      let x =
        match t2 with
        | TName (Id x) | TApply (Id x, _) -> x
        | _ -> err (sprintf "cannot find overloaded operator(?[]) function for collection of type %s" (string_of_typ t2))
        in
      let e = eapply (Operator (x + "?[]")) [e2; e1] in
      let (t, ae) = infer_exp env u e expected_typ in
      match ae with
      | (AE_ApplyX (_, _, [e2; e1]), _, _) -> ret t (AE_Op (Bop BIn, [e1; e2]))
      | _ -> internalErr ("EOp Bop BIn")
    )
(*
  | EOp (Update, [e1; e2; e3]) ->
    let e = EApply ((Id "update"), [e1; e2; e3]) in
    let (t, ae, s) = infer_exp env e expected_typ in
    let ae =
      match ae with
      | AEApply (x, es, [t], [et]) -> AE_Op (Update, es, t, et)
      | _ -> err ("'Update' should be converted to 'EApply' first before typecheckings") in
    (t, ae, s)
*)
  | EOp (FieldOp (Id xf), [e1], _) ->
    (
      let (t1, ae1) = infer_exp_force env u e1 expected_typ in
      let t1 = normalize_type env t1 in
      let x1 =
        match t1 with
        | TName (Id x1) | TApply (Id x1, _) -> x1
        | TTuple ts -> "tuple " + string (List.length ts)
        | _ -> err (sprintf "cannot find overloaded operator(.%s) function for type %s" xf (string_of_typ t1))
        in
      let e = eapply (Operator (x1 + " ." + xf)) [e1] in
      let (t, ae) = infer_exp env u e expected_typ in
      match (t1, ae) with
      | (TTuple ts, (AE_ApplyX (_, _, es), _,  _)) ->
          ret t (AE_ApplyX (Id (sprintf "__proj__Mktuple%d__item__%s" (List.length ts) xf), ts, es))
      | (_, (AE_ApplyX (_, _, es), _, _)) -> ret t (AE_Op (FieldOp (Id xf), es))
      | _ -> internalErr ("EOp FieldOp")
    )
  | EOp (FieldUpdate (Id xf), [e1; e2], _) ->
    (
      let (t1, ae1) = infer_exp_force env u e1 expected_typ in
      let x1 =
        match t1 with
        | TName (Id x1) | TApply (Id x1, _) -> x1
        | _ -> err (sprintf "cannot find overloaded operator(.%s :=) function for type %s" xf (string_of_typ t1))
        in
      let e = eapply (Operator (x1 + " ." + xf + ":=")) [e1; e2] in
      let (t, ae) = infer_exp env u e expected_typ in
      match ae with
      | (AE_ApplyX (_, _, es), _, _) -> ret t (AE_Op (FieldUpdate (Id xf), es))
      | _ -> internalErr ("EOp FieldOp")
    )
  | EOp (Cond, [e1; e2; e3], _) ->
      let tv = u_next_type_var u in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (t1, ae1) = infer_exp env u e1 (Some tBool) in
      let (t2, ae2) = infer_exp env u e2 (Some et) in
      let (t3, ae3) = infer_exp env u e3 (Some et) in
      u_constrain_subtype u t2 tv;
      u_constrain_subtype u t3 tv;
      ret tv (AE_Op (Cond, [ae1; ae2; ae3]))
  | EOp (Uop UToOperand, [e1], _) ->
    (
      match skip_loc e1 with
      | EVar (x, _) ->
        (
          match lookup_id env x with
          | (_, Some (OperandLocal (_, TName xt))) ->
            (
              match lookup_operand_type env xt with
              | (_, _, None, _) ->
                  err (sprintf "declare 'operand_type %s:t1@t2 ...' so that '@%s' will have type t2 for some type t2 (without the '@t2', no type can be given here)" (err_id xt) (err_id x))
              | (_, _, Some t, _) -> ret t (AE_Exp e)
            )
          | _ -> err (sprintf "cannot find operand %s for @ operator" (err_id x))
        )
      | _ -> err "@ operator requires an operand name"
    )
(*TODO
  | EOp (FieldOp x, [e]) ->
    let (t1, _, _) = infer_exp env e None in
    let (t, ae, s) =
      match (t1,x) with
      | (TApply (x, _), (Id f)) ->
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
  | EApply (Id "list", _, es) ->
    let tv = next_type_var () in
    let arg_typ = next_type_var () in
    let (arg_typs, aes, s) = infer_arg_typ env (List.map (fun e -> (e, None, Some arg_typ)) es) in
    let et = tapply (Id "list") [arg_typ] in
    let ae = AEApply (Id "list", aes, [tv], [et]) in
    let s = List.fold (fun l t -> l @ [(t, arg_typ)]) s arg_typs in
    (tv, ae, [(tv, et)] @ s)
*)
  | EOp (TupleOp _, es, _) ->
      let ts =
        match expected_typ with
        | Some (TTuple ts) -> ts
        | _ -> List.map (fun _ -> u_next_type_var u) es
        in
      let t = TTuple ts in
      let (_, aes) = infer_exps env u (List.map2 (fun e t -> (e, Some t)) es ts) in
      ret t (AE_ApplyX (Id "tuple", ts, aes))
  | EBind (BindLet, [ex], [(x, t)], [], e, _) ->
      // let x:t := ex in e
      check_not_local env x;
      let (t1, ae1) = infer_exp env u ex t in
      let xt = match t with | Some t -> t | _ -> t1 in
      let env = push_id env x xt in
      let (t2, ae2) = infer_exp env u e expected_typ in
      u_constrain_subtype u t1 xt;
      ret t2 (AE_Bind (BindLet, [ae1], [(x, t)], [], ae2))
  | EBind (((Forall | Exists) as b), [], fs, ts, e, _) ->
      // fs list of formals, that are distinct and are not local variables
      // ts: triggers
      // e: prop
      let env = List.fold (fun env (x, t) -> let t = match t with Some t -> t | None -> u_next_type_var u in push_id env x t) env fs in
      let (t, ae) = infer_exp env u e expected_typ in
      u_constrain_subtype u t tProp;
      ret t (AE_Bind (b, [], fs, ts, ae))
  | EBind (Lambda, [], xs, ts, e, _) ->
      let xs = List.map (fun (x, t) -> match t with Some t -> (x, t) | None -> (x, u_next_type_var u)) xs in
      let env = List.fold (fun env (x, t) -> push_id env x t) env xs in
      let (t, ae) = infer_exp env u e None in
      let ae = AE_Bind (Lambda, [], List.map (fun (x, t) -> (x, Some t)) xs, ts, ae) in
      ret (TFun (List.map snd xs, t)) ae
  | ECast (e, tc) ->
      let (t, ae) = infer_exp env u e None in
      let ae = AE_Cast (ae, tc) in
      ret tc ae
      //REVIEW: casts across arbitrary types seem to be useful (e.g. for module friends)
      //// TODO: move this check to after inference:
      //if (is_subtype env t tc_norm || is_subtype env tc_norm t) then norm_ret tc ae
      //else err (sprintf "cannot cast between types %s and %s that do not have subtype relationship" (string_of_typ t.norm_typ) (string_of_typ tc))
  | EApply (e, ts_opt, es, _) when !fstar && is_id e && id_of_exp e = (Id "list") -> check_collection_literal e PT_List ts_opt es
  | EApply (e, ts_opt, es, _) when not !fstar && is_id e && id_of_exp e = (Id "seq") -> check_collection_literal e PT_Seq ts_opt es
  | EApply (e, ts_opt, es, _) when not !fstar && is_id e && id_of_exp e = (Id "set") -> check_collection_literal e PT_Set ts_opt es
  | EApply (e, ts_opt, es, _) ->
      let applyE () =
        let fargs = List.map (fun _ -> u_next_type_var u) es in
        let fret = u_next_type_var u in
        let (_, ae) = infer_exp env u e (Some (TFun (fargs, fret))) in
        let (arg_typs, aes) = infer_arg_typ env u (List.map2 (fun e t -> (e, Some t)) es fargs) in
        ret fret (AE_ApplyE (ae, aes))
      let applyX x f =
        if List.length f.f_args <> List.length es then err (sprintf "number of args doesn't match number of parameters, expected %i, got %i" (List.length f.f_args) (List.length es));
    //    let env = if isExtern then {env with ghost = true} else env in
        let (arg_typs, aes) = infer_arg_typ env u (List.map2 (fun e t -> (e, Some t)) es f.f_args) in
        ret f.f_ret (AE_ApplyX (x, f.f_targs, aes))
        in
      match id_of_exp_opt e with
      | Some x ->
        (
          match try_lookup_fun_decl env x with
          | None -> applyE ()
          | Some f -> applyX x (compute_fun_instance env u f ts_opt)
        )
      | None -> applyE ()
  | _ ->
      notImplemented (sprintf "not yet implemented: type checking rule for %A" e)
// infer_exp_force forces the type to a concrete type suitable for pattern matching;
// this is used to resolve overloading in some cases
and infer_exp_force (env:env) (u:unifier) (e:exp) (et:typ option):(typ * aexp) =
  try
    let (t, ae) = infer_exp env u e None in
    let t =
      match t with
      | TVar (x, _) ->
        u_unify u (Some (Set.singleton x));
        subst_typ (u.u_substs) t
      | t -> t
      in
    (normalize_type env t, ae)
  with err -> (match locs_of_exp e with [] -> raise err | loc::_ -> locErr loc err)

let tc_exp (env:env) (e:exp) (et:typ option):(typ * exp) =
  try
    let u = new_unifier env (loc_of_exp_opt e) in
    let (t, ae) = infer_exp env u e et in
    //printfn "t = %A  ae = %A  u = %A" t ae u;
    u_unify u None;
    let t = subst_typ u.u_substs t in
    let es = subst_exp env u.u_substs ae in
//    printfn "e = %A  es = %A" (Emit_vale_text.string_of_exp e) (Emit_vale_text.string_of_exp es);
//    printfn "e = %A\n  ae = %A\n  t = %A\n  es = %A" e ae t es;
    (t, es)
  with
  //| UnsupportedErr s -> printfn "%s" s; (TTuple [], e)
  | err -> (match locs_of_exp e with [] -> raise err | loc::_ -> locErr loc err)

let rec update_env_stmt (env:env) (s:stmt):env =
  match s with
  | SLoc (loc, s) -> update_env_stmt env s
  | SLabel _ | SGoto _ | SReturn | SAssume _ | SAssert _ | SCalc _ -> env
  | SVar (x, t, m, g, a, eOpt) ->
    (
      let t = match t with Some t -> t | None -> internalErr "update_env_stmt" in
      let info = match (m, g) with (Mutable, XGhost) -> Some MutableGhostLocal | _ -> None in
      push_id_with_info env x t info
    )
  | SAlias (x, y) ->
    let (t, _) = lookup_id env y in
    push_id env x t
  | SAssign (xs, e) ->
    push_lhss env xs
  | SLetUpdates _ | SBlock _ | SQuickBlock _ | SIfElse _ | SWhile _ -> env
  | SForall (xs, ts, ex, e, b) ->
    List.fold (fun env (x, t)-> let t = match t with Some t -> t | None -> internalErr "update_env_stmt" in push_id env x t) env xs
  | SExists (xs, ts, e) ->
    List.fold (fun env (x, t)-> let t = match t with Some t -> t | None -> internalErr "update_env_stmt" in push_id env x t) env xs


(*
let resolve_id env id:unit =
  match id with
  | Reserved _ -> ()
  | _ ->
    match lookup_name env id true with
    | (None, _) -> err ("Identifier not found " + (err_id id))
    | (Some r, _) -> ()
*)

// TODO: move this to emit_vale_text
let string_of_inout (io:inout):string =
  match io with
  | In -> "in"
  | Out -> "out"
  | InOut -> "inout"

let string_of_operand_typ (ot:operand_typ):string =
  match ot with
  | OT_Const -> "const"
  | OT_Name x -> string_of_id x
  | OT_State (io, x) -> string_of_inout io + " " + string_of_id x

let operand_type_includes (env:env) (xo:id) (src_ot:operand_typ):typ =
  let rec match1 (dst_ot:operand_typ):bool =
    match (src_ot, dst_ot) with
    | (OT_Const, OT_Const) -> true
    | (OT_State ((Out | InOut), xs), OT_State (In, xd)) when xs = xd -> false // somewhat confusingly, In refers to the source here
    | (OT_State (_, xs), OT_State (_, xd)) when xs = xd -> true
    | (OT_Name xs, OT_Name xd) when xs = xd -> true
    | (_, OT_Name xd) ->
        let (_, _, _, dst_ots) = lookup_operand_type env xd in
        match_many dst_ots
    | _ -> false
  and match_many (dst_ots:operand_typ list):bool =
    List.exists match1 dst_ots
    in
  let (_, t, _, dst_ots) = lookup_operand_type env xo in
  if src_ot = OT_Name xo || match_many dst_ots then t else
    err (sprintf "operand '%s' does not have operand type '%s'" (string_of_operand_typ src_ot) (err_id xo))

let rec tc_proc_operand (env:env) (u:unifier) (pf:pformal) (e:exp):aexp =
  try
    let (x, txo, storage, io, attrs) = pf in
    let check_const_operand (xo:id):aexp =
      match io with
      | In ->
          let tparam = operand_type_includes env xo OT_Const in
          let (t, ae) = infer_exp {env with inline_only = true} u e (Some tparam) in
          (AE_Op (Uop UConst, [ae]), t, None)
      | Out | InOut -> err "cannot pass constant as 'out' or 'inout' operand"
      in
    match (storage, txo) with
    | (XGhost, tparam) ->
        let (_, ae) = infer_exp env u e (Some tparam) in
        ae
    | (XInline, tparam) ->
        let (_, ae) = infer_exp {env with inline_only = true} u e (Some tparam) in
        ae
    | (XOperand, TName xo) ->
      (
        match skip_loc e with
        | EVar (x, _) ->
          (
            let (t, info) = lookup_id env x in
            match (io, info) with
            | (_, (None | Some MutableGhostLocal)) -> err "expression is not an operand"
            | (_, Some (InlineLocal | ConstGlobal)) -> check_const_operand xo
            | (_, Some (StateInfo (xx, ts))) ->
                let _ = operand_type_includes env xo (OT_State (io, xx)) in
                (AE_Exp e, t, None)
            | ((Out | InOut), Some (OperandLocal (In, _))) ->
                err "cannot pass 'in' operand as 'out' or 'inout' operand"
            | (_, Some (OperandLocal (_, TName xo_local))) ->
                let _ = operand_type_includes env xo (OT_Name xo_local) in
                (AE_Exp e, t, None)
            | (_, Some (OperandLocal (_, _))) -> internalErr (sprintf "tc_proc_operand: OperandLocal: %A %A" io info)
          )
        | EApply (e, None, es, _) when is_id e ->
          (
            let x = id_of_exp e in
            match lookup_name env x true with
            | (Some (Func_decl _), _) -> check_const_operand xo
            | (Some (OperandType_info (Some pformals, t, opr, os)), _) ->
                // TODO: we should check in/out, maybe by checking whether x_in and x_out procedures exist
                let _ = operand_type_includes env xo (OT_Name x) in
                let nes = List.length es in
                let nparams = List.length pformals in
                if nes <> nparams then err (sprintf "operand type '%s' expects %i arguments(s), found %i arguments(s)" (err_id x) nparams nes) else
                let aes = List.map2 (tc_proc_operand env u) pformals es in
                (AE_ApplyX (x, [], aes), t, None)
            | _ -> err (sprintf "cannot find function named '%s' or procedure operand_type named '%s'" (err_id x) (err_id x))
          )
        | _ -> check_const_operand xo
      )
    | (XOperand, _) -> err "expected operand as procedure argument, found expression"
    | _ -> notImplemented (sprintf "tc_proc_operand %A" pf)
  with err -> (match locs_of_exp e with [] -> raise err | loc::_ -> locErr loc err)

let assign_local (env:env) (x:id):typ =
  let (t, info) = lookup_id env x in
  match info with
  | Some MutableGhostLocal -> t
  | _ -> err (sprintf "variable '%s' must be mutable ghost to allow assignment" (err_id x))

// TODO: check that global variable names are distinct
// TODO: check that local variable names are distinct

let tc_proc_call (env:env) (loc:loc option) (p:proc_decl) (xs:lhs list) (ts_opt:typ list option) (es:exp list):stmt =
  let u = new_unifier env loc in
  let pi = compute_proc_instance env u p ts_opt in
  let nxs = List.length xs in
  let nes = List.length es in
  let nparams = List.length p.pargs in
  let nrets = List.length p.prets in
  if nes <> nparams then err (sprintf "procedure expects %i arguments(s), found %i arguments(s)" nparams nes) else
  if nxs > 0 && nxs <> nrets then err (sprintf "procedure returns %i value(s), found %i return variable(s)" nrets nxs) else
  let aes = List.map2 (tc_proc_operand env u) pi.p_args es in
  let proc_ret (lhs:lhs) (ret:pformal):lhs =
    // TODO: type inference here
    let (_, tr, _, _, _) = ret in
    let check_subtype (x:id) (tx:typ):unit =
      if not (is_subtype env tr tx) then err (sprintf "cannot assign return type '%s' to variable '%s' of type '%s'" (string_of_typ tr) (err_id x) (string_of_typ tx))
      in
    match lhs with
    | (x, None) -> check_subtype x (assign_local env x); lhs
    | (x, Some (None, Ghost)) -> (x, Some (Some tr, Ghost))
    | (x, Some (Some tx, Ghost)) -> check_subtype x tx; lhs
    | (x, Some (_, NotGhost)) -> err (sprintf "variable '%s' must be ghost" (err_id x))
  let xs = List.map2 proc_ret xs pi.p_rets in
  u_unify u None;
  let es = List.map (subst_exp env u.u_substs) aes in
  let prets = List.map (fun (_, t, _, _, _) -> t) p.prets in
  let tRet = match prets with | [] -> None | [t] -> Some t | _  -> Some (TTuple prets) in
  SAssign (xs, EApply (evar p.pname, Some pi.p_targs, es, tRet))

let rec tc_stmt (env:env) (s:stmt):stmt =
  // TODO: need typing rules for statements
  match s with
  | SLoc (loc, s) -> try SLoc (loc, tc_stmt env s) with err -> locErr loc err
  | SLabel x -> err "labels are not supported"
  | SGoto x -> err "goto statements are not supported"
  | SReturn -> s
  | SAssume e -> let (_, e) = tc_exp env e (Some tProp) in SAssume e
  | SAssert (attrs, e) -> let (_, e) = tc_exp env e (Some tProp) in SAssert (attrs, e)
  | SCalc (op, contents, e) -> 
    let contents = tc_calc_contents env contents in 
    let (_, e) = tc_exp env e None in  
    SCalc (op, contents, e)
  | SVar (x, tOpt, m, g, a, eOpt) ->
    (
      (match tOpt with | Some t -> let _ = check_type env t in () | None -> ());
      let (t, eOpt) =
        let etOpt = match eOpt with | Some e -> Some (tc_exp env e tOpt) | _ -> None in
        match (tOpt, etOpt) with
        | (None, None) -> err "variable declaration must have a type or an initial expression"
        | (None, Some (t, e)) -> (t, Some e)
        | (Some t, None) -> (t, None)
        | (Some t, Some (_, e)) -> (t, Some e)
        in
      SVar (x, Some t, m, g, a, eOpt)
    )
  | SAlias (x, y) -> s // TODO resolve_id env y; s
  | SAssign ([], EOp (Uop UReveal, [EVar (x, _)], _)) ->
      //TODO: let _ = lookup_fun env x in
      s
  | SAssign (xs, e) ->
    (
      let assign_exp () =
        let (et, ft) =
          match xs with
          | [(x, None)] -> (Some (assign_local env x), fun _ -> xs)
          | [(x, Some (None, Ghost))] -> (None, fun t -> [(x, Some (Some t, Ghost))])
          | [(x, Some (Some t, Ghost))] -> (Some t, fun _ -> xs)
          | [(x, Some (_, NotGhost))] -> err (sprintf "variable '%s' must be ghost" (err_id x))
          | [] -> (None, fun _ -> xs)
          | _::_::_ -> internalErr "assign_exp"
          in
        let (t, e) = tc_exp env e et in
        SAssign (ft t, e)
        in
      match skip_loc e with
      | EApply (e, ts_opt, es, _) when is_id e ->
        (
          let x = id_of_exp e in
          match (xs, lookup_fun_or_proc env x) with
          | (([] | [_]), (FoundFunDecl _ | FoundFunExpr _)) -> assign_exp ()
          | (_::_, (FoundFunDecl _ | FoundFunExpr _)) -> err ("Expected 0 or 1 return values from function")
          | (_, FoundProc p) -> tc_proc_call env (loc_of_exp_opt e) p xs ts_opt es
        )
      | _ -> assign_exp ()
    )
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SBlock b -> let (env, b) = tc_stmts env b in SBlock b
  | SQuickBlock (x, b) -> let (env, b) = tc_stmts env b in SQuickBlock (x, b)
  | SIfElse (g, e, b1, b2) ->
      // TODO: check ghostness specified by g (here and in other statements)
      let (t, e) = tc_exp env e (Some tBool) in
      let (_, b1) = tc_stmts env b1 in
      let (_, b2) = tc_stmts env b2 in
      SIfElse (g, e, b1, b2)
  | SWhile (e, invs, ed, b) ->
      let (t, e) = tc_exp env e (Some tBool) in
      let invs = List_mapSnd (fun e -> let (_, e) = tc_exp env e (Some tProp) in e) invs in
      let ed = mapSnd (List.map (fun e -> let (_, e) = tc_exp env e None in e)) ed in
      let (_, b) = tc_stmts env b in
      SWhile (e, invs, ed, b)
  | SForall (xs, ts, ex, e, b) ->
      // TODO: xs
      // TODO: ts
      let env1 = update_env_stmt env s in
      let (t, ex) = tc_exp env1 ex (Some tProp) in
      let (_, e) = tc_exp env1 e (Some tProp) in
      let (env, b) = tc_stmts env1 b in
      SForall (xs, ts, ex, e, b)
  | SExists (xs, ts, e) ->
      // TODO: xs
      // TODO: ts
      let env1 = update_env_stmt env s in
      let (_, e) = tc_exp env1 e (Some tProp) in
      SExists (xs, ts, e)
and tc_stmts (env:env) (ss:stmt list):(env * stmt list) =
  let (env, ss_rev) =
    List.fold
      (fun (env, l) s ->
        let (ts:stmt) = tc_stmt env s in (update_env_stmt env ts, ts::l))
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
            let (tc, e) = tc_exp env e t in
            let typ = match t with Some t -> t | None -> tc in
            let env = push_id env x typ in
            let (env, es) = tc_spec_exp env es in
            (env, (loc, SpecLet (x, t, e)) :: es)
      let (env, es) = tc_spec_exp env es in
      (env, [(loc, SpecRaw (RawSpec (r, es)))])
  | SpecRaw (Lets ls) ->
      let tc_spec_let (env:env) (loc:loc, l:lets):(env * (loc * lets)) =
        match l with
        | LetsVar (x, t, e) ->
            let (tc, e) = tc_exp env e t in
            let typ = match t with Some t -> t | None -> tc in
            let env = push_id env x typ in
            (env, (loc, LetsVar (x, Some typ, e)))
        | LetsAlias (x, y) ->
            let (t, info) = lookup_id env y in
            let env = push_id_with_info env x t info in
            (env, (loc, LetsAlias (x, y))) in
      let (env, ls) = List.fold (fun (env, lets) l -> let (env, l) = tc_spec_let env l in (env, lets @ [l])) (env,[]) ls in
      (env, [(loc, SpecRaw (Lets ls))])

let tc_specs (env:env) (specs:(loc * spec) list):(env * (loc * spec) list) =
  let (env, specs) = List_mapFoldFlip tc_spec env specs in
  (env, List.concat specs)

let push_rets (env:env) (rets:pformal list):env =
  let f s (x, t, g, io, a) =
    let info =
      match g with
      | XGhost -> Some MutableGhostLocal
      | _ -> err (sprintf "return variable '%s' must be ghost" (err_id x))
    Map.add x (Info (t, info)) s in
  {env with decls_map = List.fold f env.decls_map rets}

let push_params_without_rets (env:env) (args:pformal list) (rets:pformal list):env =
  let rec aux s l =
    match l with
    | [] -> s
    | a::q ->
      (
        let (x, t, g, io, _) = a in
        let name_info =
          match g with
          | XOperand ->
            (
              match t with
              | TName xt ->
                  let (_, tx, _, _) = lookup_operand_type env xt in
                  Info (tx, Some (OperandLocal (io, t)))
              | _ -> err (sprintf "type of operand %s must be name of an operand type" (err_id x))
            )
          | XInline -> Info (t, Some InlineLocal)
          | _ -> Info (t, None)
        let s = Map.add x name_info s in
        aux s q
      )
    in
  {env with decls_map = aux env.decls_map args}

let tc_proc (env:env) (p:proc_decl):(env * proc_decl) =
//  try
    let isRecursive = attrs_get_bool (Id "recursive") false p.pattrs in
    let env = if isRecursive then push_proc env p.pname p else env in
    let globals = env in
    let env = push_id_with_info env (Reserved "this") (TName (lookup_primitive env PT_State)) (Some MutableGhostLocal) in
    let env = push_params_without_rets env p.pargs p.prets in
    let env = push_rets env p.prets in
//    let env = {env with ghost = true}
    let (env, pspecs) = tc_specs env p.pspecs in
//    let env = {env with ghost = false}
    let (env, body) =
      match p.pbody with
      | None -> (env, None)
      | Some ss -> let (env, ss) = tc_stmts env ss in (env, Some ss)
    let pNew = {p with pbody = body; pspecs = pspecs} in
    let env = globals in
    let env = if isRecursive then env else push_proc env p.pname p in
    (env, pNew)
//  with
//  | UnsupportedErr s ->
//      //printfn "%s" s;
//      let env = push_unsupported env p.pname s in
//      (env, p)

let tc_decl (env:env) (decl:((loc * decl) * bool)):(env * ((loc * decl) * bool) list) =
  let ((loc, d), verify) = decl in
  try
    match d with
    | DType (x, ts, k, t, attrs) ->
        let env = push_typ env x ts k t attrs
        (env, [decl])
    | DOperandType (x, pformals, t, opr, ots) ->
        let env = push_name_info env x (OperandType_info (pformals, t, opr, ots)) in
        (env, [decl])
    | DVar (x, t, XAlias (AliasThread, e), _) ->
        // TODO: type check t and e
        let env = push_id env x t in
        (env, [decl])
    | DVar (x, t, XState e, _) ->
      (
        match skip_loc e with
        | EApply _ ->
            //let t = normalize_type_with_transform env t (Some StateGet) in
            let env = push_id_with_info env x t(*.norm_typ*) (Some (StateInfo (x, t(*.norm_typ*)))) in
            (env, [decl])
        | _ -> err ("declaration of state member " + (err_id x) + " must provide an expression of the form f(...args...)")
      )
    | DConst (x, t) ->
        let env = push_const env x t in
        (env, [decl])
    | DFun ({fbody = None} as f) -> // TODO: fbody = Some e
      (
        let isTypeChecked = verify && (attrs_get_bool (Id "typecheck") !do_typecheck f.fattrs) in
        let name =
          // Generate distinct names for overloaded operators
          // TODO: more overloaded operators
          match (f.fname, f.fargs) with
          | (Operator "[]", [(_, Some (TName (Id x) | (TApply (Id x, _)))); _]) -> Operator (x + "[]")
          | (Operator "[]", _) -> err "operator([]) expects two arguments (the first argument must be a named type)"
          | (Operator "[:=]", [(_, Some (TName (Id x) | (TApply (Id x, _)))); _; _]) -> Operator (x + "[:=]")
          | (Operator "[:=]", _) -> err "operator([:=]) expects three arguments (the first argument must be a named type)"
          | (Operator "?[]", [(_, Some (TName (Id x) | (TApply (Id x, _)))); _]) -> Operator (x + "?[]")
          | (Operator "?[]", _) -> err "operator(?[]) expects two arguments (the first argument must be a named type)"
          | (Operator xf, [(_, Some (TName (Id xt) | (TApply (Id xt, _)))); _])
              when xf.StartsWith(".") && xf.EndsWith(":=") -> Operator (xt + " " + xf)
          | (Operator xf, _) when xf.StartsWith(".") && xf.EndsWith(":=") ->
              err (sprintf "operator(%s :=) expects expects two arguments (the first argument must be a named type)" xf)
          | (Operator xf, [(_, Some (TName (Id xt) | (TApply (Id xt, _))))]) when xf.StartsWith(".") -> Operator (xt + " " + xf)
          | (Operator xf, [(_, Some (TTuple ts))]) when xf.StartsWith(".") -> Operator ("tuple " + string (List.length ts) + " " + xf)
          | (Operator xf, _) when xf.StartsWith(".") ->
              err (sprintf "operator(%s) expects one argument, which must be a named type" xf)
          | _ -> f.fname
        let env = push_func env name f in
        (env, [decl])
      )
    | DProc p ->
        // TODO: add ptargs to env
        let isTypeChecked = verify && (Option.isSome p.pbody) && (attrs_get_bool (Id "typecheck") !do_typecheck p.pattrs) in
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
          else if isTestShouldFail then
            (env, [])
          else
            let env = push_proc env p.pname p in (env, [p])
          in
        (env, List.map (fun p -> ((loc, DProc p), verify)) ps)
    | DUnsupported (x, msg) ->
        let env = push_unsupported env x loc msg in
        (env, [decl])
    | DPragma (ModuleName s) ->
        let env = push_include_module env s (Some None) in
        (env, [decl])
    | _ -> (env, [decl])
  with
  //| UnsupportedErr s -> printfn "%s" s; (env, [decl])
  | err -> locErr loc err

let tc_include env (inc:string * string option option * (((loc * decl) * bool) list)):env =
  let (s, b, ds) = inc in
  let env = push_include_module env s b in
  let globals = env in
  let env =
    List.fold (fun env d ->
      let (env, ds) = tc_decl env d in env)
      env
      ds
    in
  let env = globals in
  env

let tc_decls (include_modules:(string * string option option * (((loc * decl) * bool) list)) list) (ds:((loc * decl) * bool) list):((loc * decl) * bool) list =
  // Prims is included and prop is defined by default
  let env = empty_env in
  let env = push_include_module env "Prims" (Some None) in
//  let env = push_include_module env "Vale.Primitives" true in
//  let env = {env with decls_map = Map.add (Id "prop") (Type_info ([], (KType bigint.One), None)) env.decls_map} in
  let env = List.fold (fun env inc -> tc_include env inc) env include_modules in
  let (env, dss_rev) =
    List.fold (fun (env:env, l:((loc * decl) * bool) list) d ->
      let (env, ds) = tc_decl env d in (env, (List.rev ds) @ l))
      (env, [])
      ds
    in
  List.rev dss_rev
