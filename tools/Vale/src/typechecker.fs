module TypeChecker

open Ast
open Ast_util
open Parse
open Microsoft.FSharp.Math
open System.Collections.Generic
open System.IO
open System
open Microsoft.FSharp.Text.Lexing

let tvar_count = ref 0
let reset_type_vars() =
  tvar_count := 0 
let next_type_var() : typ =
  let tvar = "u" + string (!tvar_count) in
  incr tvar_count;
  TVar (Id tvar, None)

type typ_constraints = (typ * typ) list
type substitutions = Map<id, typ>

type decl_type =
  {
    targs:typ list;
    trets:typ list;
    ret_name:id option;
    specs:(loc * spec) list;
    attrs:attrs;
  }

type name_info =
| Info of typ
| Func_decl of decl_type
| Proc_decl of decl_type // second proc_decl is for raw_proc
| Type_info of (tformal list * kind * typ option)
| Name of id

type scope_mod =
| Open_module of string
| Module_abbrev of (string * string)
| Variable of (id * typ)
| Func of (id * id * decl_type)
| Proc of (id * decl_type)
| Type of (id * id * tformal list * kind * typ option)
| Const of (id * id* typ)
| Unsupported of (id * id)

type env = {
  curmodule: option<string>; (* name of the module being typechecked *)
  modules: list<string>; (* previously defined modules *)
  scope_mods: list<scope_mod>; (* a STACK of scope modifiers *)
}

let empty_env:env= {curmodule=None; modules=[]; scope_mods=[]}

(* type annotated expression *)
(* annotated with the inferred type and expected type *)
(* If these two types are not equal, insert a cast *)
type aexp =
| AELoc of loc * aexp
| AEVar of id * typ * typ 
| AEInt of bigint * typ * typ
| AEReal of string * typ * typ
| AEBitVector of int * bigint * typ
| AEBool of bool * typ * typ
| AEString of string * typ
| AEOp of op * aexp list * typ * typ
| AEApply of id * aexp list * typ list * typ list
| AEBind of bindOp * aexp list * formal list * triggers * aexp * typ * typ
| AECast of aexp * typ

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
  | Id _ -> (Id mn, Id sn)
  | Reserved _ -> (Reserved mn, Reserved sn)
  | Operator _ -> (Operator mn, Operator sn)

let lookup_name (env:env) (x:id) =
  let (mn, x) = name_of_id x in
  let find = function
    | Variable (s, t) when s=x -> Some (Info t)
    | Func (s, m, decl) when (s=x && (mn = (Id "") || m = mn)) -> Some (Func_decl decl)
    | Proc (s, decl) when s=x -> Some (Proc_decl decl)
    | Type (s, m, ts, kind, t) when (s=x && (mn = (Id "") || m = mn)) -> Some (Type_info (ts, kind, t))
    | Const (s, m, t) when (s=x && (mn = (Id "") || m = mn)) -> Some (Info t)
    | Unsupported (s, m) when (s=x && (mn = (Id "") || m = mn)) -> Some (Name s)
    | _ -> None
  let rec aux = function
    | a :: q -> 
      match (find a) with
      | Some r -> Some r
      | None -> aux q
    | [] -> 
      None
  aux env.scope_mods

let push_scope_mod env scope_mod =
 {env with scope_mods = scope_mod :: env.scope_mods}

let try_lookup_type (env:env) (x:id): (typ option * kind) option =
  match lookup_name env x with
  | Some (Type_info (ts, k, t)) -> 
    Some (t, k)
  | _ -> None

let lookup_type (env:env) (x:id): (typ option * kind) =
  match try_lookup_type env x with
  | Some info -> info
  | _ -> err ("cannot find type '" + (err_id x) + "'")

let rec normalize_type env t : typ =
  match t with 
  | TName id -> 
    match try_lookup_type env id with 
    | Some (typ, k)  ->
      match typ with | Some t -> normalize_type env t | None -> t
    | _ -> t  // ISSUE: this should be an error, but not due to args are not transformed yet
  | TApp (t, ts) -> 
    let t = normalize_type env t in
    let ts = List.map (fun t -> normalize_type env t) ts in
    TApp (t, ts) 
  | _ -> t

let base_typ env t =
  let t = match t with
  | TName (Id "Prims.int") -> TInt(NegInf, Inf)
  | TName (Id "Prims.nat") 
  | TName (Id "Prims.pos")
  | TName (Id "nat")
  | TName (Id "pos") -> TInt(Int bigint.Zero, Inf)
  | TName (Id "Words_s.nat1") -> TName (Id "bool")
  | TName (Id "Prims.bool") -> TName(Id "bool")
  // those below are due to argument not transformed yet.
  | TName (Id "reg")
  | TName (Id "opr64") 
  | TName (Id "dst_opr64") 
  | TName (Id "reg_opr64") -> TInt(NegInf, Inf)
  | TName (Id "xmm") -> TName(Id "quad32")
  | _ -> t in
  normalize_type env t in

let push_unsupported env id =
  let (mn, sn) = name_of_id id in
  push_scope_mod env (Unsupported (sn, mn))

let push_id env id t =
  let t = base_typ env t in
  push_scope_mod env (Variable (id, t))
  
let push_func env id t =
  let (mn, sn) = name_of_id id in
  push_scope_mod env (Func (sn, mn,  t))
  
let push_proc env id t =
  push_scope_mod env (Proc (id, t))

let push_typ env id ts k t =
  let (mn, sn) = name_of_id id in
  push_scope_mod env (Type (sn, mn, ts, k, t))

let push_const env id t =
  let t = base_typ env t in
  let (mn, sn) = name_of_id id in
  push_scope_mod env (Const (sn, mn, t))
   
let push_rets (env:env) (rets:pformal list):env =
  {env with scope_mods = List.fold (fun s (x, t, g, io, a) -> Variable (x, (base_typ env t)):: s) env.scope_mods rets}

let push_params_without_rets (env:env) (args:pformal list) (rets:pformal list):env =
  let arg_in_rets arg l = List.exists (fun elem -> elem = arg) l in
  let rec aux s l = 
    match l with
    | [] -> s
    | a::q ->
    let (x, t, _, _, _) = a in
    let t = base_typ env t in
    let s = if arg_in_rets a rets then s else Variable (x, t):: s in
    aux s q in
  {env with scope_mods = aux env.scope_mods args}

let push_lhss (env:env) (lhss:lhs list):env =
  let push_lhs s (x,dOpt) =
    match dOpt with 
    | Some (tOpt, _) -> 
      let t = match tOpt with Some t -> t | None -> next_type_var() in
      Variable (x, t)::s
    | None -> s
  {env with scope_mods = List.fold push_lhs env.scope_mods lhss }    
  
let push_formals (env:env) (formals:formal list): env =
  {env with scope_mods = List.fold (fun s (x, t) -> let t = match t with Some t-> t | _->next_type_var() in Variable (x, t):: s) env.scope_mods formals}

let try_lookup_id (env:env) (x:id): typ option = 
  match lookup_name env x with
  | Some (Info t) -> Some t
  | Some (Name x) -> unsupported ("unsupported '" + (err_id x) + "'")
  | _ -> None

let lookup_id (env:env) (x:id): typ = 
  match try_lookup_id env x with
  | Some t -> t
  | _ -> err ("cannot find id '" + (err_id x) + "'")

let compute_proc_typ env p =
  let args = List.map (fun (_, t, _, _, _) -> base_typ env t) p.pargs in
  let outs = List.fold (fun l (_, t, _, io, _) -> match io with | Out | InOut -> l@[(base_typ env t)] | _ -> l) [] p.pargs in
  let rets = List.map (fun (_, t, _, _, _) -> base_typ env t) p.prets in
  {targs=args; trets=outs@rets; ret_name=None; specs=p.pspecs; attrs=p.pattrs}     

let compute_func_typ env f =
  let targs = List.map (fun (id, kind, _) -> TVar (id, Some kind)) f.ftargs in
  let rec replace_typ_arg t =
    match t with
    | TName id -> 
      match List.tryFind (fun tv -> match tv with | TVar (x, _) -> id=x | _ -> false) targs with
      | Some tv -> tv
      | None -> t
    | TApp (t, ts) -> TApp (replace_typ_arg t, List.map replace_typ_arg ts)
    | TVar (_, _) -> err ("unexpected type variable in functiont type")
    | TInt (_, _) -> t
    | TList t -> TList (replace_typ_arg t)
    | TTuple ts -> TTuple (List.map replace_typ_arg ts)
    | TArrow (ts, t) -> TArrow (List.map replace_typ_arg ts, replace_typ_arg t)
  let arg_typ l t = 
    match t with 
    | TName (Id "Prims.unit") -> l
    | _ -> l@[base_typ env (replace_typ_arg t)]
  let args = List.fold (fun l (id, t) -> let t = match t with | Some t -> t | None -> next_type_var() in arg_typ l t) [] f.fargs in
  let rets = arg_typ [] f.fret in
  {targs=args; trets=rets; ret_name=f.fret_name; specs=f.fspecs; attrs=f.fattrs}     

let lookup_proc (env:env) (x:id): decl_type =
  match lookup_name env x with
  | Some (Proc_decl t) -> t
  | Some (Func_decl t) -> t
  | Some (Name x) -> unsupported ("unsupported '" + (err_id x) + "'")
  | _ -> err ("cannot find fun/proc '" + (err_id x) + "'")

let compute_bound (l1:bigint) (h1:bigint) (l2:bigint) (h2:bigint) (op:bop): (bigint * bigint) =
  let s = 
    match op with
    | BAdd -> [l1+l2; h1+l2; l1+h2; h1+h2]
    | BSub -> [l1-l2; h1-l2; l1-h2; h1-h2]
    | BMul -> [l1*l2; h1*l2; l1*h2; h1*h2]
    | BDiv when (l2 > bigint.Zero) || (h2 < bigint.Zero) -> [l1/l2; h1/l2; l1/h2; h1/h2]
    | BMod when (l2 > bigint.Zero) || (h2 < bigint.Zero) -> [bigint.Zero; (abs l2)-bigint.One; (abs h2)-bigint.One]
    | _ -> err (sprintf "cannot find new bound for '(%A, %A) %A (%A, %A)'" l1 h1 op l2 h2) in
  (List.min s, List.max s)

let unify_int_bound (t1:typ) (t2:typ) (op:bop): typ option =
  match (t1, t2) with
  | (TInt(Int l1, Int h1), TInt(Int l2, Int h2)) ->
    (* bounds are known, compute the new bound *)
    let (l,h) = compute_bound l1 h1 l2 h2 op in
    Some (TInt(Int l, Int h))
  | _ ->
    (* bounds are unknow, let the unify compute its unified type *)
    None

let neg_int_bound (t:typ): typ =
  let neg = function | Int i -> Int -i | Inf -> NegInf | NegInf -> Inf in
  match t with 
  | TInt (b1, b2) -> TInt (neg b1, neg b2)
  | _ -> err ("int type is expected with neg operator")

let bnd_equal b1 b2 =
  match (b1, b2) with 
  | (Int i1, Int i2) -> i1 = i2
  | (NegInf, NegInf) -> true
  | (Inf, Inf) -> true
  | _ -> false

let rec typ_equal env t1 t2 = 
  let t1 = base_typ env t1 in
  let t2 = base_typ env t2 in
  match (t1, t2) with
  | (TName (Id "bool"), TName(Id "Words_s.nat1")) ->
    // ISSUE: Types_s.insert_nat64 has type "nat1" while it should be "bool"
    true
  | (TName x, TName y) -> 
    let (mx, x) = name_of_id x in
    let (my, y) = name_of_id y in
    if ((x = y) && (mx = Id "" || my = Id "" || mx = my)) then true else false
  | (TApp (t1, ts1), TApp (t2, ts2)) ->
    (typ_equal env t1 t2) && List.fold2 (fun b t1 t2 -> b && typ_equal env t2 t2) true ts1 ts2
  | (TVar _, TVar _) -> false
  | (TInt (l1, h1), TInt(l2, h2)) ->
    (bnd_equal l1 l2) && (bnd_equal h1 h2)
  | (TArrow (xs, y), TArrow (us, v)) ->
    List.fold2 (fun b t1 t2 -> b&& typ_equal env t1 t2) true xs us && (typ_equal env y v)
  | _ -> false

let is_subtype env (t1:typ) (t2:typ): bool =
  match (t1, t2) with
  | (TName (Id "bool"), TName (Id "prop")) -> true
  | (TInt (Int l1, Int h1), TInt (Int l2, Int h2)) ->
    if (l2 <= l1 && h1 <= h2) then true else false
  | _ -> typ_equal env t1 t2

let isArithmeticOp op = match op with | BAdd | BSub | BMul | BDiv | BMod -> true | _ -> false
let isLogicOp op = match op with | BEquiv | BImply | BExply | BAnd | BOr -> true | _ -> false
let isIcmpOp op = match op with | BLt | BGt | BLe | BGe -> true | _ -> false

let rec infer_exp (env:env) (e:exp) (expected_typ:typ option) : (typ list * aexp * typ_constraints ) =  
  let rec infer_arg_typ env (ts, ae, s) (e:exp) (t:typ option): (typ list * aexp list * typ_constraints) = 
    let (ts1, ae1, s1) = infer_exp env e t in
    (ts@ts1, ae@[ae1], s@s1) in
  let (ts, ae, s) = 
    match e with  
    | ELoc (loc, e) -> 
      let (ts, ae, s) = infer_exp env e expected_typ in 
      (ts, AELoc (loc, ae), s)
    | EVar (Reserved "this") ->
      let t = TName (Id "state") in
      let et = match expected_typ with | None -> t | Some t -> t
      ([t], AEVar (Reserved "this", t, et), [])
    | EVar x ->
      let t = 
        match x with 
        | Id "False" -> lookup_id env (Id "Prims.l_False")
        | Id "True" -> lookup_id env (Id "Prims.l_True")
        | _ -> lookup_id env x in
      let et = match expected_typ with | None -> t | Some t -> t
      ([t], AEVar (x, t, et), [])    
    | EInt i ->
      let t = TInt (Int i, Int i) in
      let et = match expected_typ with | None -> t | Some t -> t 
      ([t], AEInt (i, t, et), [])
    | EReal r -> 
      let t = TName (Id "real") in
      let et = match expected_typ with | None -> t | Some t -> t 
      ([t], AEReal (r, t, et), [])
    | EBitVector (n, i) ->
      let t = TName (Id "bitvector") in
      ([t], AEBitVector (n, i, t), [])
    | EBool b -> 
      let t = TName (Id "bool") in
      let et = match expected_typ with | None -> t | Some t -> t 
      ([t], AEBool (b, t, et), [])
    | EString s -> 
      let t = TName (Id "string") in
      ([t], AEString (s, t), [])
    | EOp (Uop UConst, [e]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (t, ae, s) = infer_exp_one env e (Some et) in
      let ae = AEOp (Uop UConst, [ae], tv, et) in
      ([tv], ae, s@[(t, tv)])
    | EOp (Uop UNeg, [e]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t, ae, s) = infer_exp_one env e (Some et) in
      let t = neg_int_bound t in
      let ae = AEOp (Uop UNeg, [ae], tv, et) in
      ([tv], ae, s@[(t, tv)])
    | EOp (Uop UNot, [e]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t, ae, s) = infer_exp_one env e (Some et) in
      let ae = AEOp (Uop UNot, [ae], tv, et) in
      ([tv], ae, s@[(t, tv)])
    | EOp (Uop UOld, [e]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (t, ae, s) = infer_exp_one env e (Some et) in
      let ae = AEOp (Uop UOld, [ae], tv, et) in
      ([tv], ae, s@[(t, tv)])
    | EOp (Uop (UIs x), [e]) ->
      let x = Id ("uu___is_"+ (string_of_id x)) in
      let e = EApply (x, [e]) in
      let (t, ae, s) = infer_exp_one env e expected_typ in
      let ae = 
        match ae with 
        | AEApply (x, es, [t], [et]) -> AEOp (Uop (UIs x), es, t, et)
        | _ -> err ("'UIs' should be converted to 'EApply' first before typechecking") in
      ([t], ae, s)
    | EOp (Uop (UCustom op), l) ->
      let p = lookup_proc env (Operator op) in
      let e = EApply (attrs_get_id (Reserved "alias") p.attrs, l) in
      let (t, ae, s) = infer_exp_one env e expected_typ in
      let ae = 
        match ae with 
        | AEApply (x, es, [t], [et]) -> AEOp (Uop (UCustom op), es, t, et)
        | _ -> err ("'UCustom' should be converted to 'EApply' first before typechecking") in
      ([t], ae, s)
    | EOp (Uop UToOperand, _) ->
      // TODO: typing rule for UToOperand
      unsupported (sprintf "unchecked Uop UToOperand")
    | EOp (Uop op, _) ->
      err (sprintf  "unsupported Uop '%A' in typechecker" op)
    | EOp (Bop op, [e1; e2]) when isArithmeticOp op ->
      // op in {+, -, *, /, %} 
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t1, ae1, s1) = infer_exp_one env e1 (Some et) in
      let (t2, ae2, s2) = infer_exp_one env e2 (Some et) in
      let ae = AEOp (Bop op, [ae1;ae2], tv, et) in
      match unify_int_bound t1 t2 op with
      | Some t -> 
        ([tv], ae, s1@s2@[(tv, t)]) (* unify (a->a->a, t->t->tv*)
      | _ -> ([tv], ae, s1@s2@[(tv, t1); (tv, t2)]) (* unify (a->a->a, t1->t2->tv) *)
    | EOp (Bop op, [e1; e2]) when isLogicOp op ->
      // op in {&&, ||, ==>, <==, <==>}
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t1, ae1, s1) = infer_exp_one env e1 (Some et) in
      let (t2, ae2, s2) = infer_exp_one env e2 (Some et) in
      let ae = AEOp (Bop op, [ae1;ae2], tv, et) in
      ([tv], ae, s1@s2@[(tv, t1); (tv, t2)]) (* unify (a->a->a, t1->t2->tv) *)
    | EOp (Bop op, [e1; e2]) when isIcmpOp op ->
      // op in {<, > , <=, >=} and it can be chained
      match (op, skip_loc e1) with
      | (op, EOp (Bop op1, [e11; e12])) when isIcmpOp op1 ->
         // Convert (a <= b) < c into (a <= b) && (b < c)
         let e2 = EOp (Bop op, [e12; e2]) in
         let e = EOp (Bop BAnd, [e1; e2]) in
         infer_exp env e expected_typ
      | _ ->      
        let tv = next_type_var() in
        let et = match expected_typ with | None -> tv | Some t -> t in 
        let (t1, ae1, s1) = infer_exp_one env e1 (Some (TInt(NegInf, Inf))) in
        let (t2, ae2, s2) = infer_exp_one env e2 (Some (TInt(NegInf, Inf))) in
        let ae = AEOp (Bop op, [ae1;ae2], tv, et) in
        let op_typ = TArrow([TInt(NegInf, Inf); TInt(NegInf, Inf)], TName(Id "bool"))
        ([tv], ae, s1@s2@[op_typ, TArrow([t1; t2], tv)]) (* unify (int->int->bool, t1->t2->tv) *)
    | EOp (Bop op, [e1; e2]) when op = BEq || op = BNe || op = BSeq ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t1, ae1, s1) = infer_exp_one env e1 None in
      let (t2, ae2, s2) = infer_exp_one env e2 None in
      let ae = AEOp (Bop op, [ae1;ae2], tv, et) in
      let t = if op = BSeq then TName (Id "bool") else TName(Id "prop") in
      let op_typ = TArrow([t1;t1], if op = BSeq then TName (Id "bool") else TName(Id "prop"))
      ([tv], ae, s1@s2@[op_typ, TArrow([t1;t2], tv)]) (* unify (t1->t1->bool/prop, t1->t2->tv) *)
    | EOp (Bop BIn, [e1; e2]) ->
      err ("BIn not supported in TypeChecker")
    | EOp (Bop BOldAt, [e1; e2]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (t1, ae1, s1) = infer_exp_one env e1 None in
      let (t2, ae2, s2) = infer_exp_one env e2 None in
      let ae = AEOp (Bop BOldAt, [ae1;ae2], tv, et) in
      ([tv], ae, s1@s2@[(t1, TName(Id "state"));(t2, tv)])
    | EOp (Bop (BCustom op), l) ->
      let p = lookup_proc env (Operator op) in
      let e = EApply (attrs_get_id (Reserved "alias") p.attrs, l) in
      let (t, ae, s) = infer_exp_one env e expected_typ in
      let ae = 
        match ae with 
        | AEApply (x, es, [t], [et]) -> AEOp (Bop (BCustom op), es, t, et)
        | _ -> err ("'BCustom' should be converted to 'EApply' first before typechecking") in
      ([t], ae, s)
    | EOp (Subscript, [e1; e2]) ->
      let e = EApply ((Id "subscript"), [e1; e2]) in
      let (t, ae, s) = infer_exp_one env e expected_typ in
      let ae = 
        match ae with 
        | AEApply (x, es, [t], [et]) -> AEOp (Subscript, es, t, et)
        | _ -> err ("'Subscript' should be converted to 'EApply' first before typechecking") in
      ([t], ae, s)
    | EOp (Update, [e1; e2; e3]) -> 
      let e = EApply ((Id "update"), [e1; e2; e3]) in
      let (t, ae, s) = infer_exp_one env e expected_typ in
      let ae = 
        match ae with 
        | AEApply (x, es, [t], [et]) -> AEOp (Update, es, t, et)
        | _ -> err ("'Update' should be converted to 'EApply' first before typecheckings") in
      ([t], ae, s)
    | EOp (Cond, [e1; e2; e3]) -> 
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (t1, ae1, s1) = infer_exp_one env e1 None in
      let (t2, ae2, s2) = infer_exp_one env e2 (Some et) in
      let (t3, ae3, s3) = infer_exp_one env e3 (Some et) in
      let ae = AEOp (Cond, [ae1; ae2; ae3], tv, et) in
      ([tv], ae, s1@s2@s3@[(t1, TName(Id "bool")); (t2, tv);(t3, tv)])
    | EOp (FieldOp x, [e]) -> 
      let (t1, _, _) = infer_exp_one env e None in
      let (t, ae, s) = 
        match (t1,x) with 
        | (TApp(TName x,_), (Id f)) ->
          let (mn, t) = name_of_id x in
          let s = if (string_of_id mn) = "" then "" else (string_of_id mn) + "." in
          let s = s + "__proj__" + "Mk" + string_of_id t + "__item__" + f in
          let e = EApply (Id s, [e]) in
          infer_exp_one env e expected_typ
        | _ -> err (sprintf "unknown field type %A for field %s" t1 (err_id x)) in
      let ae = 
        match ae with 
        | AEApply (x, es, [t], [et]) -> AEOp (FieldOp x, es, t, et)
        | _ -> err ("'FieldOp' should be converted to 'EApply' before typechecking") in
      ([t], ae, s)
    | EOp (FieldUpdate x, [e1; e2]) -> 
      let (t1, _, _) = infer_exp_one env e1 None in
      let (t2, ae2, s2) = infer_exp_one env e2 None in
      let (t, ae, s) = 
        match (t1,x) with 
        | (TName (Id t), (Id f)) ->
          let s = "__proj" + t + "__item__" + f in
          let e = EApply (Id s, [e1]) in
          infer_exp_one env e expected_typ
        | _ -> err (sprintf "unknown field type %A for field %s" t1 (err_id x)) in
      let ae = 
        match ae with 
        | AEApply (x, es, [t], [et]) -> AEOp (FieldUpdate x, es@[ae2], t, et)
        | _ -> err ("'FieldUpdate' should be converted to 'EApply' before typechecking") in
      ([t], ae, s@s2@[(t2, t)])
    | EOp (op, es) -> 
      err (sprintf "unsupported Eop %A in typechecking" op) 
    | EApply (Id "list", es) ->
      let tv = next_type_var() in
      let arg_typ = next_type_var() in
      let (arg_typs, aes, s) = List.fold (fun (tl, ae, s) e -> infer_arg_typ env (tl, ae, s) e (Some arg_typ)) ([],[],[]) es in
      let et = TList arg_typ in
      let ae = AEApply (Id "list", aes, [tv], [et]) in
      let s = List.fold (fun l t -> l@[(t, arg_typ)]) s arg_typs in
      ([tv], ae, [(tv, et)]@s)
    | EApply (Id "tuple", es) ->
      let tv = next_type_var() in
      let (arg_typs, aes, s) = List.fold (fun (tl, ae, s) e -> infer_arg_typ env (tl, ae, s) e None) ([],[],[]) es in
      let et = TTuple arg_typs in
      let ae = AEApply (Id "tuple", aes, [tv], [et]) in
      let s = s@[(tv, et)]
      ([tv], ae, s)
    | EApply (x, es) ->
      let p = lookup_proc env x in
      if List.length p.targs <> List.length es then err (sprintf "number of args doesn't match number of parameters, expected %i, got %i" (List.length p.targs) (List.length es));         
      let param_typs = p.targs in
      let ret_typs = p.trets in
      let (arg_typs, aes, s) = List.fold2 (fun (tl, ae, s) t e -> infer_arg_typ env (tl, ae, s) e (Some t)) ([],[],[]) param_typs es in
      let ae = AEApply (x, aes, ret_typs, ret_typs) in  // TODO: need check against expected_typ
      let s = List.fold2 (fun l t1 t2 -> l@[(t1, t2)]) s param_typs arg_typs in
      (ret_typs, ae, s)
    | EApplyTyped (x, ts, es) ->
      err ("EApplyTyped not implememted in typechecking")
    | EBind (BindLet, [ex], [(x, t)], [], e) -> 
      // TODO: x is not a local variable
      // let x:t := ex in e
      let tv = next_type_var() in
      let (t1, ae1, s1) = infer_exp_one env ex t in
      let xt = match t with | Some t -> t | _ -> next_type_var() in
      let env = push_id env x xt in
      let (t2, ae2, s2) = infer_exp_one env e expected_typ in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let ae = AEBind(BindLet, [ae1], [(x,t)], [], ae2, tv, et) in
      ([tv], ae, s1@s2@[(t1,xt)]@[(tv, t2)])
    | EBind (BindLet, [ex], xs, [], e) ->
      // TODO: x1, x2 ... are distinct and not local variables
      // let (x1:t1, x2:t2...) := ex in e
      let tv = next_type_var() in
      let (ts, ae1, s1) = infer_exp env ex None in
      let (t2, ae2, s2) = infer_exp_one env e expected_typ in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let ae = AEBind(BindLet, [ae1], xs, [], ae2, tv, et) in
      if (List.length ts <> List.length xs) then err (sprintf "BindLet type mismatch");
      let s = List.fold2 (fun l et (x, t) -> let t = match t with | Some t -> t | _ -> next_type_var() in l@[(t, et)]) [] ts xs in
      ([tv], ae, s1@s2@s@[(tv, t2)])
    | EBind (b, [], fs, ts, e) when b=Forall || b=Exists ->
      // fs list of formals, that are distinct and are not local variables
      // ts: triggers
      // e: prop
      let env = List.fold(fun env (x, t) -> let t = match t with Some t -> t | None -> next_type_var() in push_id env x t) env fs in
      let (t, ae, s) = infer_exp_one env e expected_typ in
      let ae = AEBind(b, [], fs, ts, ae, t, TName(Id "prop")) in
      ([t], ae, s@[(t, TName (Id "prop"))])
    | EBind (Lambda, [], xs, ts, e) ->
      let tv = next_type_var() in
      let (t, ae, s) = infer_exp_one env e expected_typ in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let ae = AEBind(Lambda, [], xs, ts, ae, t, et) in
      ([tv], ae, s@[(tv, t)])
    | ECast (e, tc) -> 
      let (t, ae, s) = infer_exp_one env e None in
      let ae = AECast (ae, tc) in
      if (is_subtype env t tc || is_subtype env tc t) then ([tc], ae, s)
      else err (sprintf "cannot cast between types %A and %A that do not have subtype relationship" t tc)
    | _ -> err (sprintf "missing typechecker for exp %A" e) in
  let ts = List.map (fun t-> base_typ env t) ts in
  (ts, ae, s)
and infer_exp_one (env:env) (e:exp) (et:typ option) : (typ * aexp * typ_constraints ) = 
  match infer_exp env e et with
  | ([t], ae, s) -> (t, ae, s)
  | (ts, _, _) -> err (sprintf "%A can have only one inferred type, got %i" e (List.length ts))

let kind_equal k1 k2 =
  match (k1, k2) with
  | (KType i1, KType i2) -> i1=i2 

let rec resolve_type env t:kind =
  match t with 
  | TName id -> let (t, k) = lookup_type env id in k
  | TApp (t, ts) -> resolve_type env t
  | TArrow (ts, t) -> err ("not implemented")
  | TInt(_, _) -> KType bigint.Zero
  | TVar(_, Some k) -> k
  | _ -> err (sprintf "cannot find the kind of the type '%A'" t)
and resolve_types env ts = List.map (resolve_type env) ts;

let rec string_of_type t =
  let rec string_of_types ts =
    match ts with
    | [] -> ""
    | [t] -> string_of_type t
    | hd::tl -> (string_of_type hd) + "," + (string_of_types tl) in
  let str_of_bnd b =
    match b with
    | Int i -> string i
    | NegInf -> "-inf"
    | Inf -> "inf"
  match t with
  | TName x -> err_id x
  | TApp (t, ts) -> string_of_type t + "(" + string_of_types ts + ")"
  | TVar (x, k) -> "uv" + err_id x 
  | TInt (b1, b2) -> "int(" + str_of_bnd b1 + "," + str_of_bnd b2 + ")"
  | TList t -> "list(" + string_of_type t + ")"
  | TTuple ts -> "tuple(" + string_of_types ts + ")"
  | TArrow (ts, t) -> "(" + string_of_types ts + ")" + "->" + string_of_type t


let match_kind env (t:typ) (k:kind option) =
  match k with
  | Some k ->
    match t with
    | TVar (_, None) -> true
    | _ -> 
      kind_equal (resolve_type env t) k
  | None -> true

(* substitute all occurrences of x in t with s *)
let rec subst env (x:id) (s:typ) (t:typ): (typ * bool) =
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
  | TList t -> let (t, b) = subst env x s t in ((TList t), b)
  | TTuple ts -> let (ts, b) = subst_typs env x s ts in ((TTuple ts), b)
  | _ -> (t, false)
and subst_typs env (x:id) (s:typ) (ts:typ list): (typ list * bool) =
  List.fold (fun (rs, b) t -> let (t, b1) = subst env x s t in (rs@[t], b1 || b)) ([], false) ts
 
let substitute env (m:substitutions) (t:typ): typ =
  let s = Map.toList m in
  let changed = true in
  let rec aux t b = 
    if b = true then  
      let (t, b) = List.foldBack (fun (x, s) (t, b) -> let (t, b1) = subst env x s t in (t, b||b1)) s (t, false) in
      aux t b
    else t in
  aux t true

let rec occurs (x : id) (t : typ) : bool =
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

let bind (m:substitutions) (x:id) (t:typ): substitutions =
  match t with
  | TVar (y, k) -> if (x=y) then m else Map.add x t m
  | _ -> if occurs x t then err ("circular type constraint" + err_id x + " " + string_of_type t) else Map.add x t m

let unify_lower_bound l1 l2 =
  match (l1, l2) with 
  | (Int i1, Int i2) -> if i1 < i2 then Int i2 else Int i2
  | (NegInf, _) | (_, NegInf) -> NegInf
  | _ -> err (sprintf "cannot unify integer lower bound %A %A" l1 l2)

let unify_upper_bound l1 l2 =
  match (l1, l2) with 
  | (Int i1, Int i2) -> if i1 > i2 then Int i2 else Int i2
  | (Inf, _) | (_, Inf) -> Inf
  | _ -> err (sprintf "cannot unify integer upper bound %A %A" l1 l2)

let bind_typ (m:substitutions) (s:typ) (t:typ):substitutions =
  match s with
  | TVar (x, _) -> bind m x t
  | _ -> m

let rec unify_one env (m:substitutions) (s:typ) (t:typ):substitutions =
  let t1 = base_typ env (substitute env m s) in
  let t2 = base_typ env (substitute env m t) in
  match (t1, t2) with
  | (TVar (x,_), _) -> bind m x t2
  | (_, TVar (x,_)) -> bind m x t1
  | (TInt (l1, h1), TInt (l2, h2)) -> 
    let u = TInt(unify_lower_bound l1 l2, unify_upper_bound h1 h2) in
    let m = bind_typ m s u in bind_typ m t u
  | (TArrow (xs, y), TArrow (us, v)) -> 
    let tc = List.fold2 (fun l t1 t2 -> l@[(t1, t2)]) [] xs us in
    unify env m (tc@[(y, v)])
  | (TApp (x, ys), TApp (u, vs)) -> 
    let tc = List.fold2 (fun (l:typ_constraints) t1 t2 -> l@[(t1, t2)]) [] ys vs in
    unify env m ([(x, u)]@tc)
  | (TName (Id "bool"), TName (Id "prop")) 
  | (TName (Id "prop"), TName (Id "bool")) -> 
    let u = TName (Id "prop") in
    let m = bind_typ m s u in bind_typ m t u
  | (TName (Id "bool"), TName(Id "Words_s.nat1")) ->
    // ISSUE: Types_s.insert_nat64 has type "nat1" while it should be "bool"
    m
  | (TName (Id "X64.Vale.Decls_i.va_state"), TName (Id "state")) 
  | (TName (Id "X64.Vale.Decls_i.va_operand"), TName (Id "X64.Machine_s.operand"))
  | (TName (Id "shift_amt64"), TInt(_,_)) 
  | (TName (Id "pos"), TInt(_,_)) ->
    // ISSUE:
    m
  | (TName x, TName y) -> 
    let (my, x) = name_of_id x in
    let (mx, y) = name_of_id y in
    if (x=y && (mx = (Id "") || my = (Id "") || mx = my)) then m
    else err ("cannot unify type \"" + string_of_type t1 + "\" and \"" + string_of_type t2 + "\"")
  | _ -> err ("cannot unify type \"" + string_of_type t1 + "\" and \"" + string_of_type t2 + "\"")

and unify env (m:substitutions) (tc:typ_constraints):substitutions =
  match tc with
  | [] -> m
  | (x, y) :: t ->
    let m = unify_one env m x y in
    unify env m t in

let insert_cast (e:exp) (t:typ) (et:typ) : exp =
  // cast from type 't' to 'et'
  // TODO: check the cast is legal
  ECast (e, et)

let rec subst_exp env (s:substitutions) (e:aexp) : exp =
  match e with
  | AELoc (loc, ae) -> ELoc (loc, subst_exp env s ae)
  | AEVar (x, t, et) ->
    let t = substitute env s t in 
    let et = substitute env s et in
    let e = EVar x in
    if (typ_equal env t et) then e else insert_cast e t et
  | AEInt (i, t, et) ->
    let t = substitute env s t in 
    let et = substitute env s t in
    let e = EInt i in
    if (typ_equal env t et) then e else insert_cast e t et
  | AEReal (r, t, et) -> 
    let t = substitute env s t in 
    let et = substitute env s et in
    let e = EReal r in 
    if (typ_equal env t et) then e else insert_cast e t et
  | AEBitVector (n, i, t) -> EBitVector (n, i)
  | AEBool (b, t, et) -> 
    let et = substitute env s t in
    let e = EBool b in 
    if (typ_equal env t et) then e else insert_cast e t et
  | AEString (s, t) -> EString s
  | AEOp (op, aes, t, et) ->
    let es = List.map (fun ae -> subst_exp env s ae) aes in
    let t = substitute env s t in 
    let et = substitute env s t in
    let op = 
      match op with 
      | Bop p -> 
        if isArithmeticOp p then
          // make sure t is TInt
          match t with 
          | TInt (_, _) -> op 
          // TODO: type still unknown due to unsupported types
          | TVar (_, _) -> unsupported (sprintf "unknown type")
          | _ -> err (sprintf "%A expected int type, got %A" op t)
        else if isLogicOp p then
          // make sure t is bool or prop, if t is prop, swap in "/\" "\/" for "&&" "||"
          match t with 
          | TName (Id "bool") -> op
          | TName (Id "prop") -> 
            match p with | BAnd -> Bop BLand | BOr -> Bop BLor | _-> op
          | _ -> err (sprintf "%A expected bool/prop type" op)
        else op
      | Uop UNot ->
        match t with
        | TName (Id "bool") 
        | TName (Id "prop") -> op
        | _ -> err (sprintf "Uop UNot expected bool type, got %A" t)
      | _ -> op
    let e = EOp (op, es) in
    if (typ_equal env t et) then e else insert_cast e t et
  | AEApply (Id "list", aes, ts, ets) ->
    let es = List.map (fun ae -> subst_exp env s ae) aes  in
    let t = (List.map (fun t -> substitute env s t) ts).Head in 
    let et = (List.map (fun t -> substitute env s t) ets).Head in
    let e = EApply (Id "list", es) in
    match (t, et) with
    | (TList x, TList y) -> 
      if typ_equal env x y then
        if (kind_equal (resolve_type env x) (KType bigint.Zero)) then e 
        else err ("Only 'Type0' is allowed in list")
      else 
        err (sprintf "inferred list type %s does not match expected list type %s" (string_of_type t) (string_of_type et))
    | _ -> err (sprintf "list type %A expected but got %A" (string_of_type et) (string_of_type t))
  | AEApply (Id "tuple", aes, ts, ets) ->
    let es = List.map (fun ae -> subst_exp env s ae) aes  in
    let t = (List.map (fun t -> substitute env s t) ts).Head in 
    let et = (List.map (fun t -> substitute env s t) ets).Head in
    let e = EApply (Id "tuple", es) in
    match (t, et) with
    | (TTuple xs, TTuple ys) -> 
      List.iter2 (fun t1 t2 -> if (not (typ_equal env t1 t2)) then err (sprintf "inferred tuple type %s does not match expected tuple type %s" (string_of_type et) (string_of_type t))) xs ys;
      List.iter (fun t -> if (not (kind_equal (resolve_type env t) (KType bigint.Zero))) then err "Only 'Type0' is allowed in tuple") xs;
      e
    | _ -> err (sprintf "tuple type %s expected but got %s" (string_of_type et) (string_of_type t))734
  | AEApply (x, aes, ts, ets) ->
    let es = List.map (fun ae -> subst_exp env s ae) aes  in
    let t = List.map (fun t -> substitute env s t) ts in 
    let et = List.map (fun t -> substitute env s t) ets in
    let e = EApply (x, es) in
    let equal = List.fold2 (fun b t1 t2 -> b&&typ_equal env t1 t2) true t et
    if equal then e else
      if(List.length t <> 1) then err ("cast for more than one return types not implemented");
      else insert_cast e t.Head et.Head
  | AEBind (bOp, aes, xs, ts, ae, t, et) ->
    let es = List.map (fun ae -> subst_exp env s ae) aes  in
    let t = substitute env s t in 
    let et = substitute env s t in
    let e = subst_exp env s ae in
    let e = EBind(bOp, es, xs, ts, e) in
    if (typ_equal env t et) then e else insert_cast e t et
  | AECast (ae, t) ->
    ECast((subst_exp env s ae), t)

let tc_exp (env:env) (e:exp) (et: typ option): (typ list * exp) = 
  try
    let (ts, ae, cl) = infer_exp env e et in
    let s = unify env Map.empty cl in
    let ts = List.map (fun t-> substitute env s t) ts in
    let es = subst_exp env s ae in
    (ts, es)
  with
    | UnsupportedErr s -> printfn "%s" s; ([], e)
    | err -> (match locs_of_exp e with [] -> raise err | loc::_ -> raise (LocErr (loc, err)))

let rec update_env_stmt (env:env) (s:stmt): env =
  match s with
  | SLoc (loc, s) -> update_env_stmt env s
  | SLabel _ | SGoto _ | SReturn | SAssume _ | SAssert _ | SCalc _ -> env
  | SVar (x, t, m, g, a, eOpt) ->
    (
      let t = match t with Some t -> t | None -> next_type_var() in
      push_id env x t
    )
  | SAlias (x, y) ->
    let t = lookup_id env y in
    push_id env x t
  | SAssign (xs, e) ->
    push_lhss env xs
  | SLetUpdates _ | SBlock _ | SQuickBlock _ | SIfElse _ | SWhile _ -> env
  | SForall (xs, ts, ex, e, b) ->
    List.fold (fun env (x, t)-> let t = match t with Some t -> t | None -> next_type_var() in push_id env x t) env xs 
  | SExists (xs, ts, e) -> 
    List.fold (fun env (x, t)-> let t = match t with Some t -> t | None -> next_type_var() in push_id env x t) env xs 
  
      
let resolve_id env id:unit =
  match id with
  | Reserved _ -> ()
  | _ ->
    match lookup_name env id with
    | None -> err ("Identifier not found " + (err_id id))
    | Some r -> ()

let rec tc_stmt (env:env) (s:stmt):stmt =
  match s with
  | SLoc (loc, s) -> SLoc (loc, tc_stmt env s)
  | SLabel x -> resolve_id env x; s
  | SGoto x -> resolve_id env x; s
  | SReturn -> s
  | SAssume e -> let (t, e) = tc_exp env e None in SAssume e
  | SAssert (attrs, e) -> let (t, e) = tc_exp env e None in SAssert (attrs, e)
  | SCalc (oop, contents) -> SCalc (oop, tc_calc_contents env contents)
  | SVar (x, t, m, g, a, eOpt) -> 
    // TODO: insert cast if 't' and 'eOpt' type do not match
    let kind = match t with | Some t -> Some (resolve_type env t) | None -> None
    let eOpt = match eOpt with | Some e -> let (t, e) = tc_exp env e t in Some e | _ -> None in
    SVar (x, t, m, g, a, eOpt)
  | SAlias (x, y) ->  resolve_id env y; s
  | SAssign (xs, e) -> 
    let et = 
      match xs with
      | [(x, Some (Some t, _))] -> Some t // TODO: check if the type match or a cast is needed
      | [(x, _)] -> try_lookup_id env x
      | _ -> None in 
    let (t, e) = tc_exp env e et in SAssign (xs, e)
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SBlock b -> let (env, b) = tc_stmts env b in SBlock b
  | SQuickBlock (x, b) -> let (env, b) = tc_stmts env b in SQuickBlock (x, b)
  | SIfElse (g, e, b1, b2) -> 
    let et = TName (Id "bool") in 
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
    // TODO: check formals and triggers?
    let (t, ex) = tc_exp env1 ex None in
    let (t, e) = tc_exp env1 e None in
    let (env, b) = tc_stmts env1 b in
    SForall (xs, ts, ex, e, b)
  | SExists (xs, ts, e) ->
    let env1 = update_env_stmt env s in
    // TODO: check formals and triggers?
    let (t, e) = tc_exp env1 e None in
    SExists (xs, ts, e)
and tc_stmts (env:env) (ss:stmt list):(env*stmt list) = List.fold (fun (env, l) s -> let (ts:stmt) = tc_stmt env s in (update_env_stmt env s, l@[ts])) (env, []) ss
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
    let rec tc_spec_exp (env:env) (es:(loc * spec_exp) list) : (env * (loc * spec_exp) list) = 
      match es with
      | [] -> (env, [])
      | (loc, SpecExp e)::es -> 
        let (t, e) = tc_exp env e None in
        let (env, es) = tc_spec_exp env es in
        (env, (loc, SpecExp e) :: es)
      | (loc, SpecLet (x, t, e))::es ->
        let typ = match t with Some t -> t | None -> next_type_var() in
        let env = push_id env x typ in
        let (tc, e) = tc_exp env e t in
        let (env, es) = tc_spec_exp env es in
        (env, (loc, SpecLet (x, t, e)) :: es)
    let (env, es) = tc_spec_exp env es in
    (env, [(loc, SpecRaw (RawSpec (r, es)))])
  | SpecRaw (Lets ls) -> 
    let tc_spec_let (env: env) (loc:loc, l:lets) : (env * (loc * lets)) =
      match l with
      | LetsVar (x, t, e) -> 
        let typ = match t with Some t -> t | None -> next_type_var() in
        let env = push_id env x typ in
        let (tc, e) = tc_exp env e t in (env, (loc,  LetsVar (x, t, e)))
      | LetsAlias (x, y) ->
        let t = lookup_id env y in
        let env = push_id env x t in
        (env, (loc, LetsAlias (x, y))) in
    let (env, ls) = List.fold (fun (env, lets) l -> let (env, l) = tc_spec_let env l in (env, lets@[l])) (env,[]) ls in
    (env, [(loc, SpecRaw (Lets ls))])

let tc_specs (env:env) (specs:(loc * spec) list):(env * (loc * spec) list) =
  let (env, specs) = List_mapFoldFlip tc_spec env specs in
  (env, List.concat specs)

let tc_proc (env:env) (p:proc_decl): (env*proc_decl) =
  let isRecursive = attrs_get_bool (Id "recursive") false p.pattrs in
  let ptyp = compute_proc_typ env p in
  let env = if isRecursive then push_proc env p.pname ptyp else env in
  let globals = ref env.scope_mods in 
  let env = push_params_without_rets env p.pargs p.prets in
  let env = push_rets env p.prets in
  let (env, pspecs) = tc_specs env p.pspecs in
  let (env, body) = 
    match p.pbody with
    | None -> (env, None)
    | Some ss -> let (env, ss) = tc_stmts env ss in (env, Some ss)
  let pNew = {p with pbody = body; pspecs = pspecs} in
  let env = {env with scope_mods = !globals } in
  let env = if isRecursive then env else push_proc env p.pname ptyp in
  (env, pNew)

let tc_decl (env:env) (decl:((loc * decl) * bool)) : env * ((loc * decl) * bool) =
  let ((l,d),b) = decl in
  match d with
  | DType (x, ts, k, t) ->
    let env = push_typ env x ts k t
    (env, decl)
  | DVar (x, t, XAlias (AliasThread, e), _) ->
    // TODO: type check t and e
    let env = push_id env x t in
    (env, decl)
  | DVar (x, t, XState e, _) ->
    ( 
      match skip_loc e with
      | EApply (Id id, es) ->
          let env = push_id env x t in
          (env, decl)
      | _ -> err ("declaration of state member " + (err_id x) + " must provide an expression of the form f(...args...)")
    )
  | DConst (x, t) ->
    let env = push_const env x t in
    (env, decl)
  | DFun ({fbody = None} as f) ->
    let ftyp = compute_func_typ env f
    let env = push_func env f.fname ftyp in
    (env, decl)
  | DProc p ->
    let isTypeChecked = attrs_get_bool (Id "typecheck") false p.pattrs in
    let (env,p) = if isTypeChecked then tc_proc env p else (env, p) in 
    (env, ((l, DProc(p)), b))
  | DUnsupported x ->
    let env = push_unsupported env x in
    (env, decl)
  | _ -> (env, decl)

let tc_decls (ds:((loc * decl) * bool) list) : ((loc * decl) * bool) list = 
  let (env,dss) = List.fold (fun (env:env,l:((loc * decl) * bool) list) d -> let (env, d) = tc_decl env d in (env, l@[d])) (empty_env,[]) ds in
  dss