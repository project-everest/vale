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
  TVar (Id tvar)

type typ_constraints = (typ * typ) list
type substitutions = Map<id, typ>

type name_info =
| Info of typ * id_info
| Func_decl of fun_decl
| Proc_decl of (proc_decl * proc_decl option) // second proc_decl is for raw_proc
| Name of string

type scope_mod =
| Open_module of string
| Module_abbrev of (string * string)
| Local of (id * typ * id_info)
| Func of (id * fun_decl)
| Proc of (id * proc_decl * proc_decl option)
| Symbol of string

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
| AEReal of string * typ
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
  aux "" es in

let lookup_name (env:env) (x:id) (nameOnly:bool) =
  let (mn, sn) = name_of_id x in
  let find = function
    | Local (s, t, info) when s=x -> Some (Info (t, info))
    | Func (s, decl) when s=x -> Some (Func_decl decl)
    | Proc (s, decl, raw_decl) when s=x -> Some (Proc_decl (decl,raw_decl))
    | Symbol s when (mn = "" && sn = s) -> Some (Name s)
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

let base_typ t =
  match t with 
  | TName (Id "int") -> TInt(NegInf, Inf)
  | TName (Id "unit") -> TInt (Int bigint.Zero, Inf)
  | TName (Id "nat") -> TInt(Int bigint.Zero, Inf)
  | _ -> t

let push_id env id t info =
  let t = base_typ t in
  push_scope_mod env (Local (id, t, info))
  
let push_func env id func =
  push_scope_mod env (Func (id, func))
  
let push_proc env id proc raw_proc =
  push_scope_mod env (Proc (id, proc, raw_proc))

let param_info isRet (x, t, g, io, a) =
  match g with
  | (XAlias (AliasThread, e)) -> ThreadLocal {local_in_param = (io = In && (not isRet)); local_exp = e; local_typ = Some t}
  | (XAlias (AliasLocal, e)) -> ProcLocal {local_in_param = (io = In && (not isRet)); local_exp = e; local_typ = Some t}
  | XInline -> InlineLocal (Some t)
  | XOperand -> OperandLocal (io, t)
  | XPhysical | XState _ -> err ("variable must be declared ghost, operand, {:local ...}, or {:register ...} " + (err_id x))
  | XGhost -> GhostLocal ((if isRet then Mutable else Immutable), Some t)
    
let push_rets (env:env) (rets:pformal list):env =
  {env with scope_mods = List.fold (fun s (x, t, g, io, a) -> Local(x, t, (param_info true (x, t, g, io, a))):: s) env.scope_mods rets}

let push_params_without_rets (env:env) (args:pformal list) (rets:pformal list):env =
  let arg_in_rets arg l = List.exists (fun elem -> elem = arg) l in
  let rec aux s l = 
    match l with
    | [] -> s
    | a::q ->
    let (x, t, _, _, _) = a in
    let t = base_typ t in
    let s = if arg_in_rets a rets then s else Local(x, t, (param_info false a)):: s in
    aux s q in
  {env with scope_mods = aux env.scope_mods args}

let push_lhss (env:env) (lhss:lhs list):env =
  let push_lhs s (x,dOpt) =
    match dOpt with 
    | Some (tOpt, _) -> 
      let t = match tOpt with Some t -> t | None -> next_type_var() in
      Local(x, t, (GhostLocal (Mutable, Some t)))::s
    | None -> s
  {env with scope_mods = List.fold push_lhs env.scope_mods lhss }    
  
let push_formals (env:env) (formals:formal list): env =
  {env with scope_mods = List.fold (fun s (x, t) -> let t = match t with Some t-> t | _->next_type_var() in Local(x, t, (GhostLocal (Immutable, Some t))):: s) env.scope_mods formals}

let lookup_id (env:env) (x:id): (typ * id_info) = 
  match lookup_name env x false with
  | Some (Info (t, info)) -> (t, info)
  | _ -> err ("cannot find id '" + (err_id x) + "'")

let lookup_proc (env:env) (x:id): proc_decl =
  match lookup_name env x false with
  | Some (Proc_decl (proc_decl, _)) -> (proc_decl)
  | _ -> err ("cannot find proc '" + (err_id x) + "'")

let compute_bound (l1:bigint) (h1:bigint) (l2:bigint) (h2:bigint) (op:bop): (bigint * bigint) =
  let s = 
    match op with
    | BAdd -> [l1+l2; h1+l2; l1+h2; h1+h2]
    | BSub -> [l1-l2; h1-l2; l1-h2; h1-h2]
    | BMul -> [l1*l2; h1*l2; l1*h2; h1*h2]
    | BDiv when (l2 > bigint.Zero) || (h2 < bigint.Zero) -> [l1/l2; h1/l2; l1/h2; h1/h2]
    | BMod when (l2 > bigint.Zero) || (h2 < bigint.Zero) -> [bigint.Zero; (abs l2)-bigint.One; (abs h2)-bigint.One]
    | _ -> err (sprintf "cannot find new bound for '(%A, %A) %A (%A, %A)" l1 h1 op l2 h2) in
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
  | _ -> err ("expect int type")

let is_subtype (t1:typ) (t2:typ): bool =
  err ("not implemented")

let isArithmeticOp op = match op with | BAdd | BSub | BMul | BDiv | BMod -> true | _ -> false
let isLogicOp op = match op with | BEquiv | BImply | BExply | BAnd | BOr -> true | _ -> false
let isIcmpOp op = match op with | BLt | BGt | BLe | BGe -> true | _ -> false

let rec infer_exp (env:env) (e:exp) (expected_typ:typ option) : (typ * aexp * typ_constraints ) =  
  let (t, ae, s) = 
    match e with  
    | ELoc (loc, e) -> 
      let (t, ae, s) = infer_exp env e expected_typ in 
      (t, AELoc (loc, ae), s)
    | EVar (Reserved "this") ->
      let t = TName (Id "state") in
      let et = match expected_typ with | None -> t | Some t -> t
      (t, AEVar (Reserved "this", t, et), [])
    | EVar x -> 
      let (t,_) = lookup_id env x in
      let et = match expected_typ with | None -> t | Some t -> t
      (t, AEVar (x, t, et), [])    
    | EInt i ->
      let t = TInt (Int i, Int i) in
      let et = match expected_typ with | None -> t | Some t -> t 
      (t, AEInt (i, t, et), [])
    | EReal r -> 
      let t = TName (Id "Real") in
      (t, AEReal (r, t), [])
    | EBitVector (n, i) ->
      let t = TName (Id "Bitvector") in
      (t, AEBitVector (n, i, t), [])
    | EBool b -> 
      let t = TName (Id "Bool") in
      let et = match expected_typ with | None -> t | Some t -> t 
      (t, AEBool (b, t, et), [])
    | EString s -> 
      let t = TName (Id "String") in
      (t, AEString (s, t), [])
    | EOp (Uop UConst, [e]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (t, ae, s) = infer_exp env e (Some et) in
      let ae = AEOp (Uop UConst, [ae], tv, et) in
      (tv, ae, s@[(t, tv)])
    | EOp (Uop UNeg, [e]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t, ae, s) = infer_exp env e (Some et) in
      let t = neg_int_bound t in
      let ae = AEOp (Uop UNeg, [ae], tv, et) in
      (tv, ae, s@[(t, tv)])
    | EOp (Uop UOld, [e]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (t, ae, s) = infer_exp env e (Some et) in
      let ae = AEOp (Uop UOld, [ae], tv, et) in
      (tv, ae, s@[(t, tv)])
    | EOp (Bop op, [e1; e2]) when isArithmeticOp op ->
      // op in {+, -, *, /, %} 
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t1, ae1, s1) = infer_exp env e1 (Some et) in
      let (t2, ae2, s2) = infer_exp env e2 (Some et) in
      let ae = AEOp (Bop op, [ae1;ae2], tv, et) in
      match unify_int_bound t1 t2 op with
      | Some t -> 
        (tv, ae, s1@s2@[(tv, t)]) (* unify (a->a->a, t->t->tv*)
      | _ -> (tv, ae, s1@s2@[(tv, t1); (tv, t2)]) (* unify (a->a->a, t1->t2->tv) *)
    | EOp (Bop op, [e1; e2]) when isLogicOp op ->
      // op in {&&, ||, ==>, <==, <==>}
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t1, ae1, s1) = infer_exp env e1 (Some et) in
      let (t2, ae2, s2) = infer_exp env e2 (Some et) in
      let ae = AEOp (Bop op, [ae1;ae2], tv, et) in
      (tv, ae, s1@s2@[(tv, t1); (tv, t2)]) (* unify (a->a->a, t1->t2->tv) *)
    | EOp (Bop op, [e1; e2]) when isIcmpOp op ->
      // op in {<, > , <=, >=}
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t1, ae1, s1) = infer_exp env e1 (Some (TInt(NegInf, Inf))) in
      let (t2, ae2, s2) = infer_exp env e2 (Some (TInt(NegInf, Inf))) in
      let ae = AEOp (Bop op, [ae1;ae2], tv, et) in
      let op_typ = TArrow([TInt(NegInf, Inf); TInt(NegInf, Inf)], TName(Id "bool"))
      (tv, ae, s1@s2@[op_typ, TArrow([t1; t2], tv)]) (* unify (int->int->bool, t1->t2->tv) *)
    | EOp (Bop op, [e1; e2]) when op = BEq || op = BNe || op = BSeq ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in 
      let (t1, ae1, s1) = infer_exp env e1 None in
      let (t2, ae2, s2) = infer_exp env e2 None in
      let ae = AEOp (Bop op, [ae1;ae2], tv, et) in
      let op_typ = TArrow([t1;t1], if op = BSeq then TName (Id "bool") else TName(Id "prop"))
      (tv, ae, s1@s2@[op_typ, TArrow([t1;t2], tv)]) (* unify (t1->t1->bool/prop, t1->t2->tv) *)
    | EOp (Bop BIn, [e1; e2]) ->
      err ("BIn not supported in TypeChecker")
    | EOp (Bop BOldAt, [e1; e2]) ->
      let tv = next_type_var() in
      let et = match expected_typ with | None -> tv | Some t -> t in
      let (t1, ae1, s1) = infer_exp env e1 None in
      let (t2, ae2, s2) = infer_exp env e2 None in
      let ae = AEOp (Bop BOldAt, [ae1;ae2], tv, et) in
      (tv, ae, s1@s2@[(t1, TName(Id "state"));(t2, tv)])
    | EOp (Bop (BCustom op), l) ->
      err ("missing typing rule for BCustom")
    | EOp (op, es) -> 
      err ("not implemented")
    | EApply (x, es) ->
      let p = lookup_proc env x in
      if List.length p.pargs <> List.length es then err ("number of args doesn't match number of parameters");         
      let param_typs = List.map (fun (_, t, _, _, _) -> base_typ t) p.pargs in
      let (ret_typs, tvs) = List.fold (fun (l, s) (_, t, _, _, _) -> (l@[base_typ t], s@[next_type_var()])) ([],[]) p.prets in
      let rec infer_arg_typ env (tl, ae, s) t e : (typ list * aexp list * typ_constraints) = 
        let (t1, ae1, s1) = infer_exp env e (Some t) in
        (tl@[t1], ae@[ae1], s@s1)
      let (arg_typs, aes, s) = List.fold2 (fun (tl, ae, s) t e -> infer_arg_typ env (tl, ae, s) t e) ([],[],[]) param_typs es in
      let ae = AEApply (x, aes, tvs, ret_typs) in
      let s = List.fold2 (fun l t1 t2 -> l@[(t1, t2)]) s param_typs arg_typs in
      let s = List.fold2 (fun l t1 t2 -> l@[(t1, t2)]) s ret_typs tvs in
      if (List.length tvs <> 1) then err ("more than 1 function return types, not implemented")
      else (tvs.Head, ae, s)
    | EBind (b, es, fs, ts, e) -> 
      err ("infer for EBind not implemented")
    | ECast (e, tc) -> 
      let (t, ae, s) = infer_exp env e None in
      let ae = AECast (ae, tc) in
      if (is_subtype t tc || is_subtype tc t) then (tc, ae, s)
      else err ("cast between types that does not have subtype relationship")
  (base_typ t, ae, s)

(* substitute all occurrences of x in t with s *)
let rec subst (x:id) (s:typ) (t:typ): typ =
  match t with
  | TVar y -> if x = y then s else t
  | TApp (t, ts) -> TApp (subst x s t, subst_typs x s ts)
  | TArrow (ts, t) -> TArrow (subst_typs x s ts, subst x s t)
  | _ -> t
and subst_typs (x:id) (s:typ) (ts:typ list): typ list =
  List.fold (fun rs t -> rs@[subst x s t]) [] ts
 
let substitute (m:substitutions) (t:typ): typ =
  let s = Map.toList m in
  List.foldBack (fun (x, s) t -> subst x s t) s t

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
  | TVar y -> x = y
  | TApp (u, l) ->   occurs x u || aux false l
  | TArrow (l, u) -> aux false l || occurs x u
  | _ -> false

let bind (m:substitutions) (x:id) (t:typ): substitutions =
  match t with
  | TVar y -> if (x=y) then m else Map.add x t m
  | _ -> if occurs x t then err ("circular type constraint") else Map.add x t m

let unify_lower_bound l1 l2 =
  match (l1, l2) with 
  | (Int i1, Int i2) -> if i1 < i2 then Int i2 else Int i2
  | (NegInf, _) | (_, NegInf) -> NegInf
  | _ -> err ("cannot unify integer lower bound")

let unify_upper_bound l1 l2 =
  match (l1, l2) with 
  | (Int i1, Int i2) -> if i1 > i2 then Int i2 else Int i2
  | (Inf, _) | (_, Inf) -> Inf
  | _ -> err ("cannot unify integer lower bound")

let bind_typ (m:substitutions) (s:typ) (t:typ):substitutions =
  match s with
  | TVar x -> bind m x t
  | _ -> m

let rec unify_one (m:substitutions) (s:typ) (t:typ):substitutions =
  let t1 = substitute m s in
  let t2 = substitute m t in
  match (t1, t2) with
  | (TVar x, _) -> bind m x t2
  | (_, TVar x) -> bind m x t1
  | (TInt (l1, h1), TInt (l2, h2)) -> 
    let u = TInt(unify_lower_bound l1 l2, unify_upper_bound h1 h2) in
    let m = bind_typ m s u in bind_typ m t u
  | (TArrow (xs, y), TArrow (us, v)) -> 
    let tc = List.fold2 (fun l t1 t2 -> l@[(t1, t2)]) [] xs us in
    unify m (tc@[(y, v)])
  | (TApp (x, ys), TApp (u, vs)) -> 
    let tc = List.fold2 (fun (l:typ_constraints) t1 t2 -> l@[(t1, t2)]) [] ys vs in
    unify m ([(x, u)]@tc)
  | (TName (Id x), TName (Id y)) -> 
    if x = y then m else err ("type mismatch ")
  | _ -> err ("type mismatch ")

and unify (m:substitutions) (tc:typ_constraints):substitutions =
  match tc with
  | [] -> m
  | (x, y) :: t ->
    let m = unify m t in
    unify_one m x y in

let bnd_equal b1 b2 =
  match (b1, b2) with 
  | (Int i1, Int i2) -> i1 = i2
  | (NegInf, NegInf) -> true
  | (Inf, Inf) -> true
  | _ -> false

let rec typ_equal t1 t2 = 
  match (t1, t2) with
  | (TName (Id x), TName (Id y)) -> x = y
  | (TApp (t1, ts1), TApp (t2, ts2)) ->
    (typ_equal t1 t2) && List.fold2 (fun b t1 t2 -> b && typ_equal t2 t2) true ts1 ts2
  | (TVar _, TVar _) -> internalErr "type variable should be resolved already"
  | (TInt (l1, h1), TInt(l2, h2)) ->
    (bnd_equal l1 l2) && (bnd_equal h1 h2)
  | (TArrow (xs, y), TArrow (us, v)) ->
    List.fold2 (fun b t1 t2 -> b&& typ_equal t1 t2) true xs us && (typ_equal y v)
  | _ -> internalErr "type mismatch"

let insert_cast (e:exp) (t:typ) (et:typ) : exp =
  // cast from type 't' to 'et'
  // TODO: check the cast is legal
  ECast (e, et)

let rec subst_exp (s:substitutions) (e:aexp) : exp =
  match e with
  | AELoc (loc, ae) -> ELoc (loc, subst_exp s ae)
  | AEVar (x, t, et) ->
    let t = substitute s t in 
    let et = substitute s et in
    let e = EVar x in
    if (typ_equal t et) then e else insert_cast e t et
  | AEInt (i, t, et) ->
    let t = substitute s t in 
    let et = substitute s t in
    let e = EInt i in
    if (typ_equal t et) then e else insert_cast e t et
  | AEReal (s, t) -> EReal s
  | AEBitVector (n, i, t) -> EBitVector (n, i)
  | AEBool (b, t, et) -> 
    let et = substitute s t in
    let e = EBool b in 
    if (typ_equal t et) then e else insert_cast e t et
  | AEString (s, t) -> EString s
  | AEOp (op, aes, t, et) ->
    let es = List.map (fun ae -> subst_exp s ae) aes in
    let t = substitute s t in 
    let et = substitute s t in
    let op = 
      match op with 
      | Bop p -> 
        if isArithmeticOp p then
          // make sure t is TInt
          match t with | TInt (_, _) -> op | _ -> err "expected int type"
        else if isLogicOp p then
          // make sure t is bool or prop, if t is prop, swap in "/\" "\/" for "&&" "||"
          match t with 
          | TName (Id "bool") -> op
          | TName (Id "prop") -> 
            match p with | BAnd -> Bop BLand | BOr -> Bop BLor | _-> op
          | _ -> err "expected bool/prop type"
        else op
      | _ -> op
    let e = EOp (op, es) in
    if (typ_equal t et) then e else insert_cast e t et
  | AEApply (x, aes, ts, ets) ->
    let es = List.map (fun ae -> subst_exp s ae) aes  in
    let t = List.map (fun t -> substitute s t) ts in 
    let et = List.map (fun t -> substitute s t) ets in
    let e = EApply (x, es) in
    let equal = List.fold2 (fun b t1 t2 -> b&&typ_equal t1 t2) true t et
    if equal then e else
      if(List.length t <> 1) then err ("cast for more than one return types not implemented");
      else insert_cast e t.Head et.Head
  | AEBind (bOp, aes, xs, ts, ae, t, et) ->
    let es = List.map (fun ae -> subst_exp s ae) aes  in
    let t = substitute s t in 
    let et = substitute s t in
    let e = subst_exp s ae in
    let e = EBind(bOp, es, xs, ts, e) in
    if (typ_equal t et) then e else insert_cast e t et
  | AECast (ae, t) ->
    ECast((subst_exp s ae), t)

let tc_exp (env:env) (e:exp): (typ * exp) = 
  let (t, ae, cl) = infer_exp env e None in
  let s = unify Map.empty cl in
  let t = substitute s t in
  let es = subst_exp s ae in
  (t, es)

let make_operand_alias (x:id) (env:env) =
  let (_, info) = lookup_id env x in
  match info with
  | OperandLocal _ | StateInfo _ | OperandAlias _ -> OperandAlias (x, info)
  | GhostLocal _ | ProcLocal _ | ThreadLocal _ | InlineLocal _ ->
      err ("'" + (err_id x) + "' must be an operand or state member")

let rec update_env_stmt (env:env) (s:stmt): env =
  match s with
  | SLoc (loc, s) -> update_env_stmt env s
  | SLabel _ | SGoto _ | SReturn | SAssume _ | SAssert _ | SCalc _ -> env
  | SVar (x, t, m, g, a, eOpt) ->
    (
      let info =
        match g with
        | XAlias (AliasThread, e) -> ThreadLocal {local_in_param = false; local_exp = e; local_typ = t}
        | XAlias (AliasLocal, e) -> ProcLocal {local_in_param = false; local_exp = e; local_typ = t}
        | XGhost -> GhostLocal (m, t)
        | XInline -> InlineLocal t
        | (XOperand | XPhysical | XState _) -> err ("variable must be declared ghost, {:local ...}, or {:register ...} " + (err_id x))
        in
      let t = match t with Some t -> t | None -> next_type_var() in
      push_id env x t info
    )
  | SAlias (x, y) ->
      let t = next_type_var() in
      push_id env x t (make_operand_alias y env)
  | SAssign (xs, e) ->
      push_lhss env xs
  | SLetUpdates _ | SBlock _ | SQuickBlock _ | SIfElse _ | SWhile _ -> env
  | SForall (xs, ts, ex, e, b) -> env
  | SExists (xs, ts, e) -> env
      
let resolve_id env id:unit =
  match id with
  | Reserved _ -> ()
  | _ ->
    match lookup_name env id true with
    | None -> err ("Identifier not found " + (err_id id))
    | Some r -> ()

let rec resolve_type env t:unit =
  let resolve_name id = 
    match lookup_name env id true with
    | Some _ -> ()
    | None -> () 
      // TODO: enable code below once we have imported types from F* 
      // err ("type not found " + (err_id id))
  match t with 
  | TName id -> resolve_name id
  | TApp (t, ts) -> resolve_type env t; resolve_types env ts
  | TArrow (ts, t) -> resolve_types env ts; resolve_type env t
  | _ -> ()
and resolve_types env ts = List.iter (resolve_type env) ts;

let rec tc_stmt (env:env) (s:stmt):stmt =
  match s with
  | SLoc (loc, s) -> SLoc (loc, tc_stmt env s)
  | SLabel x -> resolve_id env x; s
  | SGoto x -> resolve_id env x; s
  | SReturn -> s
  | SAssume e -> let (t, e) = tc_exp env e in SAssume e
  | SAssert (attrs, e) -> let (t, e) = tc_exp env e in SAssert (attrs, e)
  | SCalc (oop, contents) -> err ("not implemented")
  | SVar (x, t, m, g, a, eOpt) -> 
    // TODO: insert cast if 't' and 'eOpt' type do not match
    match t with | Some t -> resolve_type env t | None -> ();
    let eOpt = match eOpt with | Some e -> let (t, e) = tc_exp env e in Some e | _ -> None in
    SVar (x, t, m, g, a, eOpt)
  | SAlias (x, y) ->  err ("not implemented")
  | SAssign (xs, e) -> let (t, e) = tc_exp env e in SAssign (xs, e)
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SBlock b -> let (env, b) = tc_stmts env b in SBlock b
  | SQuickBlock (x, b) -> let (env, b) = tc_stmts env b in SQuickBlock (x, b)
  | SIfElse (g, e, b1, b2) -> 
    err ("not implemented")
  | SWhile (e, invs, ed, b) ->
    err ("not implemented")
  | SForall (xs, ts, ex, e, b) ->
    err ("not implemented")
  | SExists (xs, ts, e) ->
    err ("implemented")
and tc_stmts (env:env) (ss:stmt list):(env*stmt list) = List.fold (fun (env, l) s -> let (ts:stmt) = tc_stmt env s in (update_env_stmt env s, l@[ts])) (env, []) ss

let tc_proc (env:env) (p:proc_decl): (env*proc_decl) =
  // TODO: typecheck requires/ensures etc.
  let env = push_proc env p.pname p None in
  let globals = ref env.scope_mods in 
  let env = push_params_without_rets env p.pargs p.prets in
  let env = push_rets env p.prets
  let (env, body) = 
    match p.pbody with
    | None -> (env, None)
    | Some ss -> let (env, ss) = tc_stmts env ss in (env, Some ss)
  let pNew = {p with pbody = body} in
  let env = {env with scope_mods = !globals } in
  (env, pNew)

let tc_decl (env:env) (decl:((loc * decl) * bool)) : env * ((loc * decl) * bool) =
  let ((l,d),b) = decl in
  match d with
  | DVar (x, t, XAlias (AliasThread, e), _) ->
      // TODO: type check t and e
      let env = push_id env x t (ThreadLocal {local_in_param = false; local_exp = e; local_typ = Some t}) in
      (env, decl)
  | DVar (x, t, XState e, _) ->
    ( 
      // TODO: type check t and e
      match skip_loc e with
      | EApply (Id id, es) ->
          let env = push_id env x t (StateInfo (id, es, t)) in
          (env, decl)
      | _ -> err ("declaration of state member " + (err_id x) + " must provide an expression of the form f(...args...)")
    )
  | DFun ({fbody = None} as f) ->
    let env = push_func env f.fname f in
    (env, decl)
  | DProc p ->
    let (env,p) = tc_proc env p in 
    (env, ((l, DProc(p)), b))
  | _ -> (env, decl)

let tc_decls (ds:((loc * decl) * bool) list) : ((loc * decl) * bool) list = 
  let (env,dss) = List.fold (fun (env:env,l:((loc * decl) * bool) list) d -> let (env, d) = tc_decl env d in (env, l@[d])) (empty_env,[]) ds in
  dss