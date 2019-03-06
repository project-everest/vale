// Make local transformations on operands and overloaded terms:
//   - resolve overloading
//   - turn operands into appropriate ghost variables
//   - turn references to operands into appropriate ghost variables
// Mostly, this is about changing expressions and arguments

module Transform

open Ast
open Ast_util
open Parse
open TypeChecker
open Microsoft.FSharp.Math

let assumeUpdates = ref 0

type id_local = {local_in_param:bool; local_exp:exp; local_typ:typ option} // In parameters are read-only and refer to old(state)
type id_info =
| GhostLocal of mutability * typ option
| ProcLocal of id_local
| ThreadLocal of id_local
| InlineLocal of typ option
| OperandLocal of inout * typ
| StateInfo of string * exp list * typ
| OperandAlias of id * id_info

type env =
  {
    funs:Map<id, fun_decl>;
    procs:Map<id, proc_decl>;
    raw_procs:Map<id, proc_decl>;
    ids:Map<id, id_info>;
    mods:Map<id, bool>;
    lets:(loc * lets) list
    state:exp;
    abstractOld:bool; // if true, x --> va_old_x in abstract lemma
    checkMods:bool;
  }

let empty_env:env =
  {
    funs = Map.empty;
    procs = Map.empty;
    raw_procs = Map.empty;
    ids = Map.empty;
    mods = Map.empty;
    lets = [];
    state = evar (Reserved "s");
    abstractOld = false;
    checkMods = false;
  }

let vaApp (s:string) (es:exp list):exp = eapply (Reserved s) es
let vaApp_t (s:string) (es:exp list) (t:typ option):exp = eapply_t (Reserved s) es t
let vaAppOp (prefix:string) (t:typ) (es:exp list) (tOpt:typ option):exp =
  match t with
  | TName (Id x) -> vaApp_t (qprefix prefix x) es tOpt
  | _ -> err "operands must have simple named types"

let vaEvalOp (t:typ) (state:exp) (e:exp):exp =
  match t with
  | TName (Id x) -> vaApp_t (qprefix ("eval_") x) [state; e] (exp_typ e)
  | _ -> err "operands must have simple named types"

let vaOperandTyp (t:typ) : string =
  match t with
  | TName (Id x) -> "operand_" + x
  | _ -> err "operands must have simple named types"

let vaValueTyp (t:typ) : string =
  match t with
  | TName (Id x) -> "value_" + x
  | _ -> err "operands must have simple named types"

let vaTyp (t:typ) : string =
  match t with
  | TName (Id x) -> x
  | _ -> err "operands must have simple named types"

let in_id (x:id) = Reserved ("in_" + (string_of_id x))
let old_id (x:id) = Reserved ("old_" + (string_of_id x))
let prev_id (x:id) = Reserved ("prev_" + (string_of_id x))
let body_id (x:id) = Id ((string_of_id x) + "_body")
let while_id (x:id) = Id ((string_of_id x) + "_while")

let is_quick_body (a:attrs):bool =
  if List_mem_assoc (Id "quick") a then
    match List_assoc (Id "quick") a with
    | [e] -> (match skip_loc e with EVar (Id "exportOnly", _) -> false | _ -> true)
    | _ -> true
  else false

let exp_abstract (useOld:bool) (e:exp):exp =
  let c e = match e with EOp (Uop UConst, [e], _) -> e | _ -> e in
  map_exp (fun e -> match e with EOp (RefineOp, [e1; e2; e3], _) -> Replace (if useOld then c e2 else c e1) | _ -> Unchanged) e

let exp_refined (e:exp):exp =
  map_exp (fun e -> match e with EOp (RefineOp, [e1; e2; e3], _) -> Replace e3 | _ -> Unchanged) e

let stmts_abstract (useOld:bool) (ss:stmt list):stmt list =
  map_stmts (exp_abstract useOld) (fun _ -> Unchanged) ss

// TODO: get rid of "refined"
let stmts_refined (ss:stmt list):stmt list =
  map_stmts exp_refined (fun _ -> Unchanged) ss

let make_operand_alias (x:id) (env:env) =
  if not (Map.containsKey x env.ids) then err ("cannot find declaration of '" + (err_id x) + "'") else
  let info = Map.find x env.ids in
  match info with
  | OperandLocal _ | StateInfo _ | OperandAlias _ -> OperandAlias (x, info)
  | GhostLocal _ | ProcLocal _ | ThreadLocal _ | InlineLocal _ ->
      err ("'" + (err_id x) + "' must be an operand or state member")

let rec env_map_exp (f:env -> exp -> exp map_modify) (env:env) (e:exp):exp =
  map_apply_modify (f env e) (fun () ->
    let r = env_map_exp f env in
    match e with
    | ELoc (loc, e) -> try ELoc (loc, r e) with err -> raise (LocErr (loc, err))
    | EVar _ | EInt _ | EReal _ | EBitVector _ | EBool _ | EString _ -> e
    | EBind (b, es, fs, ts, e, t) ->
        let es = List.map r es in
        let env =
          match (b, List.map (exp_abstract false) es, fs) with
          | (BindAlias, [EVar (y, _)], [(x, t)]) ->
              {env with ids = Map.add x (make_operand_alias y env) env.ids}
          | (BindAlias, _, _) -> internalErr (sprintf "BindAlias %A %A" es fs)
          | (_, _, _) ->
              {env with ids = List.fold (fun env (x, t) -> Map.add x (GhostLocal (Immutable, t)) env) env.ids fs}
          in
        let r = env_map_exp f env in
        EBind (b, es, fs, List.map (List.map r) ts, r e, t)
    | EOp (op, es, t) -> EOp (op, List.map r es, t)
    | EApply (x, ts, es, t) -> EApply (x, ts, List.map r es, t)
    | ECast (e, t) -> ECast (r e, t)
    | ELabel (loc, e) -> ELabel (loc, r e)
  )

let rec env_map_exp_state (f:env -> exp -> exp map_modify) (env:env) (e:exp):exp =
  let f_state (env:env) (e:exp):exp map_modify =
    match e with
    | EVar (Reserved "this", _) -> Replace env.state
    | EOp (Uop UOld, [e], _) ->
        let env = {env with state = evar (Reserved "old_s"); abstractOld = true} in
        Replace (env_map_exp_state f env e)
    | EOp (Bop BOldAt, [es; e], _) ->
        let env = {env with state = es} in
        Replace (env_map_exp_state f env e)
    | _ -> Unchanged
    in
  env_map_exp (map_apply_compose2 f f_state) env e

let rec env_stmt (env:env) (s:stmt):(env * env) =
  match s with
  | SLoc (loc, s) -> env_stmt env s
  | SLabel _ | SGoto _ | SReturn | SAssume _ | SAssert _ | SCalc _ -> (env, env)
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
      let ids = Map.add x info env.ids in
      (env, {env with ids = ids})
    )
  | SAlias (x, y) ->
      let ids = Map.add x (make_operand_alias y env) env.ids in
      (env, {env with ids = ids})
  | SAssign (xs, e) ->
      let ids = List.fold (fun ids (x, dOpt) -> match dOpt with None -> ids | Some (t, _) -> Map.add x (GhostLocal (Mutable, t)) ids) env.ids xs in
      (env, {env with ids = ids})
  | SLetUpdates _ | SBlock _ | SQuickBlock _ | SIfElse _ | SWhile _ -> (env, env)
  | SForall (xs, ts, ex, e, b) ->
      ({env with ids = List.fold (fun env (x, t) -> Map.add x (GhostLocal (Immutable, t)) env) env.ids xs}, env)
  | SExists (xs, ts, e) ->
      (env, {env with ids = List.fold (fun env (x, t) -> Map.add x (GhostLocal (Immutable, t)) env) env.ids xs})

let rec env_map_stmt (fe:env -> exp -> exp) (fs:env -> stmt -> (env * stmt list) map_modify) (env:env) (s:stmt):(env * stmt list) =
  map_apply_modify (fs env s) (fun () ->
    let fee = fe env in
    let r = env_map_stmt fe fs env in
    let rs = env_map_stmts fe fs env in
    match s with
    | SLoc (loc, s) -> try let (env, ss) = r s in (env, List.map (fun s -> SLoc (loc, s)) ss) with err -> raise (LocErr (loc, err))
    | SLabel x -> (env, [s])
    | SGoto x -> (env, [s])
    | SReturn -> (env, [s])
    | SAssume e -> (env, [SAssume (fee e)])
    | SAssert (attrs, e) -> (env, [SAssert (attrs, fee e)])
    | SCalc (op, contents, e) -> (env, [SCalc (op, (List.map (env_map_calc_contents fe fs env) contents), fee e)])
    | SVar (x, t, m, g, a, eOpt) ->
        (snd (env_stmt env s), [SVar (x, t, m, g, map_attrs fee a, mapOpt fee eOpt)])
    | SAlias (x, y) -> (snd (env_stmt env s), [SAlias (x, y)])
    | SAssign (xs, e) -> (snd (env_stmt env s), [SAssign (xs, fee e)])
    | SLetUpdates _ -> internalErr "SLetUpdates"
    | SBlock b -> (env, [SBlock (rs b)])
    | SQuickBlock (x, b) -> (env, [SQuickBlock (x, rs b)])
    | SIfElse (g, e, b1, b2) -> (env, [SIfElse (g, fee e, rs b1, rs b2)])
    | SWhile (e, invs, ed, b) ->
        (env, [SWhile (fee e, List_mapSnd fee invs, mapSnd (List.map fee) ed, rs b)])
    | SForall (xs, ts, ex, e, b) ->
        let env1 = fst (env_stmt env s) in
        let fee = fe env1 in
        let rs = env_map_stmts fe fs env1 in
        (env, [SForall (xs, List.map (List.map fee) ts, fee ex, fee e, rs b)])
    | SExists (xs, ts, e) ->
        let env = snd (env_stmt env s) in
        let fee = fe env in
        (env, [SExists (xs, List.map (List.map fee) ts, fee e)])
  )
and env_map_stmts (fe:env -> exp -> exp) (fs:env -> stmt -> (env * stmt list) map_modify) (env:env) (ss:stmt list):stmt list =
  List.concat (snd (List_mapFoldFlip (env_map_stmt fe fs) env ss))
and env_map_calc_contents (fe:env -> exp -> exp) (fs:env -> stmt -> (env * stmt list) map_modify) (env:env)  (cc:calcContents) =
  let {calc_exp = e; calc_op = op; calc_hints = hints} = cc in
  {calc_exp = fe env e; calc_op = op; calc_hints = List.map (env_map_stmts fe fs env) hints}

let env_next_stmt (env:env) (s:stmt):env =
  let (env, _) = env_map_stmt (fun _ e -> e) (fun _ _ -> Unchanged) env s in
  env

let env_map_spec (fe:env -> exp -> exp) (fs:env -> loc * spec -> (env * (loc * spec) list) map_modify) (env:env) ((loc:loc), (s:spec)):(env * (loc * spec) list) =
  map_apply_modify (fs env (loc, s)) (fun () ->
    let fee = fe env in
    match s with
    | Requires (r, e) -> (env, [(loc, Requires (r, fee e))])
    | Ensures (r, e) -> (env, [(loc, Ensures (r, fee e))])
    | Modifies (m, e) -> (env, [(loc, Modifies (m, fee e))])
    | SpecRaw (RawSpec _) -> internalErr "SpecRaw"
    | SpecRaw (Lets ls) ->
        let map_let env (loc, l) =
          match l with
          | LetsVar (x, t, e) ->
              let ids = Map.add x (GhostLocal (Immutable, t)) env.ids in
              let env = {env with ids = ids; lets = (loc, l)::env.lets} in
              (env, [(loc, LetsVar (x, t, fee e))])
          | LetsAlias (x, y) ->
              let ids = Map.add x (make_operand_alias y env) env.ids in
              let env = {env with ids = ids; lets = (loc, l)::env.lets} in
              (env, [(loc, l)])
        in
        let (env, ls) = List_mapFoldFlip map_let env ls in
        let ls = List.concat ls in
        (env, [(loc, SpecRaw (Lets ls))])
  )
let env_map_specs (fe:env -> exp -> exp) (fs:env -> loc * spec -> (env * (loc * spec) list) map_modify) (env:env) (specs:(loc * spec) list):(env * (loc * spec) list) =
  let (env, specs) = List_mapFoldFlip (env_map_spec fe fs) env specs in
  (env, List.concat specs)

let match_proc_args (p:proc_decl) (rets:lhs list) (args:exp list):((pformal * lhs) list * (pformal * exp) list) =
  let (nap, nac) = (List.length p.pargs, List.length args) in
  let (nrp, nrc) = (List.length p.prets, List.length rets) in
  if nap <> nac then err ("in call to " + (err_id p.pname) + ", expected " + (string nap) + " argument(s), found " + (string nac) + " argument(s)") else
  if nrp <> nrc then err ("procedure " + (err_id p.pname) + " returns " + (string nrp) + " value(s), call expects " + (string nrc) + " return value(s)") else
  (List.zip p.prets rets, List.zip p.pargs args)

let operandProc (xa:id) (io:inout):id =
  let xa = string_of_id xa in
  match io with
  | In | InOut -> Id (xa + "_in")
  | Out -> Id (xa + "_out")

///////////////////////////////////////////////////////////////////////////////
// Read/modify analysis

let rec resolve_alias (env:env) (x:id):id =
  match Map.tryFind x env.ids with
  | Some (OperandAlias (y, _)) -> resolve_alias env y
  | _ -> x

// Compute (reads, reads as old, mods) to variables in env0 (not env1).  The complete environment is env0 + env1.
let rec compute_read_mods_stmt (env0:env) (env1:env) (s:stmt):(env * Set<id> * Set<id> * Set<id>) =
  let rs = compute_read_mods_stmts env0 env1 in
  let filter_ids (xs:Set<id>) =
    let xs = Set.map (resolve_alias env1) xs in
    Set.filter (fun x -> Map.containsKey x env0.ids && not (Map.containsKey x env1.ids)) xs
    in
  let env1 = snd (env_stmt env1 s) in
  let compute_exps (es:exp list) =
    let reads = Set.unionMany (List.map free_vars_exp es) in
    let fOld (e:exp) (xss:Set<id> list):Set<id> =
      match e with
      | EOp (Uop UOld, [e], _) -> free_vars_exp e
      | _ -> Set.unionMany xss
      in
    let readsOld = Set.unionMany (List.map (gather_exp fOld) es) in
    (env1, filter_ids reads, filter_ids readsOld, Set.empty)
    in
  let rec compute_call (p:proc_decl) (lhss:lhs list) (es:exp list):(Set<id> * Set<id>) =
    let collect_p_mods (_, s):(mod_kind * id) list =
      match s with
      | Modifies (m, e) ->
        (
          match skip_loc (exp_abstract false e) with
          | EVar (x, _) -> [(m, x)]
          | _ -> []
        )
      | _ -> []
      in
    let p_rmods = List.collect collect_p_mods p.pspecs in
    // TODO: process mrets
    let rec collect_operand (pp, ea):(mod_kind * id) list =
      match pp with
      | (_, _, XOperand, io, _) ->
        (
          match skip_loc ea with
          | ECast (e, _) ->
            collect_operand (pp, e)
          | EVar (x, _) ->
            (
              let x = resolve_alias env1 x in
              [((match io with In -> Read | InOut | Out -> Modify), x)]
            )
          | EOp (Uop UConst, _, _) | EInt _ -> []
          | EApply (e, _, args, _) when is_id e && Map.containsKey (operandProc (id_of_exp e) io) env0.procs ->
            (
              let xa = id_of_exp e in
              let xa_in = operandProc xa In in
              let xa_out = operandProc xa Out in
              let process_io io =
                let (rs, ms) =
                  match io with
                  | In | InOut ->
                      if (not (Map.containsKey xa_in env0.procs)) then err ("could not find procedure " + (err_id xa_in)) else
                      let p_in = Map.find xa_in env0.procs in
                      let p_in = {p_in with prets = []} in
                      compute_call p_in [] args
                  | Out ->
                      if (not (Map.containsKey xa_out env0.procs)) then err ("could not find procedure " + (err_id xa_out)) else
                      let p_out = Map.find xa_out env0.procs in
                      let p_out = {p_out with pargs = List.take (List.length p_out.pargs - 1) p_out.pargs} in
                      compute_call p_out [] args
                  in
                List.map (fun x -> (Read, x)) (Set.toList rs) @ List.map (fun x -> (Modify, x)) (Set.toList ms)
                in
              match io with
              | In -> process_io In
              | Out -> process_io Out
              | InOut -> process_io In @ process_io Out
            )
          | _ -> []
        )
      | _ -> []
      in
    let (mrets, margs) = match_proc_args p lhss es in // TODO: mrets
    let p_rmods = List.collect collect_operand margs @ p_rmods in
    // REVIEW: right now, Preserve is (conservatively) treated as Modify
    let (p_reads, p_mods) = List.partition (fun (m, _) -> match m with Read -> true | Modify | Preserve -> false) p_rmods in
    let p_reads = Set.ofList (List.map snd p_reads) in
    let p_mods = Set.ofList (List.map snd p_mods) in
    (p_reads, p_mods)
    in
  match s with
  | SLoc (loc, s) -> compute_read_mods_stmt env0 env1 s
  | SLabel x -> compute_exps []
  | SGoto x -> compute_exps []
  | SReturn -> compute_exps []
  | SAssume e -> compute_exps [e]
  | SAssert (attrs, e) -> compute_exps [e]
  | SCalc (op, contents, e) ->
      let compute_content cc =
        let {calc_exp = e; calc_op = oop; calc_hints = hints} = cc in
        let (_, rs0, rso0, _) = compute_exps [e] in
        let f (env1, rs0, rso0, mods0) b =
          let (env1, rs1, rso1, mods1) = rs b in
          (env1, Set.union rs0 rs1, Set.union rso1 rso1, Set.union mods0 mods1)
        let (env1, rs1, rso1, mods1) = List.fold f (env1, Set.empty, Set.empty, Set.empty) hints in
        (env1, Set.union rs0 rs1, Set.union rso0 rso1, mods1)
      let compute_contents cs : (env * Set<id> * Set<id> * Set<id>)=
        let f (env1, rs0, rso0, mods0) cc =
          let (env1, rs1, rso1, mods1) = compute_content cc in
          (env1, Set.union rs0 rs1, Set.union rso0 rso1, Set.union mods0 mods1)
        in
        List.fold f (env1, Set.empty, Set.empty, Set.empty) cs
      let (_, rs1, rso1, mods1) = compute_contents contents in
      let (_, rs0, rso0, _) = compute_exps [e] in
      (env1, Set.union rs0 rs1, Set.union rso0 rso1, mods1)
  | SVar (x, t, m, g, a, eOpt) -> compute_exps (match eOpt with None -> [] | Some e -> [e])
  | SAlias (x, y) -> compute_exps []
  | SAssign (lhss, e) ->
      let (rs0, mods0) =
        match skip_loc e with
        | EApply (e, _, es, _) when is_id e && Map.containsKey (id_of_exp e) env0.procs ->
            let x = id_of_exp e in
            let p = Map.find x env0.procs in
            compute_call p lhss es
        | _ -> (Set.empty, Set.empty)
        in
      let (_, reads, readsOld, _) = compute_exps [e] in
      let xs_update = List.collect (fun lhs -> match lhs with (x, None) -> [x] | _ -> []) lhss in
      let mods = filter_ids (Set.ofList xs_update) in
      (env1, Set.union rs0 reads, readsOld, Set.union mods0 mods)
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SBlock b -> rs b
  | SQuickBlock (_, b) -> rs b
  | SIfElse (g, e, b1, b2) ->
      let (_, rs0, rso0, _) = compute_exps [e] in
      let (_, rs1, rso1, mods1) = rs b1 in
      let (_, rs2, rso2, mods2) = rs b2 in
      (env1, Set.unionMany [rs0; rs1; rs2], Set.unionMany [rso0; rso1; rso2], Set.union mods1 mods2)
  | SWhile (e, invs, (_, ed), b) ->
      let (_, rs0, rso0, _) = compute_exps (e::ed @ (List.map snd invs)) in
      let (_, rs1, rso1, mods1) = rs b in
      (env1, Set.union rs0 rs1, Set.union rso0 rso1, mods1)
  | SForall (xs, ts, ex, e, b) ->
      let env2 = fst (env_stmt env1 s) in
      let ee = ebind Forall [] xs ts (eop (Bop BImply) [ex; e]) in
      let (_, rs0, rso0, _) = compute_exps [ee] in
      let (_, rs1, rso1, _) = compute_read_mods_stmts env0 env2 b in
      (env1, Set.union rs0 rs1, Set.union rso0 rso1, Set.empty)
  | SExists (xs, ts, e) ->
      let ee = ebind Exists [] xs ts e in
      compute_exps [ee]
and compute_read_mods_stmts (env0:env) (env1:env) (ss:stmt list):(env * Set<id> * Set<id> * Set<id>) =
  let f (env1, rs0, rso0, mods0) s =
    let (env1, rs1, rso1, mods1) = compute_read_mods_stmt env0 env1 s in
    (env1, Set.union rs0 rs1, Set.union rso0 rso1, Set.union mods0 mods1)
    in
  List.fold f (env1, Set.empty, Set.empty, Set.empty) ss

///////////////////////////////////////////////////////////////////////////////
// Resolve overloading
let rec resolve_overload_expr (env:env) (e:exp):exp =
  let rec fe (env:env) (e:exp):exp map_modify =
    let r = resolve_overload_expr env in
    let rs = List.map r in
    match e with
    | EOp (Uop (UCustom op), l, t) ->
        match Map.tryFind (Operator op) env.funs with
        | Some {fargs = [_]; fattrs = attrs} ->
            Replace (eapply_t (attrs_get_id (Reserved "alias") attrs) (rs l) t)
        | _ -> err ("operator '" + op + "' must be overloaded to use as a prefix operator")
    | EOp (Bop (BCustom op), l, t) ->
        match Map.tryFind (Operator op) env.funs with
        | Some {fargs = [_; _]; fattrs = attrs} ->
            Replace (eapply_t (attrs_get_id (Reserved "alias") attrs) (rs l) t)
        | _ -> err ("operator '" + op + "' must be overloaded to use as a infix operator")
    | _ -> Unchanged
    in
    env_map_exp fe env e

let resolve_overload_stmt (env:env) (s:stmt):(env * stmt list) =
  env_map_stmt resolve_overload_expr (fun _ s -> Unchanged) env s

let resolve_overload_stmts (env:env) (ss:stmt list):stmt list =
  List.concat (snd (List_mapFoldFlip resolve_overload_stmt env ss))

///////////////////////////////////////////////////////////////////////////////
// Propagate variables through state via assumes (if requested)

(*
// Currently only works for straight-line code (no if/else or while)
let assume_updates_stmts (env:env) (args:pformal list) (rets:pformal list) (ss:stmt list) (specs:spec list):stmt list =
  if !assumeUpdates = 0 then ss else
  let thisAt i = Reserved ("assume_this_" + (string i)) in
  let setPrev (i:int) (prev:Map<id, int>) (xs:id list):(int * Map<id, int> * stmt list) =
    match xs with
    | [] -> (i, prev, [])
    | _::_ ->
        let ss = [SVar (thisAt i, Some tState, XGhost, [], Some (EVar (Reserved "this")))] in
        let prev = List.fold (fun prev x -> Map.add x i prev) prev xs in
        (i + 1, prev, ss)
    in
  let genAssume (env:env) (prev:Map<id, int>) (x:id):stmt list =
    match Map.tryFind x env.ids with
    | None | Some (GhostLocal _) -> []
    | Some (OperandLocal _ | ThreadLocal _ | ProcLocal _ | InlineLocal _ | StateInfo _) ->
        let old_state = match Map.tryFind x prev with None -> EOp (Uop UOld, [EVar (Reserved "this")]) | Some i -> EOp (Bop BOldAt, [EVar (thisAt i); EVar (Reserved "this")]) in
//        let old_x = match Map.tryFind x prev with None -> EOp (Uop UOld, [EVar x]) | Some i -> EOp (Bop BOldAt, [EVar (thisAt i); EVar x]) in
        let eq = EApply (Reserved "eq_ops", [old_state; EVar (Reserved "this"); (EOp (Uop UToOperand, [EVar x]))]) in
        [(if !assumeUpdates = 1 then SAssume eq else SAssert (assert_attrs_default, eq))]
    in
  let f (env:env, i:int, prev:Map<id, int>, sss:stmt list list) (s:stmt) =
    let rec r s =
      match s with
      | SLoc (loc, s) ->
          let (i, prev, ss) = r s in
          (i, prev, List.map (fun s -> SLoc (loc, s)) ss)
      | (SLabel _ | SGoto _ | SReturn) -> (i, prev, [s])
      | SVar (x, t, (XGhost | XInline | XOperand | XPhysical | XState _), a, eOpt) ->
          (i, prev, [s])
      | SVar (x, t, XAlias _, a, eOpt) ->
          let (i, prev, ss) = setPrev i prev [x] in
          (i, prev, [s] @ ss)
      | SAssign (lhss, e) ->
        (
          match skip_loc e with
          | EApply (x, es) when Map.containsKey x env.procs ->
              let xfs = Set.toList (free_vars_stmt s) in
              let ssAssume = List.collect (genAssume env prev) xfs in
              let (mrets, margs) = match_proc_args (Map.find x env.procs) lhss es in
              let xrets = List.map (fun ((_, _, g, _, _), (x, _)) -> (EVar x, Out, g)) mrets in
              let xargs = List.map (fun ((_, _, g, io, _), e) -> (skip_loc e, io, g)) margs in
              let fx e_io_g =
                match e_io_g with
                | (EVar x, (Out | InOut), (XOperand | XAlias _ | XInline)) -> [x]
                | _ -> []
                in
              let xsOut = List.collect fx (xrets @ xargs) in
              let (i, prev, ssSet) = setPrev i prev xsOut in
              (i, prev, ssAssume @ [s] @ ssSet)
          | _ ->
              let xfs = Set.toList (free_vars_stmt s) in
              (i, prev, (List.collect (genAssume env prev) xfs) @ [s])
        )
      | (SAssume _ | SAssert _ | SForall _ | SExists _) ->
          let xfs = Set.toList (free_vars_stmt s) in
          (i, prev, (List.collect (genAssume env prev) xfs) @ [s])
      | (SIfElse _ | SWhile _) ->
          // Not yet supported
          (i, prev, [s])
      in
    let (i, prev, ss) = r s in
    let sss = ss::sss in
    let env = env_next_stmt env s in
    (env, i, prev, sss)
  in
  let (env, i, prev, sssRev) = List.fold f (env, 0, Map.empty, []) ss in
  let ss = List.concat (List.rev sssRev) in
  let enss = List.collect (fun s -> match s with Ensures e -> [s] | _ -> []) specs in
  let globals = List.collect (fun (x, info) -> match info with ThreadLocal _ -> [x] | _ -> []) (Map.toList env.ids) in
  let xArgs = List.collect (fun (x, _, g, io, _) -> match (g, io) with ((XOperand | XAlias _ | XInline), _ (* TODO? InOut | Out *)) -> [x] | _ -> []) args in
  let xRets = List.collect (fun (x, _, g, io, _) -> match (g, io) with ((XOperand | XAlias _ | XInline), _) -> [x] | _ -> []) rets in
  let xfs = Set.toList (Set.unionMany [Set.ofList globals; Set.ofList xArgs; Set.ofList xRets; free_vars_specs enss]) in
  let ensAssume = List.collect (genAssume env prev) xfs in
  ss @ ensAssume
*)

///////////////////////////////////////////////////////////////////////////////
// Rewrite variables

let stateGet (env:env) (x:id):exp =
  match Map.find x env.ids with
  | StateInfo (prefix, es, t) -> vaApp_t ("get_" + prefix) (es @ [env.state]) (Some t)
  | _ -> internalErr "stateGet"

let refineOp (env:env) (io:inout) (x:id) (e:exp):exp =
  let abs_x = match (io, env.abstractOld) with (In, _) | (InOut, true) -> (old_id x) | (Out, _) | (InOut, false) -> x in
  eop RefineOp [evar x; evar abs_x; e]

let check_state_info (env:env) (x:id):bool = // returns readWrite
  match (env.checkMods, Map.tryFind x env.mods) with
  | (true, None) -> err ("variable " + (err_id x) + " must be declared in procedure's reads clause or modifies clause")
  | (false, None) -> true
  | (_, Some readWrite) -> readWrite

let check_state_info_mod (env:env) (x:id) (io:inout):unit =
  match (env.checkMods, io, check_state_info env x) with
  | (false, _, _) -> ()
  | (true, In, _) -> ()
  | (true, (InOut | Out), true) -> ()
  | (true, (InOut | Out), false) -> err ("variable " + (err_id x) + "must be declared in procedure's modifies clause")

let rewrite_state_info (env:env) (x:id) (prefix:string) (es:exp list):exp =
  let readWrite = check_state_info env x in
  refineOp env (if readWrite then InOut else In) x (stateGet env x)

let collect_mods (p:proc_decl):id list =
  let spec_mods (_, s) =
    match s with
    | Modifies (Modify, e) ->
      (
        match skip_loc (exp_abstract false e) with
        | EVar (x, _) -> [x]
        | _ -> []
      )
    | _ -> []
    in
  List.collect spec_mods p.pspecs

let check_mods (env:env) (p:proc_decl):unit =
  let check_spec (_, s) =
    match s with
    | Modifies (m, e) ->
      (
        match skip_loc (exp_abstract false e) with
        | EVar (x, _) ->
          (
            match (m, Map.tryFind x env.mods) with
            | (Read, None) -> err ("variable " + (err_id x) + " must be declared in reads clause or modifies clause")
            | ((Modify | Preserve), (None | Some false)) -> err ("variable " + (err_id x) + " must be declared in modifies clause")
            | (_, Some true) | (Read, Some false) -> ()
          )
        | _ -> ()
      )
    | _ -> ()
    in
  if env.checkMods then List.iter check_spec p.pspecs

type rewrite_context = { extra_lemma_calls:stmt list ref }
type rewrite_ctx = rewrite_context option

let rec rewrite_vars_arg (rctx:rewrite_ctx) (g:ghost) (asOperand:string option) (io:inout) (env:env) (e:exp):exp =
  let rec fe (env:env) (e:exp):exp map_modify =
    let codeLemma e = e
//      match asOperand with
//      | None -> e
//      | Some xo -> EOp (CodeLemmaOp, [vaApp "op" [e]; e]) // REVIEW -- should be more principled
      in
    let constOp e =
      let t = exp_typ e in
      let ec = EOp (Uop UConst, [e], t) in
      match asOperand with
      | None -> ec
      | Some xo -> codeLemma (EOp (RefineOp, [ec; ec; vaApp_t ("const_" + xo) [e] t], t))
      in
    let locs = locs_of_exp e in
    match (g, skip_loc e) with
    | (_, EVar (x, _)) when Map.containsKey x env.ids ->
      (
        let rec f x info =
          match info with
          // TODO: check for incorrect uses of old
          | GhostLocal _ -> Unchanged
          | InlineLocal _ -> (match g with NotGhost -> Replace (constOp e) | Ghost -> Unchanged)
          | OperandLocal (opIo, t) ->
            (
              let xo = vaTyp t in
              if env.checkMods then (match (opIo, io) with (_, In) | ((InOut | Out), _) -> () | (In, (InOut | Out)) -> err ("cannot pass 'in' operand as 'out'/'inout'"));
              match g with
              | Ghost -> Replace (refineOp env opIo x (vaEvalOp t env.state e))
              | NotGhost ->
                (
                  match asOperand with
                  | None -> Unchanged
                  | Some xoDst ->
                      let e = if xo = xoDst then e else vaApp_t ("coerce_" + xo + "_to_" + xoDst) [e] (Some (TName (Id xoDst))) in
                      Replace (EOp (OperandArg (x, xo, t), [e], (Some (TName (Id xoDst)))))
                )
            )
          | ThreadLocal {local_in_param = inParam; local_exp = e; local_typ = t} | ProcLocal {local_in_param = inParam; local_exp = e; local_typ = t} ->
              if inParam && io <> In then err ("variable " + (err_id x) + " must be out/inout to be passed as an out/inout argument") else
              Replace
                (match g with
                  | NotGhost -> codeLemma e
                  | Ghost ->
                      let getType t = match t with Some t -> t | None -> err ((err_id x) + " must have type annotation") in
                      let es = if inParam then evar (Reserved "old_s") else env.state in
                      vaEvalOp (getType t) es e)
          | StateInfo (prefix, es, t) ->
            (
              match (g, asOperand) with
              | (Ghost, _) -> Replace (rewrite_state_info env x prefix es)
              | (NotGhost, Some xo) ->
                  let readWrite = check_state_info_mod env x io in
                  Replace (eop (StateOp (x, xo + "_" + prefix, t)) es)
              | (NotGhost, None) -> err "this expression can only be passed to a ghost parameter or operand parameter"
            )
          | OperandAlias (x, info) -> f x info
          in
        f x (Map.find x env.ids)
      )
    | (NotGhost, EOp (Uop UConst, [ec], _)) -> Replace (constOp (rewrite_vars_exp rctx env ec))
    | (NotGhost, EInt _) -> Replace (constOp e)
    | (NotGhost, EApply (e, _, args, _)) when is_id e && asOperand <> None && Map.containsKey (operandProc (id_of_exp e) io) env.procs ->
      (
        let xa = id_of_exp e in
        let xa_in = operandProc xa In in
        let xa_out = operandProc xa Out in
        let get_p io =
          match io with
          | In | InOut ->
            if (not (Map.containsKey xa_in env.procs)) then err ("could not find procedure " + (err_id xa_in)) else
            let p_in = Map.find xa_in env.procs in
            let p_in = {p_in with prets = []} in
            check_mods env p_in;
            p_in
          | Out ->
            if (not (Map.containsKey xa_out env.procs)) then err ("could not find procedure " + (err_id xa_out)) else
            let p_out = Map.find xa_out env.procs in
            let p_out = {p_out with pargs = List.take (List.length p_out.pargs - 1) p_out.pargs} in
            check_mods env p_out;
            p_out
          in
        let p =
          match io with
          | In -> get_p In
          | InOut -> let _ = get_p Out in get_p In
          | Out -> get_p Out
          in
        let (lhss, es) = rewrite_vars_args rctx env p [] args in
        let ecs = List.collect (fun e -> match e with EOp (Uop UGhostOnly, [e], _) -> [] | _ -> [e]) es in
        let es = List.map (fun e -> match e with EOp (Uop UGhostOnly, [e], _) -> e | _ -> e) es in
        let xa_fc = Reserved ("opr_code_" + (string_of_id xa)) in
        let xa_fl = Reserved ("opr_lemma_" + (string_of_id xa)) in
        let eCode = eapply xa_fc ecs in
        if !fstar then
          let ofStateOp (e:exp):exp =
            match e with
            | EOp (StateOp (x, prefix, _), es, t) -> vaApp_t ("op_" + prefix) es t
            | _ -> e
            in
          let eLemma = eapply xa_fl (env.state::(List.map ofStateOp es)) in
          let sLemma = SAssign ([], eLemma) in
          let sLemma = match locs with [] -> sLemma | loc::_ -> SLoc (loc, sLemma) in
          match rctx with
          | None -> err "complex operand not supported here"
          | Some { extra_lemma_calls = calls } ->
              calls := sLemma::!calls;
              Replace (eop CodeLemmaOp [eCode; eCode])
        else
          let eLemma = eapply xa_fl (env.state::es) in
          Replace (eop CodeLemmaOp [eCode; eLemma])
      )
(*
    | (NotGhost, EOp (Subscript, [ea; ei])) ->
      (
        // Turn
        //   m[eax + 4]
        // into
        //   va_mem_lemma_HeapPublic(m, var_eax(), va_const_operand(4))
        match (skip_loc ea, skip_loc ei) with
        | (EVar xa, EOp (Bop BAdd, [eb; eo])) ->
            let ta = match Map.tryFind xa env.ids with Some (GhostLocal (Some (TName (Id ta)))) -> ta | _ -> err ("memory operand " + (err_id xa) + " must be a local ghost variable declared with a simple, named type") in
            let eb = rewrite_vars_arg rctx NotGhost None In env eb in
            let eo = rewrite_vars_arg rctx NotGhost None In env eo in
            let eCode = vaApp ("mem_code_" + ta) [eb; eo] in
            let eLemma = vaApp ("mem_lemma_" + ta) [ea; eb; eo] in
            Replace (EOp (CodeLemmaOp, [eCode; eLemma]))
        | _ -> err ("memory operand must have the form mem[base + offset] where mem is a variable")
      )
*)
    | (NotGhost, ECast(e, t)) -> Unchanged  // TODO: need to rewrite e
    | (NotGhost, _) ->
        err "unsupported expression (if the expression is intended as a load/store operand, try declaring 'operand_type x(...):...')"
        // Replace (codeLemma e)
    | (Ghost, EOp (Uop UToOperand, [e], _)) -> Replace (rewrite_vars_arg rctx NotGhost None io env e)
// TODO: this is a real error message, it should be uncommented
//    | (_, EApply (x, _, _)) when Map.containsKey x env.procs ->
//        err ("cannot call a procedure from inside an expression or variable declaration")
    | (Ghost, _) -> Unchanged
    in
  try
    env_map_exp_state fe env e
  with err -> (match locs_of_exp e with [] -> raise err | loc::_ -> raise (LocErr (loc, err)))
and rewrite_vars_exp (rctx:rewrite_ctx) (env:env) (e:exp):exp =
  rewrite_vars_arg rctx Ghost None In env e
and rewrite_vars_args (rctx:rewrite_ctx) (env:env) (p:proc_decl) (rets:lhs list) (args:exp list):(lhs list * exp list) =
  let (mrets, margs) = match_proc_args p rets args in
  let rewrite_arg (pp, ea) =
    match pp with
    | (x, t, XOperand, io, _) -> [rewrite_vars_arg rctx NotGhost (Some (vaTyp t)) io env ea]
    | (x, t, XInline, io, _) -> [(rewrite_vars_arg rctx Ghost None io env ea)]
    | (x, t, XAlias _, io, _) ->
        let _ = rewrite_vars_arg rctx NotGhost None io env ea in // check argument validity
        [] // drop argument
    | (x, t, XGhost, In, _) -> [(eop (Uop UGhostOnly) [rewrite_vars_exp rctx env ea])]
    | (x, t, XGhost, _, _) -> err ("out/inout ghost parameters are not supported")
    | (x, _, _, _, _) -> err ("unexpected argument for parameter " + (err_id x) + " in call to " + (err_id p.pname))
    in
  let rewrite_ret (pp, ((xlhs, _) as lhs)) =
    match pp with
    | (x, t, XOperand, _, _) -> ([], [rewrite_vars_arg rctx NotGhost (Some (vaOperandTyp t)) Out env (evar xlhs)])
    | (x, t, XAlias _, _, _) ->
        let _ = rewrite_vars_arg rctx NotGhost None Out env (evar xlhs) in // check argument validity
        ([], []) // drop argument
    | (x, t, XGhost, _, _) -> ([lhs], [])
    | (x, _, _, _, _) -> err ("unexpected variable for return value " + (err_id x) + " in call to " + (err_id p.pname))
    in
  let args = List.concat (List.map rewrite_arg margs) in
  let (retsR, retsA) = List.unzip (List.map rewrite_ret mrets) in
  (List.concat retsR, (List.concat retsA) @ args)

// Turn
//   ecx < 10
// into
//   va_cmp_lt(var_ecx(), va_const_operand(10))
// Turn
//   f(ecx, 10, ...)
// into
//   va_cmp_f(var_ecx(), va_const_operand(10), ...)
let rewrite_cond_exp (env:env) (e:exp):exp =
  let r = rewrite_vars_arg None NotGhost (Some "cmp") In env in
  match skip_loc e with
  | (EApply (e, _, es, t)) when is_id e -> vaApp_t ("cmp_" + string_of_id (id_of_exp e)) (List.map r es) t
  | (EOp (op, es, t)) ->
    (
      match (op, es) with
      | (Bop (BEq _), [e1; e2]) -> vaApp_t "cmp_eq" [r e1; r e2] t
      | (Bop (BNe _), [e1; e2]) -> vaApp_t "cmp_ne" [r e1; r e2] t
      | (Bop BLe, [e1; e2]) -> vaApp_t "cmp_le" [r e1; r e2] t
      | (Bop BGe, [e1; e2]) -> vaApp_t "cmp_ge" [r e1; r e2] t
      | (Bop BLt, [e1; e2]) -> vaApp_t "cmp_lt" [r e1; r e2] t
      | (Bop BGt, [e1; e2]) -> vaApp_t "cmp_gt" [r e1; r e2] t
      | _ -> err ("conditional expression must be a comparison operation or function call")
    )
  | _ -> err ("conditional expression must be a comparison operation or function call")

let rec rewrite_vars_assign (rctx:rewrite_ctx) (env:env) (lhss:lhs list) (e:exp):(lhs list * exp) =
  match (lhss, e) with
  | (_, ELoc (loc, e)) ->
      try let (lhss, e) = rewrite_vars_assign rctx env lhss e in (lhss, ELoc (loc, e))
      with err -> raise (LocErr (loc, err))
  | (_, EApply(xe, ts, es, t)) when is_id xe ->
    (
      let x = id_of_exp xe in
      match Map.tryFind x env.procs with
      | None | Some {pghost = Ghost} -> (lhss, rewrite_vars_exp rctx env e)
      | Some p ->
          check_mods env p;
          let (lhss, args) = rewrite_vars_args rctx env p lhss es in
          (lhss, EApply(evar x, ts, args, t))
    )
  | _ -> (lhss, rewrite_vars_exp rctx env e)

let check_lhs (env:env) (x:id, dOpt):unit =
  match (x, dOpt) with
  | (Reserved "this", None) -> ()
  | (_, None) ->
    (
      match Map.tryFind x env.ids with
      | None -> err ("cannot find variable '" + (err_id x) + "'")
      | Some (GhostLocal (Immutable, _)) -> err ("cannot assign to immutable variable '" + (err_id x) + "'")
      | _ -> ()
    )
  | (_, Some _) -> ()

let rewrite_vars_stmt (env:env) (s:stmt):(env * stmt list) =
  let rec fs (env:env) (s:stmt):(env * stmt list) map_modify =
    match s with
    | SAssign (lhss, e) ->
        List.iter (check_lhs env) lhss;
        let lhss = List.map (fun xd -> match xd with (Reserved "this", None) -> (Reserved "s", None) | _ -> xd) lhss in
        let rctx = { extra_lemma_calls = ref [] } in
        let (lhss, e) = rewrite_vars_assign (Some rctx) env lhss e in
        Replace (env, (List.rev !rctx.extra_lemma_calls) @ [SAssign (lhss, e)])
    | SIfElse (SmPlain, e, b1, b2) ->
        let b1 = env_map_stmts (rewrite_vars_exp None) fs env b1 in
        let b2 = env_map_stmts (rewrite_vars_exp None) fs env b2 in
        Replace (env, [SIfElse (SmPlain, rewrite_cond_exp env e, b1, b2)])
    | SWhile (e, invs, ed, b) ->
        let invs = List_mapSnd (rewrite_vars_exp None env) invs in
        let ed = mapSnd (List.map (rewrite_vars_exp None env)) ed in
        let b = env_map_stmts (rewrite_vars_exp None) fs env b in
        Replace (env, [SWhile (rewrite_cond_exp env e, invs, ed, b)])
    | _ -> Unchanged
    in
  env_map_stmt (rewrite_vars_exp None) fs env s
let rewrite_vars_stmts (env:env) (ss:stmt list):stmt list =
  List.concat (snd (List_mapFoldFlip rewrite_vars_stmt env ss))

// Turn SpecRaw into Requires/Ensures/Modifies
// Compute env.lets
// Remove Lets from specs (replace with local let expressions)
// Directly substitute LetsAlias into Modifies (because we don't have let expressions for modifies)
let desugar_spec (env:env) ((loc:loc), (s:spec)):(env * (loc * spec) list) map_modify =
  match s with
  | Requires _ | Ensures _ | Modifies _ -> internalErr "desugar_spec"
  | SpecRaw (RawSpec (r, es)) ->
    (
      let es = exps_of_spec_exps es in
      let let_of_lets (old:bool) (loc:loc, l:lets):(loc * bindOp * formal * exp) =
        let fOld old e = if old then eop (Uop UOld) [e] else e in
        match l with
        | LetsVar (x, t, e) -> (loc, BindLet, (x, t), fOld old e)
        | LetsAlias (x, y) -> (loc, BindAlias, (x, None), evar y)
        in
      let applyLets old =
        match env.lets with
        | [] -> List.map (fun (l, e) -> (l, ELabel(l, e))) es
        | lets ->
            let e = and_of_list (List.map (fun (l, e) -> ELabel (l, e)) es) in
            let lets = List.map (let_of_lets old) lets in
            let addLet e (loc, bind, (x, t), ee) = ELoc (loc, ebind bind [ee] [(x, t)] [] e) in
            let e = List.fold addLet e lets in
            [(loc, e)]
        in
      let reqs refined = List_mapSnd (fun e -> Requires (refined, e)) (applyLets false) in
      let enss refined = List_mapSnd (fun e -> Ensures (refined, e)) (applyLets true) in
      match r with
      | RRequires refined -> Replace (env, reqs refined)
      | REnsures refined -> Replace (env, enss refined)
      | RRequiresEnsures -> Replace (env, (reqs Refined) @ (enss Refined))
      | RModifies m ->
          let rewrite env e =
            match e with
            | EVar (x, _) when Map.containsKey x env.ids ->
              (
                let rec f x info =
                  match info with
                  | OperandAlias (x, info) -> f x info
                  | _ -> Replace (evar x)
                  in
                f x (Map.find x env.ids)
              )
            | _ -> Unchanged
            in
          let mods m = List_mapSnd (fun e -> Modifies (m, env_map_exp_state rewrite env e)) es in
          Replace (env, mods m)
    )
  | SpecRaw (Lets _) -> PostProcess (fun (env, _) -> (env, []))

let rewrite_vars_spec (envIn:env) (envOut:env) (s:spec):spec =
  match s with
  | Requires (r, e) -> Requires (r, rewrite_vars_exp None envIn e)
  | Ensures (r, e) -> Ensures (r, rewrite_vars_exp None envOut e)
  | Modifies (m, e) -> Modifies (m, rewrite_vars_exp None envOut e)
  | SpecRaw _ -> internalErr "rewrite_vars_spec"

let resolve_overload_spec (envIn:env) (envOut:env) (s:spec):spec =
  match s with
  | Requires (r, e) -> Requires (r, resolve_overload_expr envIn e)
  | Ensures (r, e) -> Ensures (r, resolve_overload_expr envOut e)
  | Modifies (m, e) -> Modifies (m, resolve_overload_expr envOut e)
  | SpecRaw _ -> internalErr "resolve_overload_spec"

let check_no_duplicates (es:(loc * exp) list):unit =
  let sls = List.map (fun (l, e) -> (Emit_vale_text.string_of_exp e, one_loc_of_exp l e)) es in
  let ss = List.map fst sls in
  let ss = List.sort ss in
  let rec f ss =
    match ss with
    | [] -> ()
    | h1::h2::_ when h1 = h2 ->
        let err = Err ("duplicate read/modify declaration: " + h1) in
        raise (LocErr (List_assoc h1 (List.rev sls), err))
    | _::t -> f t
    in
  f ss

///////////////////////////////////////////////////////////////////////////////
// Add quick blocks for assert{:quick_start}...assert{:quick_end}

let is_assert_quick_start (s:stmt):bool =
  match skip_loc_stmt s with
  | SAssert ({is_quickstart = true}, e) ->
    (
      match skip_loc e with
      | EBool true -> true
      | _ -> false
    )
  | _ -> false

let is_assert_quick_end (s:stmt):bool =
  match skip_loc_stmt s with
  | SAssert ({is_quickend = true}, e) ->
    (
      match skip_loc e with
      | EBool true -> true
      | _ -> false
    )
  | _ -> false

let rec collect_mods_assign (env:env) (lhss:lhs list) (e:exp):id list =
  match e with
  | ELoc (loc, e) ->
      try collect_mods_assign env lhss e
      with err -> raise (LocErr (loc, err))
  | EApply(e, _, es, _) when is_id e ->
    (
      let x = id_of_exp e in
      match Map.tryFind x env.procs with
      | None -> []
      | Some p ->
          let fArg e =
            match skip_loc e with
            | EOp (StateOp (x, _, _), _, _) -> [x]
            | _ -> []
            in
          let xsOut = List.collect fArg es in
          xsOut @ (collect_mods p)
    )
  | _ -> []

let collect_mods_stmts (env:env) (ss:stmt list):id list =
  let fe (e:exp) (mods:id list list):id list = List.concat mods in
  let fs (s:stmt) (mods:id list list):id list =
    match s with
    | SAssign (lhss, e) -> List.concat ((collect_mods_assign env lhss e)::mods)
    | _ -> List.concat mods
    in
  let mods = gather_stmts fs fe ss in
  Set.toList (Set.ofList (List.concat mods))

let rec add_quick_blocks_stmt (env:env) (next_sym:int ref) (s:stmt):stmt =
  let r = add_quick_blocks_stmt env next_sym in
  let rs = add_quick_blocks_stmts env next_sym in
  match s with
  | SLoc (loc, s) -> SLoc (loc, r s)
  | SLabel _ | SGoto _ | SReturn | SAssume _ | SAssert _ | SAssign _ | SCalc _ | SVar _ | SAlias _ | SForall _ | SExists _-> s
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SQuickBlock _ -> internalErr "SQuickBlock"
  | SBlock b -> SBlock (rs b)
  | SIfElse (g, e, b1, b2) -> SIfElse (g, e, rs b1, rs b2)
  | SWhile (e, invs, ed, b) -> SWhile (e, invs, ed, rs b)
and collect_quick_blocks_stmts (env:env) (next_sym:int ref) (ss:stmt list):(stmt list * stmt list) =
  match ss with
  | [] -> ([], [])
  | s::ss when is_assert_quick_end s -> ([], ss)
  | s::ss ->
      let (ss1, ss2) = collect_quick_blocks_stmts env next_sym ss in
      (s::ss1, ss2)
and add_quick_blocks_stmts (env:env) (next_sym:int ref) (ss:stmt list):stmt list =
  match ss with
  | [] -> []
  | s::ss when is_assert_quick_start s ->
      incr next_sym;
      let sym = string !next_sym in
      let (ss1, ss2) = collect_quick_blocks_stmts env next_sym ss in
      let info = {qsym = sym; qmods = collect_mods_stmts env ss1} in
      (SQuickBlock (info, ss1))::(add_quick_blocks_stmts env next_sym ss2)
  | s::ss -> (add_quick_blocks_stmt env next_sym s)::(add_quick_blocks_stmts env next_sym ss)

let add_quick_type_stmts (ss:stmt list):stmt list =
  let sym = ref 0 in
  let fs (s:stmt) =
    match s with
    | SAssert ({is_quicktype = true}, e) ->
        incr sym;
        let x = Reserved ("u" + (string !sym)) in
        Replace [SAssign ([(x, Some (None, Ghost))], eapply (Id "AssertQuickType") [e])]
    | _ -> Unchanged
    in
  map_stmts (fun e -> e) fs ss

///////////////////////////////////////////////////////////////////////////////
// Hoist while loops into top-level procedures

let hoist_while_loops (env:env) (loc:loc) (p:proc_decl):decl list =
  let hoisted = ref ([]:decl list) in
  let hoist_while env s =
    match s with
    | SWhile _ ->
      (*
        procedure{:quick true} body_p(ins_in) returns(outs)
          lets L
          reads R modifies M
          requires invs(ins_in)
          ensures invs(ins_in,outs)
          requires e(ins_in)
          ensures ed(ins_in,outs) << old(ed(ins_in))
          { ins := ins_in; b }
        procedure{:quick false} while_p(ins_in) returns(outs)
          lets L
          reads R modifies M
          requires invs(ins_in)
          ensures invs(ins_in,outs)
          ensures !e(ins_in,outs)
          { ins := ins_in; while(e) invs ed { outs := body_p(ins); } }
        procedure{:quick true} p(...) ...
        {
          ... outs := while_p(ins); ...
        }
      *)
        let xp_body = body_id p.pname in
        let xp_while = while_id p.pname in
        let (_, raw_reads, raw_readsOld, raw_mods) = compute_read_mods_stmt env empty_env s in
        let mods = Set.map (resolve_alias env) raw_mods in
        let reads = Set.map (resolve_alias env) raw_reads in
        let readsOld = Set.map (resolve_alias env) raw_readsOld in
        // each read/mod is one of: (ghost/inline), state
        // move (ghost/inline) readsOld into reads, keep state in readsOld
        let find_var (x:id):id_info =
          match Map.tryFind x env.ids with
          | None -> err ("could not find variable " + (err_id x))
          | Some info -> info
          in
        let resolve_find_var (x:id):id_info = find_var (resolve_alias env x) in
        let is_state (x:id):bool = match resolve_find_var x with StateInfo _ -> true | _ -> false in
        let is_alias (x:id):bool = match find_var x with OperandAlias _ -> true | _ -> false in
        let (readsOld, reads2) = Set.partition is_state readsOld in
        let reads = Set.union reads reads2 in
        let reads = Set.difference reads mods in
        //   L = reads state via alias + mods state via alias
        //   R = reads state
        //   M = mods state
        //   ins = reads (ghost/inline) + mods (ghost/inline) + readsOld
        //   outs = mods (ghost/inline)
        let (p_reads, in_reads) = List.partition is_state (Set.toList reads) in
        let (p_mods, outs) = List.partition is_state (Set.toList mods) in
        let aliases = List.filter is_alias (Set.toList (Set.union raw_reads raw_mods)) in
        let ins = in_reads @ outs in
        let in_id (x:id) : id =
          // REVIEW: consistently apply or not apply in_id?
          match find_var x with
          | InlineLocal _ -> x
          | _ -> in_id x
          in
        let ins_in = List.map in_id ins in
        let s_old = Reserved "old" in
        let rec replace_old (e:exp):exp map_modify =
          match e with
          | EOp (Uop UOld, [e], t) -> Replace (EOp (Bop BOldAt, [evar s_old; map_exp replace_old e], t))
          | _ -> Unchanged
          in
        let s = map_stmt (map_exp replace_old) (fun _ -> Unchanged) s in
        let (eCond, invs, ed, b) =
          match s with
          | [SWhile (e, invs, ed, b)] -> (e, invs, ed, b)
          | _ -> internalErr "hoist_while_loops"
          in
        let getType (x:id):typ =
          match resolve_find_var x with
          | GhostLocal (_, None) | InlineLocal None -> err ("variable " + (err_id x) + " needs explicit type annotation to use inside while loop")
          | GhostLocal (_, Some t) | InlineLocal (Some t) -> t
          | StateInfo (_, _, t) -> t
          | _ -> err ("variables in while loops must be ghost, inline, or state component: " + (err_id x))
          in
        let to_pformal (x:id):pformal = (x, getType x, XGhost, In, []) in
        let to_pformal_in (x:id):pformal =
          let storage = match find_var x with InlineLocal _ -> XInline | _ -> XGhost in
          (in_id x, getType x, storage, In, [])
          in
        let pf_state = (s_old, tState, XGhost, In, [(Reserved "expand_state", [])]) in
        let p_ins_in = List.map to_pformal_in ins in
        let p_outs = List.map to_pformal outs in
        let subst_ins (ins:id list) (e:exp) =
          let m = Map.ofList (List.map (fun x -> (x, evar (in_id x))) ins) in
          subst_reserved_exp m e
          in
        let alias_to_spec (x:id) =
          match find_var x with
          | OperandAlias (y, _) -> (loc, SpecRaw (Lets [(loc, LetsAlias (x, y))]))
          | _ -> internalErr "alias_to_spec"
          in
        let inv_to_spec (ins:id list) (k:raw_spec_kind) ((l:loc), (e:exp)) =
          let e = subst_ins ins e in
          (l, SpecRaw (RawSpec (k, [(l, SpecExp e)])))
          in
        let mod_to_spec (m:mod_kind) (x:id) =
          (loc, SpecRaw (RawSpec (RModifies m, [(loc, SpecExp (evar x))])))
          in
        let reqs = List.map (inv_to_spec ins (RRequires Unrefined)) invs in
        let enss = List.map (inv_to_spec in_reads (REnsures Unrefined)) invs in
        let spec_aliases = List.map alias_to_spec aliases in
        let spec_reads = List.map (mod_to_spec Read) p_reads in
        let spec_mods = List.map (mod_to_spec Modify) p_mods in
        let specs = spec_aliases @ spec_reads @ spec_mods @ reqs @ enss in
        let e_exit = eop (Uop (UNot BpProp)) [eCond] in
        let spec_exit = inv_to_spec in_reads (REnsures Unrefined) (loc, e_exit) in
        let spec_enter_body = inv_to_spec ins (RRequires Unrefined) (loc, eCond) in
        // ed << old(ed)
        // precedes(ed, old(ed))
        let lexList (es:exp list) = List.foldBack (fun e ls -> eapply (Id "lexCons") [e; ls]) es (evar (Id "LexTop")) in
        let (lEd, eds) = ed in
        let edIn = eop (Uop UOld) [subst_ins ins (lexList eds)] in
        let edOut = subst_ins in_reads (lexList eds) in
        let precedes = eapply (Id "precedes_wrap") [edOut; edIn] in
        let spec_precedes = inv_to_spec [] (REnsures Unrefined) (lEd, precedes) in
        let sInitIn (x:id) = SVar (x, Some (getType x), Mutable, XGhost, [], Some (evar (in_id x))) in
        let sInitOut (x:id) = SAssign ([(x, None)], (evar (in_id x))) in
        let in_reads_init = List.filter (fun x -> match find_var x with InlineLocal _ -> false | _ -> true) in_reads in
        let sInits = List.map sInitIn in_reads_init @ List.map sInitOut outs in
        // while(e) invs ed { outs := body_p(ins); }
        let lhss = List.map (fun x -> (x, None)) outs in
        let args = (List.map evar ins) in
        let oldThis = eop (Uop UOld) [evar (Reserved "this")] in
        let callBody = SAssign (lhss, eapply xp_body ((evar s_old)::args)) in
        let callWhile = SAssign (lhss, eapply xp_while (oldThis::args)) in
        let sWhile = SWhile (eCond, invs, ed, [callBody]) in
        let p_body =
          {
            pname = xp_body;
            pghost = NotGhost;
            pinline = Inline;
            ptargs = p.ptargs;
            pargs = pf_state::p_ins_in;
            prets = p_outs;
            pspecs = specs @ [spec_enter_body; spec_precedes];
            pbody = Some (sInits @ b);
            // always non-public, even if they are generated from the body of a public procedure
            pattrs = [(Id "public", [EBool false]); (Id "already_has_mod_ok", [])] @ p.pattrs;
          }
          in
        let p_while =
          {
            pname = xp_while;
            pghost = NotGhost;
            pinline = Inline;
            ptargs = p.ptargs;
            pargs = pf_state::p_ins_in;
            prets = p_outs;
            pspecs = specs @ [spec_exit];
            pbody = Some (sInits @ [sWhile]);
            pattrs = [(Id "quick", [evar (Id "exportOnly")]); (Id "already_has_mod_ok", [])];
          }
          in
        hoisted := (DProc p_while)::(DProc p_body)::!hoisted;
        Replace (env, [callWhile])
    | _ -> Unchanged
    in
  let body =
    match p.pbody with
    | None -> None
    | Some ss -> Some (env_map_stmts (fun env e -> e) hoist_while env ss)
    in
  if !hoisted = [] then
    []
  else
    let ds = List.rev (DProc {p with pbody = body}::!hoisted) in
    //Emit_vale_text.emit_decls (debug_print_state ()) (List.map (fun d -> (loc, d)) ds);
    ds

///////////////////////////////////////////////////////////////////////////////

type transformed =
| TransformedDone of (env * env * proc_decl) * env
| TransformedRetry of decl list

// Either transform p, or return a list of decls that then must be transformed
let transform_proc (env:env) (loc:loc) (p:proc_decl):transformed =
  let isFrame = attrs_get_bool (Id "frame") (p.pghost = NotGhost) p.pattrs in
  let isRecursive = attrs_get_bool (Id "recursive") false p.pattrs in
  let isInstruction = List_mem_assoc (Id "instruction") p.pattrs in
  let isAlreadyModOk = List_mem_assoc (Id "already_has_mod_ok") p.pattrs in
  let isQuick = is_quick_body p.pattrs in
  let preserveSpecs =
    List.collect
      (fun spec ->
        match spec with
        | (_, SpecRaw (RawSpec (RModifies Preserve, es))) ->
            let es = List.collect (fun (loc, e) -> match e with SpecExp e -> [(loc, e)] | SpecLet _ -> []) es in
            List_mapSnd (fun e -> SpecExp (eop (Bop (BEq BpProp)) [e; eop (Uop UOld) [e]])) es
        | _ -> []
      )
      p.pspecs
    in
  let ok = evar (Id "ok") in
  let okMod = SpecRaw (RawSpec (RModifies Preserve, [(loc, SpecExp ok)])) in
  let okReqEns = SpecRaw (RawSpec (RRequiresEnsures, [(loc, SpecExp ok)])) in
  let okSpecs = (if isAlreadyModOk then [] else [(loc, okMod)]) @ [(loc, okReqEns)] in
  let pspecs = if isFrame then okSpecs @ p.pspecs else p.pspecs in
  let pspecs = match preserveSpecs with [] -> pspecs | _ -> pspecs @ [(loc, SpecRaw (RawSpec (REnsures Unrefined, preserveSpecs)))] in
  let addParam isRet ids (x, t, g, io, a) =
    match g with
    | (XAlias (AliasThread, e)) -> Map.add x (ThreadLocal {local_in_param = (io = In && (not isRet)); local_exp = e; local_typ = Some t}) ids
    | (XAlias (AliasLocal, e)) -> Map.add x (ProcLocal {local_in_param = (io = In && (not isRet)); local_exp = e; local_typ = Some t}) ids
    | XInline -> Map.add x (InlineLocal (Some t)) ids
    | XOperand -> Map.add x (OperandLocal (io, t)) ids
    | XPhysical | XState _ -> err ("variable must be declared ghost, operand, {:local ...}, or {:register ...} " + (err_id x))
    | XGhost -> Map.add x (GhostLocal ((if isRet then Mutable else Immutable), Some t)) ids
    in
  let mod_id (env:env) (loc, m, e) =
    let mod_err () = err "expression in modifies clause must be a variable declared as var{:state f(...)} x:t;"
    loc_apply loc e (fun e ->
      match e with
      | EVar (x, _) ->
        (
          match Map.tryFind x env.ids with
          | None -> err ("cannot find variable " + (err_id x))
          | Some (StateInfo _) -> (x, (match m with Read -> false | (Modify | Preserve) -> true))
          | Some _ -> mod_err ()
        )
      | _ -> mod_err ())
    in
  // parameters, return values, lets must all be unique
  let xArgsRets = List.map (fun (x, _, _, _, _) -> x) (p.pargs @ p.prets) in
  let specs = List.collect (fun (loc, s) -> match s with SpecRaw s -> [(loc, s)] | _ -> internalErr "!SpecRaw") pspecs in
  let lets = List.collect (fun (_, s) -> match s with (Lets ls) -> ls | _ -> []) specs in
  let xLets = List.map (fun (_, s) -> match s with LetsVar (x, _, _) | LetsAlias (x, _) -> x) lets in
  let rec checkUnique xs xset =
    match xs with
    | [] -> ()
    | x::xs ->
        if Set.contains x xset then err ("'" + (err_id x) + "' declared twice") else
        checkUnique xs (Set.add x xset)
    in
  checkUnique (xArgsRets @ xLets) (Set.empty);
  let envpIn = env in
  // Add parameters to env for both requires and ensures.
  // For ensures, add return values to env.
  // For requires, remove return values from env -- for each return value named x, remove any
  // globals named x, so that requires and ensures don't see two different x variables.
  // This makes it sane to share "lets" declarations between requires and ensures.
  let envpIn = {envpIn with ids = List.fold (addParam false) envpIn.ids p.pargs} in
  let envpIn = {envpIn with ids = List.fold (fun ids (x, _, _, _, _) -> Map.remove x ids) envpIn.ids p.prets} in
  // Desugar specs and update p so other procedures see desugared version
  let (envDesugar, pspecs) = env_map_specs (fun _ e -> e) desugar_spec envpIn pspecs in
  let lets = List.rev envDesugar.lets in
  let bodyLet (loc:loc, l:lets) =
    match l with
    | LetsVar (x, t, e) -> SLoc (loc, SVar (x, t, Immutable, XGhost, [], Some e))
    | LetsAlias (x, y) -> SLoc (loc, SAlias (x, y))
    in
  let bodyLets = List.map bodyLet lets in
  let body = mapOpt (fun ss -> bodyLets @ ss) p.pbody in
  let pOrig = p in
  let p = {p with pbody = body; pspecs = pspecs} in
  // Compute mods list and final environment for body
  let mods = List.collect (fun (loc, s) -> match s with Modifies (m, e) -> [(loc, m, e)] | _ -> []) pspecs in
  check_no_duplicates (List.map (fun (_, _, e) -> (loc, e)) mods);
  let envpIn = {envpIn with mods = Map.ofList (List.map (mod_id envpIn) mods)} in
  let envpIn = {envpIn with abstractOld = true} in
  let envp = envpIn in
  let envp = {envp with ids = List.fold (addParam true) envp.ids p.prets} in
  let envp = {envp with checkMods = isFrame} in
  let envp = {envp with abstractOld = false} in
  let specs = List_mapSnd (rewrite_vars_spec envpIn envp) pspecs in
  let specs = List_mapSnd (resolve_overload_spec envpIn envp) specs in
  let envp = if isRecursive then {envp with procs = Map.add p.pname {p with pspecs = specs} envp.procs} else envp in
  let env = {env with raw_procs = Map.add p.pname p env.raw_procs}
  // Hoist while loops
  let envpOrig = List.fold (fun env s -> snd (env_stmt env s)) envp bodyLets in
  let hoisted = if isQuick then hoist_while_loops envpOrig loc pOrig else [] in
  if hoisted <> [] then TransformedRetry hoisted else
  // Process body
  let body =
    match p.pbody with
    | None -> None
    | Some ss ->
        let rec add_while_ok s =
          match s with
          | SWhile (e, invs, ed, b) ->
              let invs = (loc, evar (Id "ok"))::invs in
              Replace [SWhile (e, invs, ed, map_stmts (fun e -> e) add_while_ok b)]
          | _ -> Unchanged
          in
        let ss = if isFrame then map_stmts (fun e -> e) add_while_ok ss else ss in
        let ss = resolve_overload_stmts envp ss in
        //let ss = assume_updates_stmts envp p.pargs p.prets ss (List.map snd pspecs) in
        let ss = add_quick_type_stmts ss in
        let ss = rewrite_vars_stmts envp ss in
        let ss = add_quick_blocks_stmts envp (ref 0) ss in
        Some ss
    in
  let pNew = {p with pbody = body; pspecs = specs} in
  let envBody = envp in
  let envProc = {env with procs = Map.add p.pname pNew env.procs} in
  let envRec = if isRecursive then envProc else env in
  TransformedDone ((envRec, envBody, pNew), envProc)

// returns:
//   - list of:
//     - minimal env for procedure body (for procedures)
//     - expanded env for procedure body (for procedures)
//     - transformed declaration
//   - env for subsequent declarations
let rec transform_decl (env:env) (loc:loc) (d:decl):((env * env * decl) list * env) =
  match d with
  | DVar (x, t, XAlias (AliasThread, e), _) ->
      let env = {env with ids = Map.add x (ThreadLocal {local_in_param = false; local_exp = e; local_typ = Some t}) env.ids} in
      ([(env, env, d)], env)
  | DVar (x, t, XState e, _) ->
    (
      match skip_loc e with
      | EApply (e, _, es, _) when is_id e ->
          let env = {env with ids = Map.add x (StateInfo (string_of_id (id_of_exp e), es, t)) env.ids} in
          ([(env, env, d)], env)
      | _ -> err ("declaration of state member " + (err_id x) + " must provide an expression of the form f(...args...)")
    )
  | DFun ({fbody = None} as f) ->
      ([], {env with funs = Map.add f.fname f env.funs})
  | DProc p ->
    (
      match transform_proc env loc p with
      | TransformedDone ((envRec, envBody, pNew), envProc) -> ([envRec, envBody, DProc pNew], envProc)
      | TransformedRetry ds ->
          let f env d = let (eds, env) = transform_decl env loc d in (env, eds) in
          let (env, eds) = List_mapFoldFlip f env ds in
          (List.concat eds, env)
    )
  | _ -> ([(env, env, d)], env)


