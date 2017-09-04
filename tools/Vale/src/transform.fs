// Make local transformations on operands and overloaded terms:
//   - resolve overloading
//   - turn operands into appropriate ghost variables
//   - turn references to operands into appropriate ghost variables
//   - insert some diagnostic assertions for {:refined true}
// Mostly, this is about changing expressions and arguments

module Transform

open Ast
open Ast_util
open Parse
open Microsoft.FSharp.Math

let assumeUpdates = ref 0

type id_local = {local_in_param:bool; local_exp:exp; local_typ:typ option} // In parameters are read-only and refer to old(state)
type id_info =
| GhostLocal of mutability * typ option
| ProcLocal of id_local
| ThreadLocal of id_local
| InlineLocal
| OperandLocal of inout * string * typ
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
    state = EVar (Reserved "s");
    abstractOld = false;
    checkMods = false;
  }

let vaApp (s:string) (es:exp list):exp = EApply (Reserved s, es)

let vaAppOp (prefix:string) (t:typ) (es:exp list):exp =
  match t with
  | TName (Id x) -> vaApp (qprefix prefix x) es
  | _ -> err "operands must have simple named types"

let vaEvalOp (xo:string) (t:typ) (state:exp) (e:exp):exp =
  match t with
  | TName (Id x) -> vaApp (qprefix ("eval_" + xo + "_") x) [state; e]
  | _ -> err "operands must have simple named types"

let old_id (x:id) = Reserved ("old_" + (string_of_id x))
let prev_id (x:id) = Reserved ("prev_" + (string_of_id x))

let tBool = TName (Reserved "bool")
let tInt = TName (Reserved "int")
let tOperand xo = TName (Reserved xo)
let tState = TName (Reserved "state")
let tCode = TName (Reserved "code")
let tCodes = TName (Reserved "codes")

let exp_abstract (useOld:bool) (e:exp):exp =
  let c e = match e with EOp (Uop UConst, [e]) -> e | _ -> e in
  map_exp (fun e -> match e with EOp (RefineOp, [e1; e2; e3]) -> Replace (if useOld then c e2 else c e1) | _ -> Unchanged) e

let exp_refined (e:exp):exp =
  map_exp (fun e -> match e with EOp (RefineOp, [e1; e2; e3]) -> Replace e3 | _ -> Unchanged) e

let stmts_abstract (useOld:bool) (ss:stmt list):stmt list =
  map_stmts (exp_abstract useOld) (fun _ -> Unchanged) ss

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
    | EVar (Reserved "this") -> env.state
    | EVar _ | EInt _ | EReal _ | EBitVector _ | EBool _ | EString _ -> e
    | EBind (b, es, fs, ts, e) ->
        let es = List.map r es in
        let env =
          match (b, List.map (exp_abstract false) es, fs) with
          | (BindAlias, [EVar y], [(x, t)]) ->
              {env with ids = Map.add x (make_operand_alias y env) env.ids}
          | (BindAlias, _, _) -> internalErr (sprintf "BindAlias %A %A" es fs)
          | (_, _, _) ->
              {env with ids = List.fold (fun env (x, t) -> Map.add x (GhostLocal (Immutable, t)) env) env.ids fs}
          in
        let r = env_map_exp f env in
        EBind (b, es, fs, List.map (List.map r) ts, r e)
    | EOp (Uop UOld, [e]) ->
        let env = {env with state = EVar (Reserved "old_s"); abstractOld = true} in
        let r = env_map_exp f env in
        r e
    | EOp (Bop BOldAt, [es; e]) ->
        let env = {env with state = es} in
        let r = env_map_exp f env in
        r e
    | EOp (op, es) -> EOp (op, List.map r es)
    | EApply (x, es) -> EApply (x, List.map r es)
  )

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
    | SCalc (oop, contents) -> (env, [SCalc (oop, List.map (env_map_calc_contents fe fs env) contents)])
    | SVar (x, t, m, g, a, eOpt) ->
      (
        let info =
          match g with
          | XAlias (AliasThread, e) -> ThreadLocal {local_in_param = false; local_exp = e; local_typ = t}
          | XAlias (AliasLocal, e) -> ProcLocal {local_in_param = false; local_exp = e; local_typ = t}
          | XGhost -> GhostLocal (m, t)
          | XInline -> InlineLocal
          | (XOperand _ | XPhysical | XState _) -> err ("variable must be declared ghost, {:local ...}, or {:register ...} " + (err_id x))
          in
        let ids = Map.add x info env.ids in
        ({env with ids = ids}, [SVar (x, t, m, g, map_attrs fee a, mapOpt fee eOpt)])
      )
    | SAlias (x, y) ->
        let ids = Map.add x (make_operand_alias y env) env.ids in
        ({env with ids = ids}, [SAlias (x, y)])
    | SAssign (xs, e) ->
        let ids = List.fold (fun ids (x, dOpt) -> match dOpt with None -> ids | Some (t, _) -> Map.add x (GhostLocal (Mutable, t)) ids) env.ids xs in
        ({env with ids = ids}, [SAssign (xs, fee e)])
    | SBlock b -> (env, [SBlock (rs b)])
    | SIfElse (g, e, b1, b2) -> (env, [SIfElse (g, fee e, rs b1, rs b2)])
    | SWhile (e, invs, ed, b) ->
        (env, [SWhile (fee e, List_mapSnd fee invs, mapSnd (List.map fee) ed, rs b)])
    | SForall (xs, ts, ex, e, b) ->
        let env = {env with ids = List.fold (fun env (x, t) -> Map.add x (GhostLocal (Immutable, t)) env) env.ids xs} in
        let fee = fe env in
        let rs = env_map_stmts fe fs env in
        (env, [SForall (xs, List.map (List.map fee) ts, fee ex, fee e, rs b)])
    | SExists (xs, ts, e) ->
        let env = {env with ids = List.fold (fun env (x, t) -> Map.add x (GhostLocal (Immutable, t)) env) env.ids xs} in
        let fee = fe env in
        (env, [SExists (xs, List.map (List.map fee) ts, fee e)])
  )
and env_map_stmts (fe:env -> exp -> exp) (fs:env -> stmt -> (env * stmt list) map_modify) (env:env) (ss:stmt list):stmt list =
  List.concat (snd (List_mapFoldFlip (env_map_stmt fe fs) env ss))
and env_map_calc_contents (fe:env -> exp -> exp) (fs:env -> stmt -> (env * stmt list) map_modify) (env:env)  (cc:calcContents) =
  let {calc_exp = e; calc_op = oop; calc_hints = hints} = cc in
  {calc_exp = fe env e; calc_op = oop; calc_hints = List.map (env_map_stmts fe fs env) hints}

let env_next_stmt (env:env) (s:stmt):env =
  let (env, _) = env_map_stmt (fun _ e -> e) (fun _ _ -> Unchanged) env s in
  env

let env_map_spec (fe:env -> exp -> exp) (fs:env -> loc * spec -> (env * (loc * spec) list) map_modify) (env:env) ((loc:loc), (s:spec)):(env * (loc * spec) list) =
  map_apply_modify (fs env (loc, s)) (fun () ->
    let fee = fe env in
    match s with
    | Requires (r, e) -> (env, [(loc, Requires (r, fee e))])
    | Ensures (r, e) -> (env, [(loc, Ensures (r, fee e))])
    | Modifies (b, e) -> (env, [(loc, Modifies (b, fee e))])
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

let match_proc_args (env:env) (p:proc_decl) (rets:lhs list) (args:exp list):((pformal * lhs) list * (pformal * exp) list) =
  let (nap, nac) = (List.length p.pargs, List.length args) in
  let (nrp, nrc) = (List.length p.prets, List.length rets) in
  if nap <> nac then err ("in call to " + (err_id p.pname) + ", expected " + (string nap) + " argument(s), found " + (string nac) + " argument(s)") else
  if nrp <> nrc then err ("procedure " + (err_id p.pname) + " returns " + (string nrp) + " value(s), call expects " + (string nrc) + " return value(s)") else
  (List.zip p.prets rets, List.zip p.pargs args)

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
    | Some (OperandLocal _ | ThreadLocal _ | ProcLocal _ | InlineLocal | StateInfo _) ->
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
              let (mrets, margs) = match_proc_args env (Map.find x env.procs) lhss es in
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
  | StateInfo (prefix, es, _) -> vaApp ("get_" + prefix) (es @ [env.state])
  | _ -> internalErr "stateGet"

let refineOp (env:env) (io:inout) (x:id) (e:exp):exp =
  let abs_x = match (io, env.abstractOld) with (In, _) | (InOut, true) -> (old_id x) | (Out, _) | (InOut, false) -> x in
  EOp (RefineOp, [EVar x; EVar abs_x; e])

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

let check_mods (env:env) (p:proc_decl):unit =
  let check_spec (_, s) =
    match s with
    | Modifies (m, e) ->
      (
        match skip_loc (exp_abstract false e) with
        | EVar x ->
          (
            match (m, Map.tryFind x env.mods) with
            | (false, None) -> err ("variable " + (err_id x) + " must be declared in reads clause or modifies clause")
            | (true, (None | Some false)) -> err ("variable " + (err_id x) + " must be declared in modifies clause")
            | (_, Some true) | (false, Some false) -> ()
          )
        | _ -> ()
      )
    | _ -> ()
    in
  if env.checkMods then List.iter check_spec p.pspecs

let rec rewrite_vars_arg (g:ghost) (asOperand:string option) (io:inout) (env:env) (e:exp):exp =
  let rec fe (env:env) (e:exp):exp map_modify =
    let codeLemma e = e
//      match asOperand with
//      | None -> e
//      | Some xo -> EOp (CodeLemmaOp, [vaApp "op" [e]; e]) // REVIEW -- should be more principled
      in
    let constOp e =
      let ec = EOp (Uop UConst, [e]) in
      match asOperand with
      | None -> ec
      | Some xo -> codeLemma (EOp (RefineOp, [ec; ec; vaApp ("const_" + xo) [e]]))
      in
    let operandProc xa io =
      let xa = string_of_id xa in
      match io with
      | In | InOut -> Id (xa + "_in")
      | Out -> Id (xa + "_out")
      in
    match (g, skip_loc e) with
    | (_, EVar x) when Map.containsKey x env.ids ->
      (
        let rec f x info =
          match info with
          // TODO: check for incorrect uses of old
          | GhostLocal _ -> Unchanged
          | InlineLocal -> (match g with NotGhost -> Replace (constOp e) | Ghost -> Unchanged)
          | OperandLocal (opIo, xo, t) ->
            (
              if env.checkMods then (match (opIo, io) with (_, In) | ((InOut | Out), _) -> () | (In, (InOut | Out)) -> err ("cannot pass 'in' operand as 'out'/'inout'"));
              match g with
              | Ghost -> Replace (refineOp env opIo x (vaEvalOp xo t env.state e))
              | NotGhost ->
                (
                  match asOperand with
                  | None -> Unchanged
                  | Some xoDst ->
                      let e = if xo = xoDst then e else vaApp ("coerce_" + xo + "_to_" + xoDst) [e] in
                      Replace (EOp (OperandArg (x, xo, t), [e]))
                )
            )
          | ThreadLocal {local_in_param = inParam; local_exp = e; local_typ = t} | ProcLocal {local_in_param = inParam; local_exp = e; local_typ = t} ->
              if inParam && io <> In then err ("variable " + (err_id x) + " must be out/inout to be passed as an out/inout argument") else
              Replace
                (match g with
                  | NotGhost -> codeLemma e
                  | Ghost ->
                      let getType t = match t with Some t -> t | None -> err ((err_id x) + " must have type annotation") in
                      let es = if inParam then EVar (Reserved "old_s") else env.state in
                      vaEvalOp "op" (getType t) es e)
          | StateInfo (prefix, es, t) ->
            (
              match (g, asOperand) with
              | (Ghost, _) -> Replace (rewrite_state_info env x prefix es)
              | (NotGhost, Some xo) ->
                  let readWrite = check_state_info_mod env x io in
                  Replace (EOp (StateOp (x, xo + "_" + prefix, t), es))
              | (NotGhost, None) -> err "this expression can only be passed to a ghost parameter or operand parameter"
            )
          | OperandAlias (x, info) -> f x info
          in
        f x (Map.find x env.ids)
      )
    | (NotGhost, ELoc _) -> Unchanged
    | (NotGhost, EOp (Uop UConst, [ec])) -> Replace (constOp (rewrite_vars_exp env ec))
    | (NotGhost, EInt _) -> Replace (constOp e)
    | (NotGhost, EApply (xa, args)) when (asOperand <> None && Map.containsKey (operandProc xa io) env.procs) ->
      (
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
        let (lhss, es) = rewrite_vars_args env p [] args in
        let ecs = List.collect (fun e -> match e with EOp (Uop UGhostOnly, [e]) -> [] | _ -> [e]) es in
        let es = List.map (fun e -> match e with EOp (Uop UGhostOnly, [e]) -> e | _ -> e) es in
        let xa_fc = Reserved ("opr_code_" + (string_of_id xa)) in
        let xa_fl = Reserved ("opr_lemma_" + (string_of_id xa)) in
        Replace (EOp (CodeLemmaOp, [EApply (xa_fc, ecs); EApply (xa_fl, env.state::es)]))
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
            let eb = rewrite_vars_arg NotGhost None In env eb in
            let eo = rewrite_vars_arg NotGhost None In env eo in
            let eCode = vaApp ("mem_code_" + ta) [eb; eo] in
            let eLemma = vaApp ("mem_lemma_" + ta) [ea; eb; eo] in
            Replace (EOp (CodeLemmaOp, [eCode; eLemma]))
        | _ -> err ("memory operand must have the form mem[base + offset] where mem is a variable")
      )
*)
    | (NotGhost, _) ->
        err "unsupported expression (if the expression is intended as a const operand, try wrapping it in 'const(...)'; if the expression is intended as a non-const operand, try declaring operand procedures)"
        // Replace (codeLemma e)
    | (Ghost, EOp (Uop UToOperand, [e])) -> Replace (rewrite_vars_arg NotGhost None io env e)
// TODO: this is a real error message, it should be uncommented
//    | (_, EApply (x, _)) when Map.containsKey x env.procs ->
//        err ("cannot call a procedure from inside an expression or variable declaration")
    | (Ghost, _) -> Unchanged
    in
  try
    env_map_exp fe env e
  with err -> (match locs_of_exp e with [] -> raise err | loc::_ -> raise (LocErr (loc, err)))
and rewrite_vars_exp (env:env) (e:exp):exp =
  rewrite_vars_arg Ghost None In env e
and rewrite_vars_args (env:env) (p:proc_decl) (rets:lhs list) (args:exp list):(lhs list * exp list) =
  let (mrets, margs) = match_proc_args env p rets args in
  let rewrite_arg (pp, ea) =
    match pp with
    | (x, t, XOperand xo, io, _) -> [rewrite_vars_arg NotGhost (Some xo) io env ea]
    | (x, t, XInline, io, _) -> [(rewrite_vars_arg Ghost None io env ea)]
    | (x, t, XAlias _, io, _) ->
        let _ = rewrite_vars_arg NotGhost None io env ea in // check argument validity
        [] // drop argument
    | (x, t, XGhost, In, []) -> [EOp (Uop UGhostOnly, [rewrite_vars_exp env ea])]
    | (x, t, XGhost, _, []) -> err ("out/inout ghost parameters are not supported")
    | (x, _, _, _, _) -> err ("unexpected argument for parameter " + (err_id x) + " in call to " + (err_id p.pname))
    in
  let rewrite_ret (pp, ((xlhs, _) as lhs)) =
    match pp with
    | (x, t, XOperand xo, _, _) -> ([], [rewrite_vars_arg NotGhost (Some xo) Out env (EVar xlhs)])
    | (x, t, XAlias _, _, _) ->
        let _ = rewrite_vars_arg NotGhost None Out env (EVar xlhs) in // check argument validity
        ([], []) // drop argument
    | (x, t, XGhost, _, []) -> ([lhs], [])
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
  let r = rewrite_vars_arg NotGhost (Some "cmp") In env in
  match skip_loc e with
  | (EApply (Id xf, es)) -> vaApp ("cmp_" + xf) (List.map r es)
  | (EOp (op, es)) ->
    (
      match (op, es) with
      | (Bop BEq, [e1; e2]) -> vaApp "cmp_eq" [r e1; r e2]
      | (Bop BNe, [e1; e2]) -> vaApp "cmp_ne" [r e1; r e2]
      | (Bop BLe, [e1; e2]) -> vaApp "cmp_le" [r e1; r e2]
      | (Bop BGe, [e1; e2]) -> vaApp "cmp_ge" [r e1; r e2]
      | (Bop BLt, [e1; e2]) -> vaApp "cmp_lt" [r e1; r e2]
      | (Bop BGt, [e1; e2]) -> vaApp "cmp_gt" [r e1; r e2]
      | _ -> err ("conditional expression must be a comparison operation or function call")
    )
  | _ -> err ("conditional expression must be a comparison operation or function call")

let rec rewrite_vars_assign (env:env) (lhss:lhs list) (e:exp):(lhs list * exp) =
  match (lhss, e) with
  | (_, ELoc (loc, e)) ->
      try let (lhss, e) = rewrite_vars_assign env lhss e in (lhss, ELoc (loc, e))
      with err -> raise (LocErr (loc, err))
  | (_, EApply(x, es)) ->
    (
      match Map.tryFind x env.procs with
      | None -> (lhss, rewrite_vars_exp env e)
      | Some p ->
          check_mods env p;
          let (lhss, args) = rewrite_vars_args env p lhss es in
          (lhss, EApply(x, args))
    )
  | _ -> (lhss, rewrite_vars_exp env e)

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
        let (lhss, e) = rewrite_vars_assign env lhss e in
        Replace (env, [SAssign (lhss, e)])
    | SIfElse (SmPlain, e, b1, b2) ->
        let b1 = env_map_stmts rewrite_vars_exp fs env b1 in
        let b2 = env_map_stmts rewrite_vars_exp fs env b2 in
        Replace (env, [SIfElse (SmPlain, rewrite_cond_exp env e, b1, b2)])
    | SWhile (e, invs, ed, b) ->
        let invs = List_mapSnd (rewrite_vars_exp env) invs in
        let ed = mapSnd (List.map (rewrite_vars_exp env)) ed in
        let b = env_map_stmts rewrite_vars_exp fs env b in
        Replace (env, [SWhile (rewrite_cond_exp env e, invs, ed, b)])
    | _ -> Unchanged
    in
  env_map_stmt rewrite_vars_exp fs env s
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
        let fOld old e = if old then EOp (Uop UOld, [e]) else e in
        match l with
        | LetsVar (x, t, e) -> (loc, BindLet, (x, t), fOld old e)
        | LetsAlias (x, y) -> (loc, BindAlias, (x, None), EVar y)
        in
      let applyLets old =
        match env.lets with
        | [] -> es
        | lets ->
            let e = and_of_list (List.map snd es) in
            let lets = List.map (let_of_lets old) lets in
            let addLet e (loc, bind, (x, t), ee) = ELoc (loc, EBind (bind, [ee], [(x, t)], [], e)) in
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
            | EVar x when Map.containsKey x env.ids ->
              (
                let rec f x info =
                  match info with
                  | OperandAlias (x, info) -> f x info
                  | _ -> Replace (EVar x)
                  in
                f x (Map.find x env.ids)
              )
            | _ -> Unchanged
            in
          let mods m = List_mapSnd (fun e -> Modifies (m, env_map_exp rewrite env e)) es in
          Replace (env, mods m)
    )
  | SpecRaw (Lets _) -> PostProcess (fun (env, _) -> (env, []))
  
let rewrite_vars_spec (envIn:env) (envOut:env) (s:spec):spec =
  match s with
  | Requires (r, e) -> Requires (r, rewrite_vars_exp envIn e)
  | Ensures (r, e) -> Ensures (r, rewrite_vars_exp envOut e)
  | Modifies (m, e) -> Modifies (m, rewrite_vars_exp envOut e)
  | SpecRaw _ -> internalErr "rewrite_vars_spec"

///////////////////////////////////////////////////////////////////////////////
// Add extra asserts for p's ensures clauses and for called procedures' requires clauses,
// to produce better error messages.

let rec is_while_proc (ss:stmt list):bool =
  match ss with
  | [s] ->
    (
      match skip_loc_stmt s with
      | SWhile (e, invs, ed, _) -> true
      | _ -> false
    )
  | s::ss when (match skip_locs_stmt s with [SVar (_, _, _, XGhost, _, _)] | [SAssign ([(_, None)], EVar _)] -> true | _ -> false) -> is_while_proc ss
  | _ -> false

let add_req_ens_asserts (env:env) (loc:loc) (p:proc_decl) (ss:stmt list):stmt list =
  if is_while_proc ss then ss else
  let hideResults ss = // wrap assertions in "forall ensures true" for better performance
    SForall ([], [], EBool true, EBool true, ss)
    in
  let rec fs (loc:loc) (s:stmt):stmt list map_modify =
    let reqAssert (f:exp -> exp) (loc, spec) =
      match spec with
      | Requires (Unrefined, _) -> []
      | Requires (Refined, e) -> [SLoc (loc, SAssert (assert_attrs_default, f e))]
      | _ -> []
      in
    let rec assign e =
      match e with
      | ELoc (loc, e) -> try assign e with err -> raise (LocErr (loc, err))
      | EApply (x, es) when Map.containsKey x env.raw_procs ->
        let pCall = Map.find x env.raw_procs in
        if List.length es = List.length pCall.pargs then
          (* Generate one assertion for each precondition of the procedure pCall that we're calling.
             Also generate "assert true" to mark the location of the call itself.
             Wrap the whole thing in "forall ensures true" to improve verification performance.
          forall 
            ensures true
          {
            ghost var va_tmp_dst := va_x90_eax;
            ghost var va_tmp_ptr := va_old_esi;
            ghost var va_tmp_offset := 60;
            assert true;
            assert inMem(va_tmp_ptr + va_tmp_offset, va_x99_mem);
          }
          *)
          let es = List.map (map_exp (fun e -> match e with EOp (Uop UConst, [e]) -> Replace e | _ -> Unchanged)) es in
          let xs = List.map (fun (x, _, _, _, _) -> x) pCall.pargs in
          let rename x = Reserved ("tmp_" + string_of_id x) in
          let xSubst = Map.ofList (List.map (fun x -> (x, EVar (rename x))) xs) in
          let xDecl x e = SVar (rename x, None, Immutable, XGhost, [], Some e) in
          let xDecls = List.map2 xDecl xs es in
          let f e =
//            let f2 e x ex = EBind (BindLet, [ex], [(rename x, None)], [], e) in
//            List.fold2 f2 (subst_reserved_exp xSubst e) xs es
            let e = map_exp (fun e -> match e with EOp (Uop UOld, [e]) -> Replace e | _ -> Unchanged) e in
            subst_reserved_exp xSubst e
            in
          let reqAsserts = (List.collect (reqAssert f) pCall.pspecs) in
          let reqMarker = SLoc (loc, SAssert (assert_attrs_default, EBool true)) in
          Replace ([hideResults (xDecls @ (reqMarker::reqAsserts)); s])
        else Unchanged
      | _ -> Unchanged
      in
    match s with
    | SLoc (loc, s) -> fs loc s
    | SAssign (_, e) -> assign e
    | _ -> Unchanged
    in
  let ss = map_stmts (fun e -> e) (fs loc) ss in
  let ensStmt (loc, s) =
    (* Generate one assertion for each postcondition of the current procedure p.
       Wrap each assertion in a "forall ensures true" to improve verification performance.
    forall 
      ensures true
    {
      assert va_old_esi + 64 <= va_old_edi || va_old_edi + 64 <= va_old_esi;
    }
    *)
    match s with
    | Ensures (Unrefined, _) -> []
    | Ensures (Refined, e) -> [hideResults [SLoc (loc, SAssert (assert_attrs_default, e))]]
    | _ -> []
    in
  let ensStmts = List.collect ensStmt p.pspecs in
  ss @ ensStmts

///////////////////////////////////////////////////////////////////////////////

let transform_decl (env:env) (loc:loc) (d:decl):(env * decl * decl) =
  match d with
  | DVar (x, t, XAlias (AliasThread, e), _) ->
      let env = {env with ids = Map.add x (ThreadLocal {local_in_param = false; local_exp = e; local_typ = Some t}) env.ids} in
      (env, d, d)
  | DVar (x, t, XState e, _) ->
    (
      match skip_loc e with
      | EApply (Id id, es) ->
          let env = {env with ids = Map.add x (StateInfo (id, es, t)) env.ids} in
          (env, d, d)
      | _ -> err ("declaration of state member " + (err_id x) + " must provide an expression of the form f(...args...)")
    )
  | DProc p ->
    (
      let isRefined = attrs_get_bool (Id "refined") false p.pattrs in
      let isFrame = attrs_get_bool (Id "frame") true p.pattrs in
      let isRecursive = attrs_get_bool (Id "recursive") false p.pattrs in
      let isInstruction = List_mem_assoc (Id "instruction") p.pattrs in
      let ok = EVar (Id "ok") in
      let okMod = SpecRaw (RawSpec (RModifies true, [(loc, SpecExp ok)])) in
      let okReqEns = SpecRaw (RawSpec (RRequiresEnsures, [(loc, SpecExp ok)])) in
      let okSpecs = [(loc, okMod); (loc, okReqEns)] in
      let pspecs = if isRefined || isFrame then okSpecs @ p.pspecs else p.pspecs in
      let addParam isRet ids (x, t, g, io, a) =
        match g with
        | (XAlias (AliasThread, e)) -> Map.add x (ThreadLocal {local_in_param = (io = In && (not isRet)); local_exp = e; local_typ = Some t}) ids
        | (XAlias (AliasLocal, e)) -> Map.add x (ProcLocal {local_in_param = (io = In && (not isRet)); local_exp = e; local_typ = Some t}) ids
        | XInline -> Map.add x InlineLocal ids
        | XOperand xo -> Map.add x (OperandLocal (io, xo, t)) ids
        | XPhysical | XState _ -> err ("variable must be declared ghost, operand, {:local ...}, or {:register ...} " + (err_id x))
        | XGhost -> Map.add x (GhostLocal ((if isRet then Mutable else Immutable), Some t)) ids
        in
      let mod_id (env:env) (loc, modifies, e) =
        let mod_err () = err "expression in modifies clause must be a variable declared as var{:state f(...)} x:t;"
        loc_apply loc e (fun e ->
          match e with
          | EVar x ->
            (
              match Map.tryFind x env.ids with
              | None -> err ("cannot find variable " + (err_id x))
              | Some (StateInfo _) -> (x, modifies)
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
      let pReprint = p in
      let p = {p with pbody = body; pspecs = pspecs} in
      // Compute mods list and final environment for body
      let mods = List.collect (fun (loc, s) -> match s with Modifies (m, e) -> [(loc, m, e)] | _ -> []) pspecs in
      let envpIn = {envpIn with mods = Map.ofList (List.map (mod_id envpIn) mods)} in
      let envpIn = {envpIn with abstractOld = true} in
      let envp = envpIn in
      let envp = {envp with ids = List.fold (addParam true) envp.ids p.prets} in
      let envp = {envp with checkMods = isRefined || isFrame} in
      let envp = {envp with abstractOld = false} in
      let specs = List_mapSnd (rewrite_vars_spec envpIn envp) pspecs in
      let envp = if isRecursive then {envp with procs = Map.add p.pname {p with pspecs = specs} envp.procs} else envp in
      let env = {env with raw_procs = Map.add p.pname p env.raw_procs}
      // Process body
      let resolveBody = p.pbody in
      let body =
        match p.pbody with
        | None -> None
        | Some ss ->
            let rec add_while_ok s =
              match s with
              | SWhile (e, invs, ed, b) ->
                  let invs = (loc, EVar (Id "ok"))::invs in
                  Replace [SWhile (e, invs, ed, map_stmts (fun e -> e) add_while_ok b)]
              | _ -> Unchanged
              in
            let ss = if isFrame then map_stmts (fun e -> e) add_while_ok ss else ss in
            let ss = if isRefined && not isInstruction then add_req_ens_asserts env loc p ss else ss in
            //let ss = assume_updates_stmts envp p.pargs p.prets ss (List.map snd pspecs) in
            let ss = rewrite_vars_stmts envp ss in
            Some ss
        in
      (env, DProc pReprint, DProc {p with pbody = body; pspecs = specs})
    )
  | _ -> (env, d, d)


