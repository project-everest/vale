// Implement '{:quick}' procedures

module Emit_common_quick_code

open Ast
open Ast_util
open Parse
open Parse_util
open Transform
open Emit_common_base
open Microsoft.FSharp.Math
open System.Numerics

let qlemma_exp (e:exp):exp =
  let e = get_lemma_exp e in
  let e = map_exp stateToOp e in
  let e = exp_refined e in
  e

let rec build_qcode_stmt (env:env) (outs:id list) (loc:loc) (s:stmt) ((needsState:bool), (eTail:exp)):(bool * exp) =
  let err () = internalErr (Printf.sprintf "make_gen_quick_block: %A" s) in
  let env0 = env in
  let env = snd (env_stmt env s) in
  let range = EVar (Id "range1") in
  let msg = EString ("***** PRECONDITION NOT MET AT " + string_of_loc loc + " *****") in
  let uses_state (e:exp):bool =
    let f (e:exp) (bs:bool list):bool =
      match e with
      | EVar (Reserved "s") -> true
      | _ -> List.fold (||) false bs
      in
    gather_exp f e
    in
  let inline_call (x:string) (rets:formal list) (es:exp list):(bool * exp) =
    let es = List.map qlemma_exp es in
    let es = List.map (fun e -> match e with EOp (Uop UGhostOnly, [e]) -> e | _ -> e) es in
    let e = vaApp ("quick_" + x) es in
    let f g eTail =
      let fTail = EBind (Lambda, [], [(Reserved "s", Some tState); g], [], eTail) in
      (uses_state e, eapply (Id "QBind") [range; msg; e; fTail])
      in
    match (needsState, rets) with
    | (false, []) -> (uses_state e, eapply (Id "QSeq") [range; msg; e; eTail])
    | (true, []) -> f (Id "_", None) eTail
    | (_, [g]) -> f g eTail
    | _ ->
        let g = Reserved "g" in
        let eTail = EBind (BindLet, [EVar g], rets, [], eTail) in
        f (g, None) eTail
    in
  let lemma_call (x:id) (rets:formal list) (es:exp list):(bool * exp) =
    let es = List.map qlemma_exp es in
    let eApp = eapply x es in
    let fApp = EBind (Lambda, [], [(Id "_", Some tUnit)], [], eApp) in
    (true, eapply (Id "qPURE") [range; msg; fApp; eTail])
    // TODO: return values from lemmas
//    (true, eapply (Id "qPURE") [fApp; eTail])
    in
  let assign_or_var (allowLemma:bool) (x:id) (tOpt:typ option) (e:exp):(bool * exp) =
    match skip_loc e with
    | EApply (Id xp, _, es) when is_proc env (Id xp) NotGhost ->
        inline_call xp [(x, tOpt)] es
//    | EApply (xp, _, es) when allowLemma ->
//        lemma_call xp [(x, tOpt)] es
    | _ ->
        let e = qlemma_exp e in
        (true, EBind (BindLet, [e], [(x, tOpt)], [], eTail))
    in
  match s with
  | SLoc (loc, s) -> build_qcode_stmt env outs loc s (needsState, eTail)
  | SAlias _ -> (needsState, eTail)
  | SAssign ([(x, None)], e) ->
      let tOpt =
        match Map.tryFind x env0.ids with
        | Some (GhostLocal (Mutable, tOpt)) -> tOpt
        | _ -> None
        in
      assign_or_var true x tOpt e
  | SAssign ([(x, Some (tOpt, _))], e) -> assign_or_var true x tOpt e
  | SAssign (xs, e) ->
    (
      let formal_of_lhs ((x:id), typGhostOpt):formal =
        match typGhostOpt with
        | Some (Some t, _) -> (x, Some t)
        | _ -> (x, None)
        in
      let xs = List.map formal_of_lhs xs in
      match skip_loc e with
      | EApply (Id x, _, es) when is_proc env (Id x) NotGhost ->
          inline_call x xs es
      | EApply (x, _, es) ->
          lemma_call x xs es
      | EOp (Uop UReveal, es) ->
          let x = "reveal_opaque" in
          if is_proc env (Id x) NotGhost then
             inline_call x xs es
          else
             lemma_call (Id x) xs es
      | _ -> err ()
    )
  | SVar (x, tOpt, _, XGhost, _, Some e) -> assign_or_var false x tOpt e
  | SLetUpdates ([], s) -> build_qcode_stmt env [] loc s (needsState, eTail)
  | SLetUpdates (xs, s) ->
      // eTailLet = (let (...gs...) = g in eTail)
      // pass eTailLet as tail to s
      let eTailLet = EBind (BindLet, [EVar (Reserved "g")], xs, [], eTail) in
      let outs = List.map fst xs in
      build_qcode_stmt env outs loc s (needsState, eTailLet)
  | SAssume e ->
      let e = qlemma_exp e in
      (true, eapply (Id "qAssume") [range; msg; e; eTail])
  | SAssert (_, e) ->
      let e = qlemma_exp e in
      (true, eapply (Id "qAssert") [range; msg; e; eTail])
  | SIfElse (((SmInline | SmPlain) as sm), eb, ss1, ss2) ->
      let eb_alt () =
        // HACK
        match eb with
        | EApply (Reserved "cmp_eq", ts, args) -> EApply (Id "Cmp_eq", ts, args)
        | EApply (Reserved "cmp_ne", ts, args) -> EApply (Id "Cmp_ne", ts, args)
        | EApply (Reserved "cmp_le", ts, args) -> EApply (Id "Cmp_le", ts, args)
        | EApply (Reserved "cmp_ge", ts, args) -> EApply (Id "Cmp_ge", ts, args)
        | EApply (Reserved "cmp_lt", ts, args) -> EApply (Id "Cmp_lt", ts, args)
        | EApply (Reserved "cmp_gt", ts, args) -> EApply (Id "Cmp_gt", ts, args)
        | _ -> internalErr "SIfElse"
        in
      let eb = qlemma_exp eb in
      let eqc1 = build_qcode_block false env outs loc ss1 in
      let eqc2 = build_qcode_block false env outs loc ss2 in
      let (sq, eCmp) =
        match sm with
        | SmInline -> ("qInlineIf", eb)
        | _ -> ("qIf", qlemma_exp (eb_alt ()))
        in
      let eIf = eapply (Id sq) [eCmp; eqc1; eqc2] in
      let fTail = EBind (Lambda, [], [(Reserved "s", Some tState); (Reserved "g", None)], [], eTail) in
      (true, eapply (Id "QBind") [range; msg; eIf; fTail])
  | SForall ([], [], (EBool true | ECast (EBool true, _)), ep, ss) ->
      let ep = qlemma_exp ep in
      let eQcs = build_qcode_stmts env [] loc ss in
      let s = Reserved "s" in
      let eAssertBy = eapply (Id "qAssertBy") [range; msg; ep; eQcs; EVar s; eTail] in
      (true, eAssertBy)
  | _ -> err ()
and build_qcode_stmts (env:env) (outs:id list) (loc:loc) (ss:stmt list):exp =
  let outTuple = EOp (TupleOp None, List.map EVar outs) in
  let empty = eapply (Id "QEmpty") [outTuple] in
  let (needsState, e) = List.foldBack (build_qcode_stmt env outs loc) ss (false, empty) in
  e
and build_qcode_block (add_old:bool) (env:env) (outs:id list) (loc:loc) (ss:stmt list):exp =
  let s = Reserved "s" in
  let eStmts = build_qcode_stmts env outs loc ss in
  let eLet = if add_old then EBind (BindLet, [EVar s], [(Reserved "old_s", Some tState)], [], eStmts) else eStmts in
  let fApp = EBind (Lambda, [], [(s, Some tState)], [], eLet) in
  eapply (Id "qblock") [fApp]

let make_gen_quick_block (loc:loc) (p:proc_decl):((env -> quick_info -> lhs list -> exp list -> stmt list -> stmt list) * (unit -> decls)) =
  let funs = ref ([]:decls) in
  let fArgs = (List.collect fArg p.prets) @ (List.collect fArg p.pargs) in
  let fParams = make_fun_params p.prets p.pargs in
  let pParams = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.pargs in
  let pArgs = List.map (fun (x, _) -> EVar x) pParams in
  let gen_quick_block env info outs args ss =
    let id = Reserved ("qcode_" + info.qsym + "_" + (string_of_id p.pname)) in
    let cid = Reserved ("code_" + info.qsym + "_" + (string_of_id p.pname)) in
    let tArgs = List.map (fun (x, _) -> TName x) fParams in
    let tCodeApp = tapply cid tArgs in
//    let fBody = build_qcode_block false env [] loc ss in
    let fBody = build_qcode_stmts env [] loc ss in
    let fCode =
      {
        fname = id;
        fghost = Ghost;
        ftargs = [];
        fargs = pParams;
        fret_name = None;
//        fret = tapply (Reserved "quickCode") [tUnit; tCodeApp];
        fret = tapply  (Id "quickCodes") [tUnit; tCodeApp];
        fspecs = [];
        fbody = Some (hide_ifs fBody);
        fattrs = [(Id "opaque_to_smt", []); (Id "qattr", [])] @ attr_no_verify "admit" p.pattrs;
      }
      in
    let dFun = DFun fCode in
    funs := (loc, dFun)::!funs;
    (*
      let (va_s2, va_fc2, ()) = wp_run_code_norm (va_code_1_Incr3 ()) (va_quick_1_Incr3 ()) va_s0
        (fun (s0:state) (sN:state) -> va_update_reg Rax sN (va_update_flags sN s0))
        (fun (sN:state) (sN':state) -> va_get_reg Rax sN == va_get_reg Rax sN' /\ va_get_flags sN == va_get_flags sN')
    *)
    let eCode = eapply cid fArgs in
    let eQCode = eapply id pArgs in
    let s0 = Reserved "s0" in
    let sM = Reserved "sM" in
    let sN = Reserved "sN" in
    let eqMod x =
      let getM = stateGet {env with state = EVar sM} x in
      let getN = stateGet {env with state = EVar sN} x in
      EOp (Bop (BEq BpProp), [getM; getN])
      in
    let eEq = and_of_list (List.map eqMod info.qmods) in
    let fEq = EBind (Lambda, [], [(sM, Some tState); (sN, Some tState)], [], eEq) in
    let frameMod e x =
      match Map.tryFind x env.ids with
      | Some (StateInfo (prefix, es, t)) -> vaApp ("update_" + prefix) (es @ [EVar sN; e])
      | _ -> internalErr ("gen_quick_block: could not find variable " + (err_id x))
      in
    let eUpdate = List.fold frameMod (EVar s0) info.qmods in
    let fUpdate = EBind (Lambda, [], [(s0, Some tState); (sN, Some tState)], [], eUpdate) in
    let sLemma = SAssign (outs, eapply (Id "wp_run_norm") (eCode::eQCode::args @ [fUpdate; fEq])) in
    [sLemma]
    in
  let gen_quick_block_funs () = List.rev !funs in
  (gen_quick_block, gen_quick_block_funs)

let build_qcode (env:env) (loc:loc) (p:proc_decl) (ss:stmt list):decls =
  (*
  [@"opaque_to_smt"]
  let va_qcode_Add3 () : quickCode unit (va_code_Add3 ()) = qblock (
    fun (va_s:state) -> let va_old_s = va_s in
    QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    QEmpty ()
    )))
  )
  *)
  let cParams = make_fun_params p.prets p.pargs in
  let makeParam (x, t, storage, io, attrs) = (x, Some t) in
  let qParams = List.map makeParam p.pargs in
  let makeRet (x, t, storage, io, attrs) = match storage with XGhost -> [(x, t)] | _ -> [] in
  let prets = List.collect makeRet p.prets in
  let tRet = TTuple (List.map snd prets) in
  let cid = Reserved ("code_" + (string_of_id p.pname)) in
  let tArgs = List.map (fun (x, _) -> TName x) cParams in
  let tCodeApp = tapply cid tArgs in
  let tRetQuick = tapply (Id "quickCode") [tRet; tCodeApp] in
  let mutable_scope = Map.ofList (List.map (fun (x, t, _, _, _) -> (x, Some t)) p.prets) in
  let (_, ss) = let_updates_stmts mutable_scope ss in
  let outs = List.map fst prets in
  let eQuick = build_qcode_block true env outs loc ss in
  let fCodes =
    {
      fname = Reserved ("qcode_" + (string_of_id p.pname));
      fghost = NotGhost;
      ftargs = [];
      fargs = qParams;
      fret_name = None;
      fret = tRetQuick;
      fspecs = [];
      fbody = Some (hide_ifs eQuick);
      fattrs = [(Id "opaque_to_smt", []); (Id "qattr", [])] @ attr_no_verify "admit" p.pattrs;
    }
    in
  [(loc, DFun fCodes)]

let build_proc_body (env:env) (loc:loc) (p:proc_decl) (code:exp) (ens:exp):stmt list =
  let makeArg (x, t, storage, io, attrs) = EVar x
  let args = List.map makeArg p.pargs in
  // let (sM, fM, g) = wpSound_X code (qCodes_X ARGS) s0 (fun s0 sM gs -> let (g1, ..., gn) = g in ENS) in
  // let (g1, ..., gn) = g in
  let s0 = Reserved "s0" in
  let fM = Reserved "fM" in
  let sM = Reserved "sM" in
  let g = Reserved "g" in
//  let wpSound_X = Reserved ("wpSound_" + (string_of_id p.pname)) in
  let wpSound_X = Id "wp_sound_code_norm" in
  let qCodes_X = Reserved ("qcode_" + (string_of_id p.pname)) in
  let ghostRets = List.collect (fun (x, t, g, _, _) -> match g with XGhost -> [(x, t)] | _ -> []) p.prets in
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let letGs = EBind (BindLet, [EVar g], gAssigns, [], hide_ifs ens) in
  let funCont = EBind (Lambda, [], [(s0, None); (sM, None); (g, None)], [], letGs) in
  let eWpSound = eapply wpSound_X [code; eapply qCodes_X args; EVar s0; funCont] in
  let sWpSound = SAssign ([(sM, None); (fM, None); (g, None)], eWpSound) in
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let sAssignGs =
    match ghostRets with
    | [] -> []
    | _ -> [SAssign (gAssigns, EVar g)]
    in
  [sWpSound] @ sAssignGs
