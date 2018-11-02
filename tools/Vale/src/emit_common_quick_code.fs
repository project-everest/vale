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

let qmods_opt (x:'a):'a list = if !quick_mods then [x] else []

let qlemma_exp (e:exp):exp =
  let e = get_lemma_exp e in
  let e = map_exp stateToOp e in
  let e = exp_refined e in
  e

let makeFrame (env:env) (preserveModifies:bool) (p:proc_decl) (s0:id) (sM:id):exp * exp list * formal list =
  let id_x (x:id) = Reserved ("x_" + string_of_id x) in
  let specModsIo preserveModifies = List.collect (specModIo env preserveModifies) p.pspecs in
  let collectArg (isRet:bool) (x, t, storage, io, _) =
    match (isRet, storage, io) with
    | (true, XOperand, _) | (_, XOperand, (InOut | Out)) -> [(x, id_x x, t)]
    | _ -> []
    in
  let collectMod (io, (x, _)) =
    match io with
    | (InOut | Out) ->
      (
        match Map.tryFind x env.ids with
        | Some (StateInfo (prefix, es, t)) -> [(id_x x, t, prefix, es)]
        | _ -> internalErr ("frameMod: could not find variable " + (err_id x))
      )
    | _ -> []
    in
  let mods preserveModifies = List.collect collectMod (specModsIo preserveModifies) in
  let args = (List.collect (collectArg true) p.prets) @ (List.collect (collectArg false) p.pargs) in
  let frameArg e (x, xx, t) = vaApp ("upd_" + (vaOperandTyp t)) [evar x; evar xx; e] (Some t) in
  let framePArg (x, _, t) = vaApp ("mod_" + (vaTyp t)) [evar x] (Some t) in
  let frameMod e (x, t, prefix, es) = vaApp ("upd_" + prefix) (es @ [evar x; e]) (Some t) in
  let framePMod (_, t, prefix, es) = eapply_opt (Id ("Mod_" + prefix)) es (Some t) in
  let e = evar s0 in
  let e = List.fold frameArg e args in
  let e = List.fold frameMod e (mods false) in
  let pmods = List.map framePArg args @ List.map framePMod (mods preserveModifies) in
  let fs = [] in
  let fs = List.fold (fun fs (_, xx, t) -> (xx, Some (tOperand (vaValueTyp t)))::fs) fs args in
  let fs = List.fold (fun fs (x, t, _, _) -> (x, Some t)::fs) fs (mods false) in
  (e, List.rev pmods, List.rev fs)

let rec build_qcode_stmt (env:env) (outs:id list) (loc:loc) (s:stmt) ((needsState:bool), (eTail:exp)):(bool * exp) =
  let err () = internalErr (Printf.sprintf "make_gen_quick_block: %A" s) in
  let env0 = env in
  let env = snd (env_stmt env s) in
  let range = evar (Id "range1") in
  let msg = EString ("***** PRECONDITION NOT MET AT " + string_of_loc loc + " *****") in
  let mods = evar (Reserved "mods") in
  let uses_state (e:exp):bool =
    let f (e:exp) (bs:bool list):bool =
      match e with
      | EVar (Reserved "s", _) -> true
      | _ -> List.fold (||) false bs
      in
    gather_exp f e
    in
  let inline_call (x:string) (rets:formal list) (es:exp list) (t: typ option):(bool * exp) =
    let es = List.map qlemma_exp es in
    let es = List.map (fun e -> match e with EOp (Uop UGhostOnly, [e], _) -> e | _ -> e) es in
    let e = vaApp ("quick_" + x) es t in
    let f g eTail =
      let fTail = EBind (Lambda, [], [(Reserved "s", Some tState); g], [], eTail, None) in
      (uses_state e, eapply (Id "QBind") [range; msg; e; fTail] None)
      in
    match (needsState, rets) with
    | (false, []) -> (uses_state e, eapply (Id "QSeq") [range; msg; e; eTail] None)
    | (true, []) -> f (Id "_", None) eTail
    | (_, [g]) -> f g eTail
    | _ ->
        let g = Reserved "g" in
        let eTail = EBind (BindLet, [evar g], rets, [], eTail, None) in
        f (g, None) eTail
    in
  let lemma_call (x:id) (rets:formal list) (es:exp list) (t: typ option):(bool * exp) =
    let es = List.map qlemma_exp es in
    let eApp = eapply x es t in
    let fApp = EBind (Lambda, [], [(Id "_", Some tUnit)], [], eApp, None) in
    (true, eapply (Id "qPURE") [range; msg; fApp; eTail] None)
    // TODO: return values from lemmas
//    (true, eapply (Id "qPURE") [fApp; eTail])
    in
  let assign_or_var (allowLemma:bool) (x:id) (tOpt:typ option) (e:exp):(bool * exp) =
    match skip_loc e with
    | EApply (Id xp, _, es, t) when is_proc env (Id xp) NotGhost ->
        inline_call xp [(x, tOpt)] es t
//    | EApply (xp, _, es) when allowLemma ->
//        lemma_call xp [(x, tOpt)] es
    | _ ->
        let e = qlemma_exp e in
        (true, EBind (BindLet, [e], [(x, tOpt)], [], eTail, None))
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
      | EApply (Id x, _, es, t) when is_proc env (Id x) NotGhost ->
          inline_call x xs es t
      | EApply (x, _, es, t) ->
          lemma_call x xs es t
      | EOp (Uop UReveal, es, t) ->
          let x = "reveal_opaque" in
          if is_proc env (Id x) NotGhost then
             inline_call x xs es t
          else
             lemma_call (Id x) xs es t
      | _ -> err ()
    )
  | SVar (x, tOpt, _, XGhost, _, Some e) -> assign_or_var false x tOpt e
  | SLetUpdates ([], s) -> build_qcode_stmt env [] loc s (needsState, eTail)
  | SLetUpdates (xs, s) ->
      // eTailLet = (let (...gs...) = g in eTail)
      // pass eTailLet as tail to s
      let eTailLet = EBind (BindLet, [evar (Reserved "g")], xs, [], eTail, None) in
      let outs = List.map fst xs in
      build_qcode_stmt env outs loc s (needsState, eTailLet)
  | SAssume e ->
      let e = qlemma_exp e in
      (true, eapply (Id "qAssume") [range; msg; e; eTail] None)
  | SAssert (_, e) ->
      let e = qlemma_exp e in
      (true, eapply (Id "qAssert") [range; msg; e; eTail] None)
  | SIfElse (((SmInline | SmPlain) as sm), eb, ss1, ss2) ->
      let eb_alt () =
        // HACK
        match eb with
        | EApply (Reserved "cmp_eq", ts, args, t) -> EApply (Id "Cmp_eq", ts, args, t)
        | EApply (Reserved "cmp_ne", ts, args, t) -> EApply (Id "Cmp_ne", ts, args, t)
        | EApply (Reserved "cmp_le", ts, args, t) -> EApply (Id "Cmp_le", ts, args, t)
        | EApply (Reserved "cmp_ge", ts, args, t) -> EApply (Id "Cmp_ge", ts, args, t)
        | EApply (Reserved "cmp_lt", ts, args, t) -> EApply (Id "Cmp_lt", ts, args, t)
        | EApply (Reserved "cmp_gt", ts, args, t) -> EApply (Id "Cmp_gt", ts, args, t)
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
      let eIf = eapply (Id sq) (qmods_opt mods @ [eCmp; eqc1; eqc2]) None in
      let fTail = EBind (Lambda, [], [(Reserved "s", Some tState); (Reserved "g", None)], [], eTail, None) in
      (true, eapply (Id "QBind") [range; msg; eIf; fTail] None)
  | SForall ([], [], (EBool true | ECast (EBool true, _)), ep, ss) ->
      let ep = qlemma_exp ep in
      let eQcs = build_qcode_stmts env [] loc ss in
      let s = Reserved "s" in
      let eAssertBy = eapply (Id "qAssertBy") (qmods_opt mods @ [range; msg; ep; eQcs; evar s; eTail]) None in
      (true, eAssertBy)
  | _ -> err ()
and build_qcode_stmts (env:env) (outs:id list) (loc:loc) (ss:stmt list):exp =
  let outTuple = EOp (TupleOp None, List.map evar outs, None) in
  let empty = eapply (Id "QEmpty") [outTuple] None in
  let (needsState, e) = List.foldBack (build_qcode_stmt env outs loc) ss (false, empty) in
  e
and build_qcode_block (add_old:bool) (env:env) (outs:id list) (loc:loc) (ss:stmt list):exp =
  let s = Reserved "s" in
  let eStmts = build_qcode_stmts env outs loc ss in
  let eLet = if add_old then EBind (BindLet, [evar s], [(Reserved "old_s", Some tState)], [], eStmts, None) else eStmts in
  let fApp = EBind (Lambda, [], [(s, Some tState)], [], eLet, None) in
  eapply (Id "qblock") (qmods_opt (evar (Reserved "mods")) @ [fApp]) None

let make_gen_quick_block (loc:loc) (p:proc_decl):((env -> quick_info -> lhs list -> exp list -> stmt list -> stmt list) * (unit -> decls)) =
  let funs = ref ([]:decls) in
  let fArgs = (List.collect fArg p.prets) @ (List.collect fArg p.pargs) in
  let fParams = make_fun_params p.prets p.pargs in
  let pParams = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.pargs in
  let pArgs = List.map (fun (x, _) -> evar x) pParams in
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
    let eCode = eapply cid fArgs None in
    let eQCode = eapply id pArgs None in
    let s0 = Reserved "s0" in
    let sM = Reserved "sM" in
    let sN = Reserved "sN" in
    let eqMod x =
      let getM = stateGet {env with state = evar sM} x in
      let getN = stateGet {env with state = evar sN} x in
      EOp (Bop (BEq BpProp), [getM; getN], None)
      in
    let eEq = and_of_list (List.map eqMod info.qmods) in
    let fEq = EBind (Lambda, [], [(sM, Some tState); (sN, Some tState)], [], eEq, None) in
    let frameMod e x =
      match Map.tryFind x env.ids with
      | Some (StateInfo (prefix, es, t)) -> vaApp ("update_" + prefix) (es @ [evar sN; e]) None
      | _ -> internalErr ("gen_quick_block: could not find variable " + (err_id x))
      in
    let eUpdate = List.fold frameMod (evar s0) info.qmods in
    let fUpdate = EBind (Lambda, [], [(s0, Some tState); (sN, Some tState)], [], eUpdate, None) in
    let sLemma = SAssign (outs, eapply (Id "wp_run_norm") (eCode::eQCode::args @ [fUpdate; fEq]) None) in
    [sLemma]
    in
  let gen_quick_block_funs () = List.rev !funs in
  (gen_quick_block, gen_quick_block_funs)

let build_qcode (env:env) (loc:loc) (p:proc_decl) (ss:stmt list):decls =
  (*
  [@"opaque_to_smt"]
  let va_qcode_Add3 (va_mods:mods_t) : quickCode unit (va_code_Add3 ()) = qblock (
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
      fargs = (qmods_opt (Reserved "mods", Some (TName (Id "mods_t")))) @ qParams;
      fret_name = None;
      fret = tRetQuick;
      fspecs = [];
      fbody = Some (hide_ifs eQuick);
      fattrs = [(Id "opaque_to_smt", []); (Id "qattr", [])] @ attr_no_verify "admit" p.pattrs;
    }
    in
  [(loc, DFun fCodes)]

let build_proc_body (env:env) (loc:loc) (p:proc_decl) (code:exp) (ens:exp):stmt list =
  let makeArg (x, t, storage, io, attrs) = evar x
  let args = List.map makeArg p.pargs in
  // let (sM, fM, g) = wpSound_X code (qCodes_X ARGS) s0 (fun s0 sM gs -> let (g1, ..., gn) = g in ENS) in
  // let (g1, ..., gn) = g in
  let s0 = Reserved "s0" in
  let fM = Reserved "fM" in
  let sM = Reserved "sM" in
  let g = Reserved "g" in
  let mods = Reserved "mods" in
  let qc = Reserved "qc" in
  let (_, pmods, _) = makeFrame env true p s0 sM in
  let ePMods = eapply (Id "list") pmods None in
  let sMods = SAssign ([(mods, Some (Some (TName (Id "mods_t")), Ghost))], ePMods) in
//  let wpSound_X = Reserved ("wpSound_" + (string_of_id p.pname)) in
  let wpSound_X = Id "wp_sound_code_norm" in
  let qCodes_X = Reserved ("qcode_" + (string_of_id p.pname)) in
  let ghostRets = List.collect (fun (x, t, g, _, _) -> match g with XGhost -> [(x, t)] | _ -> []) p.prets in
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let letGs = EBind (BindLet, [evar g], gAssigns, [], hide_ifs ens, None) in
  let funCont = EBind (Lambda, [], [(s0, None); (sM, None); (g, None)], [], letGs, None) in
  let args = qmods_opt (evar mods) @ args in
  let sQc = SAssign ([(qc, None)], eapply qCodes_X args None) in
  let eWpSound = eapply wpSound_X [code; evar qc; evar s0; funCont] None in
  let sWpSound = SAssign ([(sM, None); (fM, None); (g, None)], eWpSound) in
  // assert_norm (va_qc.mods == va_mods)
  let eQcMods = EOp (FieldOp (Id "mods"), [evar qc], None) in
  let sQcNorm = SAssign ([], eapply (Id "assert_norm") [EOp (Bop (BEq BpProp), [eQcMods; evar mods], None)] None) in
  // lemma_norm_mods va_mods va_sM va_s0
  let sLemmaNormMods = SAssign ([], eapply (Id "lemma_norm_mods") [ePMods; evar sM; evar s0] None) in
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let sAssignGs =
    match ghostRets with
    | [] -> []
    | _ -> [SAssign (gAssigns, evar g)]
    in
  qmods_opt sMods @ [sQc; sWpSound] @ qmods_opt sQcNorm @ qmods_opt sLemmaNormMods @ sAssignGs
