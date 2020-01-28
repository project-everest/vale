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
        | Some (StateInfo (prefix, es, t, _)) -> [(id_x x, t, prefix, es)]
        | _ -> internalErr ("frameMod: could not find variable " + (err_id x))
      )
    | _ -> []
    in
  let mods preserveModifies = List.collect collectMod (specModsIo preserveModifies) in
  let args = (List.collect (collectArg true) p.prets) @ (List.collect (collectArg false) p.pargs) in
  let frameArg e (x, xx, t) = vaApp_t ("upd_" + (vaOperandTyp t)) [evar x; evar xx; e] (exp_typ e) in
  let framePArg (x, _, t) = vaApp ("mod_" + (vaTyp t)) [evar x] in
  let frameMod e (x, t, prefix, es) = vaApp_t ("upd_" + prefix) (es @ [evar x; e]) (exp_typ e) in
  let framePMod (_, t, prefix, es) = eapply_opt (Reserved ("Mod_" + prefix)) es in
  let e = evar s0 in
  let e = List.fold frameArg e args in
  let e = List.fold frameMod e (mods false) in
  let pmods = List.map framePArg args @ List.map framePMod (mods preserveModifies) in
  let fs = [] in
  let fs = List.fold (fun fs (_, xx, t) -> (xx, Some (tOperand (vaValueTyp t)))::fs) fs args in
  let fs = List.fold (fun fs (x, t, _, _) -> (x, Some t)::fs) fs (mods false) in
  (e, List.rev pmods, List.rev fs)

let rec fbind_gs (g:id) (xOuts:formal list) (gs:formal list) (e:exp) : exp =
  // REVIEW: this is ugly: for normalizability, in some places we have to say
  //   let g1 = (let (g1, ..., gn) = g in g1) in
  //   ...
  //   let gn = (let (g1, ..., gn) = g in gn) in
  //   e
  // instead of
  //   let (g1, ..., gn) = g in e
  // Currently:
  //   - in while, "forall ... (g:a)" in wp_While introduces a g that's a variable, not a tuple constructor
  //   - in lemma calls, all return values for va_qBindPURE are passed in a single variable
  let fbind_g e = ebind BindLet [evar g] xOuts [] e in
  match gs with
  | [] -> e
  | (gk, t)::gs ->
      let egk = fbind_g (evar gk) in
      ebind BindLet [egk] [(gk, t)] [] (fbind_gs g xOuts gs e)
  in

// With --use_two_phase_tc true, we need to turn:
//   f(e)
// into:
//   let x:t = e in f(x)
// when we use F*'s $ type inference for f(...) and e's type is a subtype of what f expects
// (or when e contains subtyping internally)
let lift_subtype_arg (t:typ) (e:exp):(formal * exp) option * exp =
  // For simplicity, err on the side of lifting: if it's not a variable with exactly the right
  // type or a constant integer, lift it.
  match skip_loc e with
  | EVar (_, Some tx) when t = tx -> (None, e)
  | EInt _ | ECast (_, EInt _, _) -> (None, e)
  | _ ->
      let i = string (gen_lemma_sym ()) in
      let x = Reserved ("arg" + i) in
      (Some ((x, Some t), e), EVar (x, Some t))

let rec build_qcode_stmt (env:env) (outs_t:formal list) (loc:loc) (s:stmt) ((needsState:bool), (eTail:exp)):(bool * exp) =
  let ierr () = internalErr (Printf.sprintf "build_qcode_stmt: %A" s) in
  let outs = List.map fst outs_t in
  let env0 = env in
  let env = snd (env_stmt env s) in
  let range = evar (Reserved "range1") in
  let msg = EString ("***** PRECONDITION NOT MET AT " + string_of_loc loc + " *****") in
  let msgs = EString ("***** EXPRESSION PRECONDITIONS NOT MET WITHIN " + string_of_loc loc + " *****") in
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
    let e = vaApp_t ("quick_" + x) es t in
    let f g eTail =
      let fTail = ebind Lambda [] [(Reserved "s", Some tState); g] [] eTail in
      (uses_state e, eapply (Reserved "QBind") [range; msg; e; fTail])
      in
    match (needsState, rets) with
    | (false, []) -> (uses_state e, eapply (Reserved "QSeq") [range; msg; e; eTail])
    | (true, []) -> f (Id "_", None) eTail
    | (_, [g]) -> f g eTail
    | _ ->
        let g = Reserved "g" in
        let eTail = ebind BindLet [evar g] rets [] eTail in
        f (g, None) eTail
    in
  let lemma_call (x:id) (tfun:typ option) (rets:formal list) (ts:(tqual * typ) list option) (es:exp list) (t:typ option):(bool * exp) =
    let pOpt = Map.tryFind x env.procs in
    let infer_spec =
      // infer_spec
      match pOpt with
      | None -> true
      | Some {pattrs = a} when attrs_get_bool (Id "infer_spec") false a -> true
      | _ -> false
      in
    let () =
      match (infer_spec, rets) with
      // F* inference of specs only works with no return values:
      | (true, _::_) -> err "infer_spec only supported for lemmas (no return values allowed)"
      | _ -> ()
      in
    let es = List.map qlemma_exp es in
    let (xlets, es) =
      match (infer_spec, tfun) with
      | (true, Some (TFun (targs, _))) -> List.unzip (List.map2 lift_subtype_arg targs es)
      | _ -> ([], es)
      in
    let xlets = List.collect (fun xt -> match xt with None -> [] | Some xt -> [xt]) xlets in
    let eApp = eapply_t x es t in
    let fApp = ebind Lambda [] [(Id "_", Some tUnit)] [] eApp in
    let app qPure eTail =
      let eCall = eapply (Reserved qPure) [range; msg; fApp; eTail] in
      let eCall = List.fold (fun e (xt, ex) -> ebind BindLet [ex] [xt] [] e) eCall xlets in
      (true, eCall)
      in
    match (infer_spec, rets, pOpt) with
    | (true, [], _) -> app "qPURE" eTail
    | (false, [], Some p) ->
        // va_QLemma range msg pre post fApp eTail
        let p = Map.find x env.procs in
        // pre = (fun(x1...xn) req)(e1...en)
        // post = (fun(x1...xn) ens)(e1...en)
        let (reqs, enss) = collect_specs false p.pspecs in
        let xs = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.pargs in
        let pre = rename_args p.ptargs xs ts es (and_of_list reqs) in
        let post = rename_args p.ptargs xs ts es (and_of_list enss) in
        let post = ebind Lambda [] [(Id "_", None)] [] post in
        let eCall = eapply (Reserved "QLemma") [range; msg; pre; post; fApp; eTail] in
        (true, eCall)
    | _ -> notImplemented "lemma calls with return values"
(* TODO: use QGhost and instantiate pre and post explicitly
    | [(xarg, Some targ)] when is_proc env x Ghost ->
        // QGhost targ range msg pre post fApp eTail
        let p = Map.find x env.procs in
        // pre = (fun(x1...xn) req)(e1...en)
        // post = (fun(x1...xn) fun(x) ens)(e1...en)
        let (reqs, enss) = collect_specs false p.pspecs in
        let pre = and_of_list reqs in
        let post = and_of_list enss in
        let eTail = ebind Lambda [] [(xarg, Some targ)] [] eTail in
        let eCall = EApply (evar (Reserved "QLemma"), Some [t], [range; msg; pre; post; fApp; eTail], None) in
        (true, eCall)
    | [x] -> vaApp "qBindPURE" (ebind Lambda [] [(dummy, None); x] [] eTail)
    | _::_ ->
        let eTail = fbind_gs g rets rets eTail in
        let eTail = ebind Lambda [] [(dummy, None); (g, None)] [] eTail in
        vaApp "qBindPURE" eTail
*)
    in
  let assign_or_var (allowLemma:bool) (x:id) (tOpt:typ option) (e:exp):(bool * exp) =
    match skip_loc e with
    | EApply (e, _, es, t) when is_id e && is_proc env (id_of_exp e) NotGhost->
        let xp = string_of_id (id_of_exp e) in 
        inline_call xp [(x, tOpt)] es t
//    | EApply (xp, _, es) when allowLemma ->
//        lemma_call xp [(x, tOpt)] es
    | _ ->
        let e = qlemma_exp e in
        (true, ebind BindLet [e] [(x, tOpt)] [] eTail)
    in
  let eb_alt (eb:exp) =
    // HACK
    match eb with
    | EApply (e, ts, args, t) when is_id e && id_of_exp e = Reserved "cmp_eq" -> EApply (evar (Id "Cmp_eq"), ts, args, t)
    | EApply (e, ts, args, t) when is_id e && id_of_exp e = Reserved "cmp_ne" -> EApply (evar (Id "Cmp_ne"), ts, args, t)
    | EApply (e, ts, args, t) when is_id e && id_of_exp e = Reserved "cmp_le" -> EApply (evar (Id "Cmp_le"), ts, args, t)
    | EApply (e, ts, args, t) when is_id e && id_of_exp e = Reserved "cmp_ge" -> EApply (evar (Id "Cmp_ge"), ts, args, t)
    | EApply (e, ts, args, t) when is_id e && id_of_exp e = Reserved "cmp_lt" -> EApply (evar (Id "Cmp_lt"), ts, args, t)
    | EApply (e, ts, args, t) when is_id e && id_of_exp e = Reserved "cmp_gt" -> EApply (evar (Id "Cmp_gt"), ts, args, t)
    | _ -> internalErr "unsupported if/while condition"
    in
  match s with
  | SLoc (loc, s) -> build_qcode_stmt env outs_t loc s (needsState, eTail)
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
      | EApply (e, _, es, t) when is_id e && is_proc env (id_of_exp e) NotGhost ->
          inline_call (string_of_id (id_of_exp e)) xs es t
      | EApply (e, ts, es, t) when is_id e ->
          let tfun = match skip_loc e with EVar (_, t) -> t | _ -> None in
          lemma_call (id_of_exp e) tfun xs ts es t
      | EOp (Uop UReveal, [e], t) ->
        (
          let e = qlemma_exp e in
          let f ex =
            let esx = EOp (Uop UFStarNameString, [ex], None) in
            let eq = eapply (Reserved "reveal_eq") [esx; e; e] in
            let eq = ebind Lambda [] [(Id "_", None)] [] eq in
            let ecall = eapply (Reserved "reveal_opaque") [esx; e] in
            let ef = ebind Lambda [] [(Id "_", None)] [] ecall in
            (true, eapply (Reserved "QLemma") [range; msg; EBool true; eq; ef; eTail])
            in
          match skip_loc e with
          | EVar (x, _) -> f e
          | EApply (ex, _, _, _) ->
            (
              match skip_loc ex with
              | EVar (x, _) as ex -> f ex
              | _ -> ierr ()
            )
          | _ -> ierr ()
        )
      | _ -> ierr ()
    )
  | SVar (x, tOpt, _, XGhost, _, Some e) -> assign_or_var false x tOpt e
  | SLetUpdates ([], s) -> build_qcode_stmt env [] loc s (needsState, eTail)
  | SLetUpdates (xs, s) ->
      // eTailLet = (let (...gs...) = g in eTail)
      // pass eTailLet as tail to s
      let eTailLet = ebind BindLet [evar (Reserved "g")] xs [] eTail in
      build_qcode_stmt env xs loc s (needsState, eTailLet)
  | SAssume e ->
      let e = qlemma_exp e in
      (true, eapply (Reserved "qAssume") [range; msg; e; eTail])
  | SAssert ({is_quicktype = Some b}, e) ->
      let e = qlemma_exp e in
      let eTail = ebind Lambda [] [(Id "_", None)] [] eTail in
      (true, eapply (Reserved "qAssertSquash") [range; (if b then msgs else msg); e; eTail])
  | SAssert (_, e) ->
      let e = qlemma_exp e in
      (true, eapply (Reserved "qAssert") [range; msg; e; eTail])
  | SIfElse (((SmInline | SmPlain) as sm), eb, ss1, ss2) ->
      let eb = qlemma_exp eb in
      let eqc1 = build_qcode_block false env outs_t loc ss1 in
      let eqc2 = build_qcode_block false env outs_t loc ss2 in
      let (sq, eCmp) =
        match sm with
        | SmInline -> ("qInlineIf", eb)
        | _ -> ("qIf", qlemma_exp (eb_alt eb))
        in
      let eIf = eapply (Reserved sq) (qmods_opt mods @ [eCmp; eqc1; eqc2]) in
      let fTail = ebind Lambda [] [(Reserved "s", Some tState); (Reserved "g", None)] [] eTail in
      (true, eapply (Reserved "QBind") [range; msg; eIf; fTail])
  | SWhile (eb, invs, (_, [ed]), ss) ->
      let eb = qlemma_exp eb in
      let inv = and_of_list (List.map snd invs) in
      let eInv = qlemma_exp inv in
      let ed = qlemma_exp ed in // TODO: more than one decreases expression --> ed = %[...]
      let eqc = build_qcode_block false env outs_t loc ss in
      let eCmp = eb_alt eb in
      let xs = (Reserved "s", Some tState) in
      let xg = (Reserved "g", None) in
      let xOuts = List.map (fun x -> (x, None)) outs in
      let outTuple = eop (TupleOp None) (List.map evar outs) in
      // REVIEW: this is ugly: for normalizability, we have to say
      //   let g1 = (let (g1, ..., gn) = g in g1) in
      //   ...
      //   let gn = (let (g1, ..., gn) = g in gn) in
      //   e
      // instead of
      //   let (g1, ..., gn) = g in e
      // (this is because "forall ... (g:a)" in wp_While introduces a g that's a variable, not a tuple constructor)
      let fbinds_g = fbind_gs (Reserved "g") xOuts outs_t in
      let fqc = ebind Lambda [] [xg] [] (fbinds_g eqc) in
      let fInv = ebind Lambda [] [xs; xg] [] (fbinds_g eInv) in
      let fd = ebind Lambda [] [xs; xg] [] (fbinds_g ed) in
      let eWhile = eapply (Reserved "qWhile") (qmods_opt mods @ [eCmp; fqc; fInv; fd; outTuple]) in
      let eTail = ebind BindLet [eop (TupleOp None) (List.map evar outs)] [xg] [] eTail in
      let fTail = ebind Lambda [] [xs; xg] [] (fbinds_g eTail) in
      (true, eapply (Reserved "QBind") [range; msg; eWhile; fTail])
  | SForall ([], [], (EBool true | ECast (_, EBool true, _)), ep, ss) ->
      let ep = qlemma_exp ep in
      let eQcs = build_qcode_stmts env [] loc ss in
      //let s = Reserved "s" in
      let eAssertBy = eapply (Reserved "qAssertBy") [range; msg; ep; eQcs; eTail] in
      (true, eAssertBy)
  | _ -> ierr ()
and build_qcode_stmts (env:env) (outs_t:formal list) (loc:loc) (ss:stmt list):exp =
  let outs = List.map fst outs_t in
  let outTuple = eop (TupleOp None) (List.map evar outs) in
  let empty = eapply (Reserved "QEmpty") [outTuple] in
  let (needsState, e) = List.foldBack (build_qcode_stmt env outs_t loc) ss (false, empty) in
  e
and build_qcode_block (add_old:bool) (env:env) (outs_t:formal list) (loc:loc) (ss:stmt list):exp =
  let s = Reserved "s" in
  let eStmts = build_qcode_stmts env outs_t loc ss in
  let eLet = if add_old then ebind BindLet [evar s] [(Reserved "old_s", Some tState)] [] eStmts else eStmts in
  let fApp = ebind Lambda [] [(s, Some tState)] [] eLet in
  eapply (Id "qblock") (qmods_opt (evar (Reserved "mods")) @ [fApp])

let build_qcode (env:env) (loc:loc) (p:proc_decl) (ss:stmt list):decls =
  (*
  [@"opaque_to_smt"]
  let va_qcode_Add3 (va_mods:mods_t) : va_quickCode unit (va_code_Add3 ()) = qblock (
    fun (va_s:state) -> let va_old_s = va_s in
    va_QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    va_QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    va_QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    va_QEmpty ()
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
  let tRetQuick = tapply (Reserved "quickCode") [tRet; tCodeApp] in
  let mutable_scope = Map.ofList (List.map (fun (x, t, _, _, _) -> (x, Some t)) p.prets) in
  let (_, ss) = let_updates_stmts mutable_scope ss in
  let outs = List.map (fun (x, t) -> (x, Some t)) prets in
  let eQuick = build_qcode_block true env outs loc ss in
  let fCodes =
    {
      fname = Reserved ("qcode_" + (string_of_id p.pname));
      fghost = NotGhost;
      ftargs = [];
      fargs = (qmods_opt (Reserved "mods", Some (TName (Reserved "mods_t")))) @ qParams;
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
  // let va_old = expand_state va_old in
  let expand_arg (x, t, _, _, a) =
    if attrs_get_bool (Reserved "expand_state") false a then
      [SAssign ([(x, None)], eapply (Reserved "expand_state") [evar x])]
    else []
    in
  let expansions = List.collect expand_arg p.pargs in
  // let (sM, fM, g) = wpSound_X code (qCodes_X ARGS) s0 (fun s0 sM gs -> let (g1, ..., gn) = g in ENS) in
  // let (g1, ..., gn) = g in
  let s0 = Reserved "s0" in
  let fM = Reserved "fM" in
  let sM = Reserved "sM" in
  let g = Reserved "g" in
  let mods = Reserved "mods" in
  let qc = Reserved "qc" in
  let (_, pmods, _) = makeFrame env true p s0 sM in
  let ePMods = eapply (Id "list") pmods in
  let sMods = SAssign ([(mods, Some (Some (TName (Reserved "mods_t")), Ghost))], ePMods) in
//  let wpSound_X = Reserved ("wpSound_" + (string_of_id p.pname)) in
  let wpSound_X = Reserved "wp_sound_code_norm" in
  let qCodes_X = Reserved ("qcode_" + (string_of_id p.pname)) in
  let ghostRets = List.collect (fun (x, t, g, _, _) -> match g with XGhost -> [(x, t)] | _ -> []) p.prets in
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let letGs = ebind BindLet [evar g] gAssigns [] (hide_ifs ens) in
  let funCont = ebind Lambda [] [(s0, None); (sM, None); (g, None)] [] letGs in
  let args = qmods_opt (evar mods) @ args in
  let sQc = SAssign ([(qc, None)], eapply qCodes_X args) in
  let eWpSound = eapply wpSound_X [code; evar qc; evar s0; funCont] in
  let sWpSound = SAssign ([(sM, None); (fM, None); (g, None)], eWpSound) in
  // assert_norm (va_qc.mods == va_mods)
  let eQcMods = eop (FieldOp (Id "mods")) [evar qc] in
  let sQcNorm = SAssign ([], eapply (Id "assert_norm") [eop (Bop (BEq BpProp)) [eQcMods; evar mods]]) in
  // va_lemma_norm_mods va_mods va_sM va_s0
  let sLemmaNormMods = SAssign ([], eapply (Reserved "lemma_norm_mods") [ePMods; evar sM; evar s0]) in
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let sAssignGs =
    match ghostRets with
    | [] -> []
    | _ -> [SAssign (gAssigns, evar g)]
    in
  expansions @ qmods_opt sMods @ [sQc; sWpSound] @ qmods_opt sQcNorm @ qmods_opt sLemmaNormMods @ sAssignGs
