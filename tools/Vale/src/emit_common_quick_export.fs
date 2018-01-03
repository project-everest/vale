// Export declarations for '{:quick}' procedures

module Emit_common_quick_export

open Ast
open Ast_util
open Parse
open Parse_util
open Transform
open Emit_common_base
open Microsoft.FSharp.Math
open System.Numerics

(*
Example: Add64
  X = Add64
  PARAMS = (dst:va_operand_dst_opr64) (src:va_operand_opr64)
  ARGS = dst src
  A = unit
  MODS = (x:nat64) (flags:nat64)
  GHOSTRETS = (g1:t1) ... (gn:tn)
  REQ = (va_is_dst_dst_opr64 dst s0) /\ (va_is_src_opr64 src s0) /\ s0.ok /\ (va_eval_opr64 s0 src) + (va_eval_dst_opr64 s0 dst) < nat64_max
  ENS = x == (va_eval_dst_opr64 s0 dst) + (va_eval_opr64 s0 src)
  UPDATES = (update_operand dst x ({s0 with flags = flags}))
  UPDATES_SM = (update_operand dst (eval_operand dst sM) ({s0 with flags = sM.flags}))

// Function
let wp_X PARAMS (s0:state) (wpContinue:state -> A -> Type0) : Type0 =
  REQ(s0) /\
  (forall MODS GHOSTRETS.
    let sM = UPDATES(s0, MODS) in
    ENS(s0, sM) ==>
    wpContinue sM (g1, ..., gn)
  )

// Procedure
val wpProof_X PARAMS (aN:Type0) (qs:state -> state * fuel * aN -> Type0) (s0:state) (wpContinue:(state -> A -> Type0)) :
  Ghost (sM:state & f0:fuel & g:A & va_quickProc_q aN (qs sM) True (va_quickProc_q aN (qs sM) (wpContinue sM g) unit))
  (requires wp_X ARGS s0 wpContinue)
  (ensures fun (|sM, f0, _, _|) -> eval_code (va_code_X ARGS) s0 f0 sM)

let wpProof_X ARGS aN qs s0 wpContinue =
  let (sM, f0, g1, ..., gn) = va_lemma_X (va_code_X ARGS) s0 ARGS in
  let g = (g1, ..., gn) in
  va_lemma_upd_update sM;
  assert (state_eq sM UPDATES_SM);
  let f : (va_quickProc_q aN (qs sM) (wpContinue sM g) unit -> Ghost (state * fuel * aN) True (qs sM)) = fun x -> x () in
  (|sM, f0, g, f|)

// Function
[@"opaque_to_smt"]
let quick_X PARAMS : quickCode A (va_code_X ARGS) =
  va_QProc (va_code_X ARGS) (wp_X ARGS) (wpProof_X ARGS)
*)

let makeFrame (env:env) (p:proc_decl) (s0:id) (sM:id):exp * formal list =
  let id_x (x:id) = Reserved ("x_" + string_of_id x) in
  let specModsIo = List.collect (Emit_common_lemmas.specModIo env false) p.pspecs in
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
  let mods = List.collect collectMod specModsIo in
  let args = (List.collect (collectArg true) p.prets) @ (List.collect (collectArg false) p.pargs) in
  let frameArg e (x, xx, t) = vaApp ("upd_" + (vaOperandTyp t)) [EVar x; EVar xx; e] in
  let frameMod e (x, _, prefix, es) = vaApp ("upd_" + prefix) (es @ [EVar x; e]) in
  let e = EVar s0 in
  let e = List.fold frameArg e args in
  let e = List.fold frameMod e mods in
  let fs = [] in
  let fs = List.fold (fun fs (_, xx, t) -> (xx, Some (tOperand (vaValueTyp t)))::fs) fs args in
  let fs = List.fold (fun fs (x, t, _, _) -> (x, Some t)::fs) fs mods in
  (e, List.rev fs)

let build_proc (env:env) (loc:loc) (p:proc_decl):decls =
  let makeParam (x, t, storage, io, attrs) =
    match storage with
    | XOperand -> (x, tOperand (vaOperandTyp t), storage, io, attrs)
    | _ -> (x, t, storage, io, attrs)
    in
  let pargs = List.map makeParam p.pargs in
  let fParams = List.map (fun (x, t, _, _, _) -> (x, Some t)) pargs in
  let fParamsCode = List.collect (fun (x, t, storage, _, _) -> match storage with XGhost -> [] | _ -> [(x, Some t)]) pargs in
  let xArgs = List.map fst fParams in
  let xArgsCode = List.map fst fParamsCode in
  let tArgs = List.map (fun x -> TName x) xArgs in
  let eArgs = List.map (fun x -> EVar x) xArgs in
  let tArgsCode = List.map (fun x -> TName x) xArgsCode in
  let eArgsCode = List.map (fun x -> EVar x) xArgsCode in
  let eUnit = EApply (Id "tuple", []) in
  let tType0 = TName (Id "Type0") in
  let tUnit = TName (Id "unit") in
  let tTrue = TName (Id "True") in
  let ghostRets = List.collect (fun (x, t, g, _, _) -> match g with XGhost -> [(x, t)] | _ -> []) p.prets in
  let tA =
    match ghostRets with
    | [] -> tUnit
    | [(_, t)] -> t
    | xts -> TApp (TName (Id "tuple"), List.map snd xts)
    in
  let wp_X = Reserved ("wp_" + (string_of_id p.pname)) in
  let wpProof_X = Reserved ("wpProof_" + (string_of_id p.pname)) in
  let lemma_X = Reserved ("lemma_" + (string_of_id p.pname)) in
  let aN = Reserved "aN" in
  let qs = Reserved "qs" in
  let s0 = Reserved "s0" in
  let sM = Reserved "sM" in
  let f0 = Reserved "f0" in
  let x = Reserved "x" in
  let g = Reserved "g" in
  let f = Reserved "f" in
  let pf = Reserved "pf" in
  let quickProc_q = Reserved "quickProc_q" in
  let wpContinue = Reserved "wpContinue" in
  let tAN = TName aN in
  let tContinue = TApp (TName (Id "fun"), [tState; tA; tType0]) in
  let argContinue = (wpContinue, Some tContinue) in
  let tCode = TApp (TName (Reserved ("code_" + (string_of_id p.pname))), tArgsCode) in
  let eCode = EApply (Reserved ("code_" + (string_of_id p.pname)), eArgsCode) in

  let reqIsExps =
    (List.collect (Emit_common_lemmas.reqIsArg s0 true) p.prets) @
    (List.collect (Emit_common_lemmas.reqIsArg s0 false) p.pargs)
    in

  // wp_X
  let ghostRetTuple = EApply (Id "tuple", List.map (fun (x, _) -> EVar x) ghostRets) in
  let ghostRetFormals = List.map (fun (x, t) -> (x, Some t)) ghostRets in
  let (pspecs, pmods) = List.unzip (List.map (Emit_common_lemmas.build_lemma_spec env s0 (EVar sM)) p.pspecs) in
  let (updatesX, wpFormals) = makeFrame env p s0 sM in
  let (wpReqs, wpEnss) = collect_specs (List.concat pspecs) in
  let (wpReq, wpEns) = (and_of_list (reqIsExps @ wpReqs), and_of_list wpEnss) in
  let continueM = EApply (wpContinue, [EVar sM; ghostRetTuple]) in
  let ensContinue = EOp (Bop BImply, [wpEns; continueM]) in
  let letEnsContinue = EBind (BindLet, [updatesX], [(sM, None)], [], ensContinue) in
  let wpForall = EBind (Forall, [], wpFormals @ ghostRetFormals, [], letEnsContinue) in
  let wpBody = EOp (Bop BAnd, [wpReq; wpForall]) in
  let fWp =
    {
      fname = wp_X;
      fghost = NotGhost;
      fargs = fParams @ [(s0, Some tState); argContinue];
      fret = tType0;
      fbody = Some wpBody;
      fattrs = [(Id "public", [])];
    }
    in
  // wpProof_X declaration
  let tRetQuick = TApp (TName (Reserved "quickCode"), [tA; tCode]) in
  let tQsTuple = TApp (TName (Id "tuple"), [tState; tFuel; tAN]) in
  let tQs = TApp (TName (Id "fun"), [tState; tQsTuple; tType0]) in
  let arg x t = (x, t, XGhost, In, []) in
  let pAN = arg aN tType0 in
  let pQs = arg qs tQs in
  let pS0 = arg s0 tState in
  let pWpContinue = arg wpContinue tContinue in
  let rSM = arg sM tState in
  let rF0 = arg f0 tFuel in
  let rG = arg g tA in
  let tQ = TApp (TName qs, [TName sM]) in
  let tWpContinue = TApp (TName wpContinue, [TName sM; TName g]) in
  let tPf1 = TApp (TName quickProc_q, [tAN; tQ; tWpContinue; tUnit]) in
  let tPf2 = TApp (TName quickProc_q, [tAN; tQ; tTrue; tPf1]) in
  let rPf = arg pf tPf2 in
  let specReq = Requires (Unrefined, EApply (wp_X, eArgs @ [EVar s0; EVar wpContinue])) in
  let specEns = Ensures (Unrefined, EApply (Id "eval_code", [eCode; EVar s0; EVar f0; EVar sM])) in
  // wpProof_X body
  //   let (sM, f0, g1, ..., gn) = va_lemma_X (va_code_X ARGS) s0 ARGS in
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let sCallLemma = SAssign ((sM, None)::(f0, None)::gAssigns, EApply (lemma_X, eCode::(EVar s0)::eArgs)) in
  let sAssignG = SAssign ([(g, None)], ghostRetTuple) in
  let sLemmaUpd = SAssign ([], EApply (Reserved "lemma_upd_update", [EVar sM])) in
  let (_, eqUpdates) = Emit_common_lemmas.makeFrame env p s0 sM in
  let sAssertEq = SAssert (assert_attrs_default, eqUpdates) in
  //   let f : (va_quickProc_q aN (qs sM) (wpContinue sM g) unit -> Ghost (state * fuel * aN) True (qs sM)) = fun x -> x () in
  let tFRet = TApp (TName (Id "Ghost"), [tQsTuple; tTrue; tQ]) in
  let tF = TApp (TName (Id "fun"), [tPf1; tFRet]) in
  let eLambda = EBind (Lambda, [], [(x, None)], [], EApply (x, [eUnit])) in
  let sAssignF = SAssign ([(f, Some (Some tF, Ghost))], eLambda) in
  let sAssignPf = SAssign ([(pf, None)], EVar f) in
  let pProof =
    {
      pname = wpProof_X;
      pghost = Ghost;
      pinline = Outline;
      pargs = pargs @ [pAN; pQs; pS0; pWpContinue];
      prets = [rSM; rF0; rG; rPf];
      pspecs = [(loc, specReq); (loc, specEns)];
      pbody = Some [sCallLemma; sAssignG; sLemmaUpd; sAssertEq; sAssignF; sAssignPf];
      pattrs = [(Id "dependent", [])]
    }
    in
  // quick_X
  //   va_QProc (va_code_X ARGS) (wp_X ARGS) (wpProof_X ARGS)
  let applyOpt f args = match args with [] -> EVar f | _ -> EApply (f, args) in
  let wpArgs = applyOpt wp_X eArgs in
  let applyProof = applyOpt wpProof_X eArgs in
  let eQuick = EApply (Reserved "QProc", [eCode; wpArgs; applyProof]) in
  let fQuick =
    {
      fname = Reserved ("quick_" + (string_of_id p.pname));
      fghost = NotGhost;
      fargs = fParams;
      fret = tRetQuick;
      fbody = Some eQuick;
      fattrs = [(Id "public", []); (Id "opaque_to_smt", [])];
    }
    in
  [(loc, DFun fWp); (loc, DProc pProof); (loc, DFun fQuick)]
