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
let wp_X PARAMS (s0:state) (k:state -> A -> Type0) : Type0 =
  REQ(s0) /\
  (forall MODS GHOSTRETS.
    let sM = UPDATES(s0, MODS) in
    ENS(s0, sM) ==>
    k sM (g1, ..., gn)
  )

// Procedure
val wpMonotone_X PARAMS (s0:state) (k1:state -> A -> Type0) (k2:state -> A -> Type0) : Lemma
  (requires (forall (s:state) (g:A). k1 s g ==> k2 s g))
  (ensures wp_X ARGS s0 k1 ==> wp_X ARGS s0 k2) =
let wpMonotone_X s0 k1 k2 = ()

val wpCompute_X PARAMS (s0:state) : Ghost (state * fuel * A)
  (requires wp_X ARGS s0 k_true)
  (ensures fun _ -> True)
let wpCompute_X s0 =
  let (sM, f0, g1, ..., gn) = va_lemma_X (va_code_X ARGS) s0 ARGS in
  let g = (g1, ..., gn) in
  (sM, f0, g)

val wpProof_X PARAMS (s0:state) (k:state -> A -> Type0) : Lemma
  (requires wp_X ARGS s0 k)
  (ensures t_ensure (va_code_X ARGS) (wp_X ARGS) (wpMonotone_X ARGS) (wpCompute_X ARGS) s0 k)
let wpProof_X s0 k =
  let (sM, f0, g1, ..., gn) = va_lemma_X (va_code_X ARGS) s0 ARGS in
  va_lemma_upd_update sM;
  assert (state_eq sM UPDATES_SM);
  ()

// Function
[@"opaque_to_smt"]
let quick_X PARAMS : quickCode A (va_code_X ARGS) =
  va_QProc (va_code_X ARGS) (wp_X ARGS) (wpMonotone_X ARGS) (wpCompute_X ARGS) (wpProof_X ARGS)
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
  let eTrue = EVar (Id "True") in
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
  let wpMonotone_X = Reserved ("wpMonotone_" + (string_of_id p.pname)) in
  let wpCompute_X = Reserved ("wpCompute_" + (string_of_id p.pname)) in
  let wpProof_X = Reserved ("wpProof_" + (string_of_id p.pname)) in
  let lemma_X = Reserved ("lemma_" + (string_of_id p.pname)) in
  let s = Reserved "s" in
  let s0 = Reserved "s0" in
  let sM = Reserved "sM" in
  let f0 = Reserved "f0" in
  let x = Reserved "x" in
  let g = Reserved "g" in
  let k = Reserved "k" in
  let k1 = Reserved "k1" in
  let k2 = Reserved "k2" in
  let k_true = Id "k_true" in
  let tContinue = TApp (TName (Id "fun"), [tState; tA; tType0]) in
  let argContinue = (k, Some tContinue) in
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
  let (wpReqs, wpEnss) = collect_specs false (List.concat pspecs) in
  let (wpReq, wpEns) = (and_of_list (reqIsExps @ wpReqs), and_of_list wpEnss) in
  let continueM = EApply (k, [EVar sM; ghostRetTuple]) in
  let ensContinue = EOp (Bop BImply, [wpEns; continueM]) in
  let letEnsContinue = EBind (BindLet, [updatesX], [(sM, None)], [], ensContinue) in
  let wpForall = EBind (Forall, [], wpFormals @ ghostRetFormals, [], letEnsContinue) in
  let wpBody = EOp (Bop BLand, [wpReq; wpForall]) in
  let fWp =
    {
      fname = wp_X;
      fghost = NotGhost;
      fargs = fParams @ [(s0, Some tState); argContinue];
      fret = tType0;
      fbody = Some (hide_ifs wpBody);
      fattrs = [(Id "public", []); (Id "qattr", [])] @ attr_no_verify "lax" p.pattrs;
    }
    in

  // wpMonotone_X declaration
  let applyOpt f args = match args with [] -> EVar f | _ -> EApply (f, args) in
  let appArgs x = applyOpt x eArgs in
  let arg x t = (x, t, XGhost, In, []) in
  let pS0 = arg s0 tState in
  let pK1 = arg k1 tContinue in
  let pK2 = arg k2 tContinue in
  let appSG k = EApply (k, [EVar s; EVar g]) in
  let reqImp = EOp (Bop BImply, [appSG k1; appSG k2]) in
  let reqForall = EBind (Forall, [], [(s, Some tState); (g, Some tA)], [], reqImp) in 
  let appWp k = EApply (wp_X, eArgs @ [EVar s0; EVar k]) in
  let ensImp = EOp (Bop BImply, [appWp k1; appWp k2]) in
  let specReq = Requires (Unrefined, reqForall) in
  let specEns = Ensures (Unrefined, ensImp) in
  // wpMonotone_X body
  let pMonotone =
    {
      pname = wpMonotone_X;
      pghost = Ghost;
      pinline = Outline;
      pargs = pargs @ [pS0; pK1; pK2];
      prets = [];
      pspecs = [(loc, specReq); (loc, specEns)];
      pbody = Some [];
      pattrs = attr_no_verify "admit" p.pattrs;
    }
    in

  // wpCompute_X declaration
  let rSM = arg sM tState in
  let rF0 = arg f0 tFuel in
  let rG = arg g tA in
  let specReq = Requires (Unrefined, EApply (wp_X, eArgs @ [EVar s0; EVar k_true])) in
  let specEns = Ensures (Unrefined, eTrue) in
  // wpCompute_X body
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let sCallLemma = SAssign ((sM, None)::(f0, None)::gAssigns, EApply (lemma_X, eCode::(EVar s0)::eArgs)) in
  let sAssignG = SAssign ([(g, None)], ghostRetTuple) in
  let pCompute=
    {
      pname = wpCompute_X;
      pghost = Ghost;
      pinline = Outline;
      pargs = pargs @ [pS0];
      prets = [rSM; rF0; rG];
      pspecs = [(loc, specReq); (loc, specEns)];
      pbody = Some [sCallLemma; sAssignG];
      pattrs = [(Id "reducible", [])] @ attr_no_verify "admit" p.pattrs;
    }
    in

  // wpProof_X declaration
  let pK = arg k tContinue in
  let specEnsArgs = [eCode; appArgs wp_X; appArgs wpMonotone_X; appArgs wpCompute_X; EVar s0; EVar k] in
  let specReq = Requires (Unrefined, EApply (wp_X, eArgs @ [EVar s0; EVar k])) in
  let specEns = Ensures (Unrefined, EApply (Id "t_ensure", specEnsArgs)) in
  // wpProof_X body
  let sLemmaUpd = SAssign ([], EApply (Reserved "lemma_upd_update", [EVar sM])) in
  let (_, eqUpdates) = Emit_common_lemmas.makeFrame env p s0 sM in
  let sAssertEq = SAssert (assert_attrs_default, eqUpdates) in
  let pProof =
    {
      pname = wpProof_X;
      pghost = Ghost;
      pinline = Outline;
      pargs = pargs @ [pS0; pK];
      prets = [];
      pspecs = [(loc, specReq); (loc, specEns)];
      pbody = Some [sCallLemma; sLemmaUpd; sAssertEq];
      pattrs = attr_no_verify "admit" p.pattrs;
    }
    in

  // quick_X
  //   va_QProc (va_code_X ARGS) (wp_X ARGS) (wpProof_X ARGS)
  //   va_QProc (va_code_X ARGS) (wp_X ARGS) (wpMonotone_X ARGS) (wpCompute_X ARGS) (wpProof_X ARGS)
  let tRetQuick = TApp (TName (Reserved "quickCode"), [tA; tCode]) in
  let eQuick = EApply (Reserved "QProc", [eCode; appArgs wp_X; appArgs wpMonotone_X; appArgs wpCompute_X; appArgs wpProof_X]) in
  let fQuick =
    {
      fname = Reserved ("quick_" + (string_of_id p.pname));
      fghost = NotGhost;
      fargs = fParams;
      fret = tRetQuick;
      fbody = Some eQuick;
      fattrs = [(Id "public", []); (Id "opaque_to_smt", []); (Id "qattr", [])] @ attr_no_verify "lax" p.pattrs;
    }
    in
  [(loc, DFun fWp); (loc, DProc pMonotone); (loc, DProc pCompute); (loc, DProc pProof); (loc, DFun fQuick)]
