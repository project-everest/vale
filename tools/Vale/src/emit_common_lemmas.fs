module Emit_common_lemmas

open Ast
open Ast_util
open Parse
open Parse_util
open TypeChecker
open Transform
open Emit_common_base
open Microsoft.FSharp.Math
open System.Numerics

type build_env =
  {
    proc:proc_decl;
    loc:loc;
    is_instruction:bool;
    is_quick:bool;
    is_operand:bool;
    is_framed:bool;
    is_terminating:bool;
    code_name:string -> id;
    frame_exp:id -> exp * exp;
    gen_quick_block:env -> quick_info -> lhs list -> exp list -> stmt list -> stmt list;
    gen_quick_block_funs:unit -> decls;
    quick_code_funs:fun_decl list ref;
  }

(* Build code value for body of procedure Q:
function method{:opaque} va_code_Q(...):va_code
{
  va_Block(va_CCons(va_code_P(va_op_reg(EBX), 10), va_CCons(va_code_P(va_op_reg(EBX), 20), va_CCons(va_code_P(va_op_reg(EBX), 30), va_CNil()))))
}
*)
let rec build_code_stmt (env:env) (benv:build_env) (s:stmt):exp list =
  let rs = build_code_block env benv in
  let rec assign e =
    match e with
    | ELoc (_, e) -> assign e
    | EApply (e, _, es, t) when is_id e && is_proc env (id_of_exp e) NotGhost->
        let x = string_of_id (id_of_exp e) in
        let es = List.filter (fun e -> match e with EOp (Uop UGhostOnly, _, _) -> false | _ -> true) es in
        let es = List.map get_code_exp es in
        let es = List.map (map_exp stateToOp) es in
        [vaApp_t ("code_" + x) es t]
    | _ -> []
    in
  match s with
  | SLoc (loc, s) ->
      try List.map (fun e -> ELoc (loc, e)) (build_code_stmt env benv s) with err -> raise (LocErr (loc, err))
  | SBlock b -> [rs b]
  | SQuickBlock (info, b) ->
      // REVIEW: would be more consistent to generate a value of type "code" rather than "codes",
      // but the normalization doesn't seem to work as well for "code".
      let p = benv.proc in
      let fParams = make_fun_params p.prets p.pargs in
      let name = benv.code_name (info.qsym + "_") in
      let f =
        {
          fname = name;
          fghost = NotGhost;
          ftargs = [];
          fargs = fParams;
          fret_name = None;
//          fret = tCode;
          fret = tCodes;
          fspecs = [];
//          fbody = Some (rs b);
          fbody = Some (build_code_stmts env benv b);
          fattrs = [(Id "opaque_to_smt", []); (Id "qattr", [])] @ attr_no_verify "admit" benv.proc.pattrs;
        }
        in
      benv.quick_code_funs := f::!(benv.quick_code_funs);
      let e = eapply name (List.map (fun (x, t) -> EVar(x,t)) fParams) in
//      [e]
      [vaApp "Block" [e]]
  | SIfElse (SmPlain, cmp, ss1, ss2) ->
      let e1 = rs ss1 in
      let e2 = rs ss2 in
      [vaApp_t "IfElse" [map_exp stateToOp cmp; e1; e2] (exp_typ e1)]
  | SIfElse (SmInline, cmp, ss1, ss2) ->
      let e1 = rs ss1 in
      let e2 = rs ss2 in
      [EOp (Cond, [map_exp stateToOp cmp; e1; e2], (exp_typ e1))]
  | SWhile (cmp, ed, invs, ss) ->
      let ess = rs ss in
      [vaApp "While" [map_exp stateToOp cmp; ess]]
  | SAssign (_, e) -> assign e
  | _ -> []
and build_code_stmts (env:env) (benv:build_env) (stmts:stmt list):exp =
  let empty = vaApp "CNil" [] in
  let cons el e = vaApp "CCons" [e; el] in
  let slist = List.collect (build_code_stmt env benv) stmts in
  List.fold cons empty (List.rev slist)
and build_code_block (env:env) (benv:build_env) (stmts:stmt list):exp =
  vaApp "Block" [build_code_stmts env benv stmts]

// compute parameters/returns for procedures (abstract/concrete/lemma)
// pfIsRet == false ==> pf is input parameter
// pfIsRet == true ==> pf is output return value
// ret == false ==> generate parameters
// ret == true ==> generate return values
let make_proc_param (modifies:bool) (pfIsRet:bool) (ret:bool) (pf:pformal):pformal list =
  let (x, t, storage, io, attrs) = pf in
  let pfOp xo = (x, tOperand xo, XPhysical, In, attrs) in
  match (ret, storage, pfIsRet, modifies) with
  | (_, XGhost, _, false) -> if ret = pfIsRet then [pf] else []
  | (_, _, _, true) -> []
  | (false, XInline, false, false) -> [pf]
  | (_, XOperand, _, false) -> if ret = pfIsRet then [pfOp (vaOperandTyp t)] else []
  | (_, XAlias _, _, false) -> []
  | (true, XInline, false, _) -> []
  | (_, XInline, true, _) -> internalErr "XInline"
  | (_, XState _, _, _) -> internalErr "XState"
  | (_, XPhysical, _, _) -> internalErr "XPhysical"

let make_proc_params (ret:bool) (prets:pformal list) (pargs:pformal list):pformal list =
  (List.collect (make_proc_param false true ret) prets) @
  (List.collect (make_proc_param true true ret) prets) @
  (List.collect (make_proc_param false false ret) pargs) @
  (List.collect (make_proc_param true false ret) pargs)

type stmt_env =
  {
    env:env;
    benv:build_env;
    b1:id; // code in forward order, shrinking to []
    bM:id;
    code:exp;
    s0:id;
    f0:id;
    sM:id;
    fM:id;
    sN:id;
    loc:loc;
  }

let listIf (b:bool) (l:'a list) = if b then l else []
let listIfNot (b:bool) (l:'a list) = if b then [] else l
let total_suffix (b:bool) = if b then "_total" else ""

let lemma_block (total:bool) (sM:lhs) (cM:lhs) (bM:lhs) (f0:lhs) (eb:exp) (es0:exp) (esN:exp):stmt list =
  let xBlock = "lemma_block" + total_suffix total in
  let eBlock = vaApp xBlock (listIfNot total [eb; es0; esN]) in
  //[SAssign ((if total then [f0] else [sM; cM; bM]), eBlock)] // ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  listIfNot total [SAssign ([sM; cM; bM], eBlock)]

let rec build_lemma_stmt (senv:stmt_env) (s:stmt):ghost * bool * stmt list =
  let env = senv.env in
  let benv = senv.benv in
  let loc = senv.loc in
  let s0 = senv.s0 in
  let sM = senv.sM in
  let code = senv.code in
  let sub es e = subst_reserved_exp (Map.ofList [(Reserved "s", es)]) e in
  let sub_s0 e = sub (evar s0) e in
  let total = benv.is_terminating in
  let rec assign lhss e =
    let lhss = List.map (fun xd -> match xd with (Reserved "s", None) -> (s0, None) | _ -> xd) lhss in
    match e with
    | ELoc (loc, e) -> try assign lhss e with err -> raise (LocErr (loc, err))
    | EApply (e, _, es, t) when is_id e && is_proc env (id_of_exp e) NotGhost ->
        let x = id_of_exp e in
        let p = Map.find x env.procs in
        let pargs = List.filter (fun (_, _, storage, _, _) -> match storage with XAlias _ -> false | _ -> true) p.pargs in
        let (pretsOp, pretsNonOp) = List.partition (fun (_, _, storage, _, _) -> match storage with XOperand -> true | _ -> false) p.prets in
        let pretsArgs = pretsOp @ pargs in
        let es = List.map (fun e -> match e with EOp (Uop UGhostOnly, [e], _) -> sub_s0 e | _ -> e) es in
        let es = List.map (fun e -> match e with EOp (CodeLemmaOp, [_; e], _) -> sub_s0 e | _ -> e) es in
        let es = List.map (map_exp stateToOp) es in
        let xLemma = "lemma_" + (string_of_id x) in
        let bh = if total then vaApp "hd" [evar senv.b1] else evar senv.b1 in
        let lem = vaApp_t xLemma ([bh; evar s0] @ listIfNot total [evar senv.sN] @ es) t in
        let blockLhss = List.map varLhsOfId (if total then [sM; senv.fM] else [senv.bM; sM]) in
        let sLem = SAssign (blockLhss @ lhss, lem) in
        (NotGhost, false, [sLem])
    | EApply (e, ts, es, t) when is_proc env (id_of_exp e) Ghost ->
        let es = List.map (fun e -> match e with EOp (Uop UGhostOnly, [e], _) -> sub_s0 e | _ -> sub_s0 e) es in
        let e = EApply (e, ts, es, t)
        (Ghost, false, [SAssign (lhss, e)])
    | _ -> (Ghost, false, [SAssign (lhss, sub_s0 e)])
    in
  match s with
  | SLoc (loc, s) ->
      try
        let (g, b, ss) = build_lemma_stmt {senv with loc = loc} s in
        (g, b, List.map (fun s -> SLoc (loc, s)) ss)
      with err -> raise (LocErr (loc, err))
  | SLabel _ -> err "unsupported feature: labels (unstructured code)"
  | SGoto _ -> err "unsupported feature: 'goto' (unstructured code)"
  | SReturn _ -> err "unsupported feature: 'return' (unstructured code)"
  | SAssume e -> (Ghost, false, [SAssume (sub_s0 e)])
  | SAssert (attrs, e) -> (Ghost, false, [SAssert (attrs, sub_s0 e)])
  | SCalc (op, contents, e) ->
      let ccs = List.map (build_lemma_calcContents senv sub_s0) contents in
      (Ghost, false, [SCalc (op, ccs, sub_s0 e)])
  | SVar (_, _, _, (XPhysical | XOperand | XInline | XAlias _), _, _) -> (Ghost, false, [])
  | SVar (x, t, m, g, a, eOpt) -> (Ghost, false, [SVar (x, t, m, g, a, mapOpt sub_s0 eOpt)])
  | SAlias _ -> (Ghost, false, [])
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SBlock b -> (NotGhost, true, build_lemma_block senv b)
  | SQuickBlock (info, b) ->
      let outS = (sM, Some (Some tState, Ghost)) in
      let outF = (senv.fM, Some (Some tFuel, Ghost)) in
      let outG = (Reserved "g", None) in
      let ss = benv.gen_quick_block env info [outS; outF; outG] [evar s0] b in
      (NotGhost, true, ss)
  | SIfElse (SmGhost, e, ss1, ss2) ->
      let e = sub_s0 e in
      let ss1 = build_lemma_ghost_stmts senv ss1 in
      let ss2 = build_lemma_ghost_stmts senv ss2 in
      (Ghost, false, [SIfElse (SmGhost, e, ss1, ss2)])
  | SIfElse (SmPlain, e, ss1, ss2) ->
      let codeId = match code with EVar (x, _) -> x | _ -> internalErr (sprintf "SIfElse: %A" code) in
      let cond = Reserved ("cond_" + (reserved_id codeId)) in
      let i1 = string (gen_lemma_sym ()) in
      let s1 = Reserved("s" + i1) in
      let sCode = listIf total [SAssign ([varLhsOfId codeId], vaApp "hd" [evar senv.b1])] in
      let codeCond = vaApp "get_ifCond" [code] in
      let codet = vaApp "get_ifTrue" [code] in
      let codef = vaApp "get_ifFalse" [code] in
      let xIfElse = "lemma_ifElse" + total_suffix total in
      let lem = vaApp xIfElse ([codeCond; codet; codef; evar s0] @ listIfNot total [evar sM]) in
      let s1Lhs = (s1, Some (Some tState, Ghost)) in
      let sMLhs = (senv.sM, Some (Some tState, Ghost)) in
      let fMLhs = (senv.fM, Some (Some tFuel, Ghost)) in
      let sb1 = SAssign ([varLhsOfId cond; s1Lhs] @ listIf total [sMLhs; fMLhs], lem) in
      let sbT = build_lemma_block { senv with s0 = s1; code = codet } ss1 in
      let sbF = build_lemma_block { senv with s0 = s1; code = codef } ss2 in
      let lemT = vaApp "lemma_ifElseTrue_total" [codeCond; codet; codef; evar s0; evar senv.f0; evar senv.sM] in
      let lemF = vaApp "lemma_ifElseFalse_total" [codeCond; codet; codef; evar s0; evar senv.f0; evar senv.sM] in
      let slemT = listIf total [SAssign ([], lemT)] in
      let slemF = listIf total [SAssign ([], lemF)] in
      (NotGhost, true, sCode @ [sb1; SIfElse (SmPlain, evar cond, sbT @ slemT, sbF @ slemF)])
  | SIfElse (SmInline, e, ss1, ss2) ->
      let codeId = match code with EVar (x, _) -> x | _ -> internalErr (sprintf "SIfElse: %A" code) in
      let sCode = listIf total [SAssign ([varLhsOfId codeId], vaApp "hd" [evar senv.b1])] in
      let sState = listIf total [SVar (senv.sM, None, Mutable, XGhost, [], None)] in
      let sFuel = listIf total [SVar (senv.fM, None, Mutable, XGhost, [], None)] in
      let sbT = build_lemma_block senv ss1 in
      let sbF = build_lemma_block senv ss2 in
      (NotGhost, true, sCode @ sState @ sFuel @ [SIfElse (SmPlain, e, sbT, sbF)])
  | SWhile (e, invs, ed, ss) ->
      let codeId = match code with EVar (x, _) -> x | _ -> internalErr (sprintf "SWhile: %A" code) in
      let sCode = listIf total [SAssign ([varLhsOfId codeId], vaApp "hd" [evar senv.b1])] in
      let codeCond = vaApp "get_whileCond" [code] in
      let codeBody = vaApp "get_whileBody" [code] in
      let i1 = string (gen_lemma_sym ()) in
      let i2 = string (gen_lemma_sym ()) in
      let (n1, s1, sw1, fw1) = (Reserved ("n" + i1), Reserved ("s" + i1), Reserved ("sW" + i1), Reserved ("fW" + i1)) in
      let (sw2, fw2) = (Reserved ("sW" + i2), Reserved ("fW" + i2)) in
      let (codeCond, codeBody, sCodeVars) =
        if !fstar then
          // REVIEW: workaround for F* issue
          let (xc, xb) = (Reserved ("sC" + i1), Reserved ("sB" + i1)) in
          let sCond = SAssign ([(xc, None)], codeCond) in
          let sBody = SAssign ([(xb, None)], codeBody) in
          (evar xc, evar xb, [sCond; sBody])
        else (codeCond, codeBody, [])
        in
      let ts = total_suffix total in
      let lem = vaApp ("lemma_while" + ts) ([codeCond; codeBody; evar s0] @ listIfNot total [evar sM]) in
      let lemTrue = vaApp ("lemma_whileTrue" + ts) ([codeCond; codeBody] @ (if total then [evar s0; evar sw1; evar fw1] else [evar n1; evar sw1; evar sM])) in
      let lemFalse = vaApp ("lemma_whileFalse" + ts) ([codeCond; codeBody] @ (if total then [evar s0; evar sw1; evar fw1] else [evar sw1; evar sM])) in
      let n1Lhs = (n1, Some (Some tInt, Ghost)) in
      let s1Lhs = (s1, Some (Some tState, Ghost)) in
      let sw1Lhs = (sw1, Some (Some tState, Ghost)) in
      let fw1Lhs = (fw1, Some (Some tFuel, Ghost)) in
      let sw2Lhs = (sw2, Some (Some tState, Ghost)) in
      let fw2Lhs = (fw2, Some (Some tFuel, Ghost)) in
      let slem = SAssign (listIfNot total [n1Lhs] @ [sw1Lhs] @ listIf total [fw1Lhs], lem) in
      let slemTrue = SAssign ([s1Lhs] @ (if total then [fw2Lhs] else [sw2Lhs]), lemTrue) in
      let slemFalse = SAssign ([(sM, None)] @ listIf total [(senv.fM, None)], lemFalse) in
      let whileInv = vaApp ("whileInv" + ts) ([codeCond; codeBody] @ (if total then [evar s0; evar sw1; evar fw1] else [evar n1; evar sw1; evar sM])) in
      let fw1Lemma = vaApp "lemma_whileMerge_total" [code; evar s0; evar fw1; evar sw1; evar fw2; evar sw2] in
      let fw1Update = SAssign ([(fw1, None)], fw1Lemma) in
      let sw1Update = SAssign ([(sw1, None)], evar sw2) in
      let n1Update = SAssign ([(n1, None)], eop (Bop BSub) [evar n1; EInt bigint.One]) in
      let sbBody = build_lemma_block { senv with code = codeBody; s0 = s1; sM = sw2; f0 = fw2 } ss in
      let nCond = eop (Bop BGt) [evar n1; EInt bigint.Zero] in
      let bCond = vaApp "evalCond" [codeCond; evar sw1] in
      let invFrame = (loc, snd (benv.frame_exp sw1)) in
      let invFrames = if benv.is_framed then [invFrame] else [] in
      let invs = List_mapSnd (sub (evar sw1)) invs in
      let ed =
        match ed with
        | (loc, []) -> if not total then (loc, [evar n1]) else err "terminating procedure must have decreases clause"
        | (loc, es) -> (loc, List.map (sub (evar sw1)) es)
        in
      let whileBody = slemTrue::sbBody @ listIf total [fw1Update] @ [sw1Update] @ listIfNot total [n1Update] in
      let sWhile = SWhile ((if total then bCond else nCond), (loc, whileInv)::invs @ invFrames, ed, whileBody) in
      (NotGhost, true, listIf total sCode @ sCodeVars @ [slem; sWhile; slemFalse])
  | SAssign (lhss, e) -> assign lhss e
  | SForall (xs, ts, ex, e, ss) ->
      let ts = List.map (List.map sub_s0) ts in
      let ex = sub_s0 ex in
      let e = sub_s0 e in
      let ss = build_lemma_ghost_stmts senv ss in
      (Ghost, false, [SForall (xs, ts, ex, e, ss)])
  | SExists (xs, ts, e) ->
      let ts = List.map (List.map sub_s0) ts in
      let e = sub_s0 e in
      (Ghost, false, [SExists (xs, ts, e)])
and build_lemma_ghost_stmt (senv:stmt_env) (s:stmt):stmt list =
  let (g, _, ss) = build_lemma_stmt { senv with sN = senv.sM } s in
  (match g with Ghost -> () | NotGhost -> err "Only ghost statements allowed here.  Ghost statements include 'forall', 'ghost if', lemma calls, assignments to ghost variables, assertions, etc, but not 'while' or 'if' or non-ghost procedure calls.");
  ss
and build_lemma_ghost_stmts (senv:stmt_env) (stmts:stmt list):stmt list =
  List.collect (build_lemma_ghost_stmt senv) stmts
and build_lemma_calcContents (senv:stmt_env) (sub_s0:exp -> exp) (cc:calcContents):calcContents =
  let {calc_exp = e; calc_op = oop; calc_hints = hints} = cc in
  {calc_exp = sub_s0 e; calc_op = oop; calc_hints = List.map (build_lemma_ghost_stmts senv) hints}
and build_lemma_stmts (senv:stmt_env) (stmts:stmt list):stmt list =
  let total = senv.benv.is_terminating in
  match stmts with
  | [] ->
      let xEmpty = "lemma_empty" + total_suffix total in
      let lem = vaApp xEmpty ([evar senv.s0] @ (if total then [evar senv.b1] else [evar senv.sM])) in
      [SAssign ([(senv.sM, None)] @ listIf total [(senv.f0, None)], lem)]
  | hd::tl ->
    (
      let i1 = string (gen_lemma_sym ()) in
      let (s1, f1, fc1, c1, b1) = (Reserved ("s" + i1), Reserved ("f" + i1), Reserved ("fc" + i1), Reserved ("c" + i1), Reserved ("b" + i1)) in
      let senv1 = { senv with bM = b1; code = evar c1; sM = s1; f0 = fc1; fM = fc1; sN = senv.sM } in
      let senv2 = { senv with b1 = b1; s0 = s1; f0 = f1; } in
      let (ghost, addBlockLemma, sb2) = build_lemma_stmt senv1 hd in
      let sTail = listIf total [SAssign ([varLhsOfId senv1.bM], vaApp "tl" [evar senv1.b1])] in
      let esMerge = [evar senv1.b1; evar senv1.s0; evar fc1; evar senv1.sM; evar f1; evar senv1.sN] in
      let sMerge = listIf total [SAssign ([(senv.f0, None)], vaApp "lemma_merge_total" esMerge)] in
      match (ghost, addBlockLemma) with
      | (Ghost, _) ->
          let sb3 = build_lemma_stmts senv tl in
          sb2 @ sb3
      | (NotGhost, true) ->
          let sLoc = one_loc_of_stmt senv.loc hd in
          let sb1 = lemma_block total (varLhsOfId s1) (varLhsOfId c1) (varLhsOfId b1) (senv.f0, None) (evar senv.b1) (evar senv.s0) (evar senv.sM) in
          let sb3 = build_lemma_stmts senv2 tl in
          sb1 @ sTail @ sb2 @ sb3 @ sMerge
      | (NotGhost, false) ->
          let sb3 = build_lemma_stmts senv2 tl in
          sb2 @ sTail @ sb3 @ sMerge
    )
and build_lemma_block (senv:stmt_env) (stmts:stmt list):stmt list =
  let total = senv.benv.is_terminating in
  let i0 = string (gen_lemma_sym ()) in
  let b0 = Reserved ("b" + i0) in
  let codeCond = vaApp "get_block" [senv.code] in
  let sb1 = SAssign ([varLhsOfId b0], codeCond) in
  let sb2 = build_lemma_stmts { senv with b1 = b0; } stmts in
  [sb1] @ sb2

let build_lemma_spec (env:env) (s0:id) (sM:exp) (loc:loc, s:spec):((loc * spec) list * exp list) =
  try
    match s with
    | Requires (r, e) ->
        let e = exp_refined e in
        let m = Map.ofList [(Reserved "old_s", evar s0); (Reserved "s", evar s0)] in
        ([(loc, Requires (r, subst_reserved_exp m e))], [])
    | Ensures (r, e) ->
        let e = exp_refined e in
        let m = Map.ofList [(Reserved "old_s", evar s0); (Reserved "s", sM)] in
        ([(loc, Ensures (r, subst_reserved_exp m e))], [])
    | Modifies (m, e) ->
        let e = exp_refined e in
        let m = Map.ofList [(Reserved "old_s", evar s0); (Reserved "s", evar s0)] in
        ([], [subst_reserved_exp m e])
    | SpecRaw _ -> internalErr "SpecRaw"
  with err -> raise (LocErr (loc, err))

// Generate well-formedness for operands:
//   requires va_is_dst_int(dummy, s0)
let reqIsArg (s0:id) (isRet:bool) ((x, t, storage, io, _):pformal):exp list =
  match (isRet, storage, io) with
  | (true, XOperand, _) | (false, XOperand, (InOut | Out)) -> [vaAppOp ("is_dst_") t [evar x; evar s0] (Some (TBool BpBool))]
  | (false, XOperand, In) -> [vaAppOp ("is_src_") t [evar x; evar s0] (Some (TBool BpBool))]
  | _ -> []
  in

// Generate framing postcondition, which limits the variables that may be modified:
//   ensures  va_state_eq(va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_ok(va_sM, va_update(dummy2, va_sM, va_update(dummy, va_sM, va_s0))))))
let makeFrame (env:env) (p:proc_decl) (s0:id) (sM:id):(exp * exp) =
  let specModsIo = List.collect (specModIo env true) p.pspecs in
  let frameArg (isRet:bool) e (x, t, storage, io, _) =
    match (isRet, storage, io) with
    | (true, XOperand, _) | (_, XOperand, (InOut | Out)) -> vaApp ("update_" + (vaOperandTyp t)) [evar x; evar sM; e]
    | _ -> e
    in
  let frameMod e (io, (x, _)) =
    match io with
    | (InOut | Out) ->
      (
        match Map.tryFind x env.ids with
        | Some (StateInfo (prefix, es, t)) -> vaApp ("update_" + prefix) (es @ [evar sM; e])
        | _ -> internalErr ("frameMod: could not find variable " + (err_id x))
      )
    | _ -> e
    in
  let e = evar s0 in
  let e = List.fold (frameArg true) e p.prets in
  let e = List.fold (frameArg false) e p.pargs in
  let e = List.fold frameMod e specModsIo in
  (e, vaApp "state_eq" [evar sM; e])

(* Build function for code for procedure Q
function method{:opaque} va_code_Q(iii:int, dummy:va_operand, dummy2:va_operand):va_code
{
  va_Block(...)
}
*)
let build_code (loc:loc) (env:env) (benv:build_env) (stmts:stmt list):(loc * decl) list =
  let p = benv.proc in
  if p.pghost = Ghost then [] else
  let fParams = make_fun_params p.prets p.pargs in
  let attrs = List.filter filter_fun_attr p.pattrs in
  let f =
    {
      fname = benv.code_name "";
      fghost = NotGhost;
      ftargs = [];
      fargs = fParams;
      fret_name = None;
      fret = tCode;
      fspecs = [];
      fbody =
        if benv.is_instruction then Some (attrs_get_exp (Id "instruction") p.pattrs)
        else Some (build_code_block env benv stmts);
      fattrs =
        if benv.is_quick then
          [(Id "opaque_to_smt", []); (Id "public_decl", []); (Id "qattr", [])] @ attrs @ attr_no_verify "admit" benv.proc.pattrs
        else
          [(Id "opaque", [])] @ attrs @ attr_no_verify "admit" p.pattrs;
    }
    in
  List.map (fun f -> (loc, DFun f)) (List.rev (f::!(benv.quick_code_funs)))

let build_lemma (env:env) (benv:build_env) (b1:id) (stmts:stmt list) (bstmts:stmt list):decls =
  // generate va_lemma_Q
  let p = benv.proc in
  let loc = benv.loc in
  let codeName = benv.code_name "" in
  let fArgs = (List.collect fArg p.prets) @ (List.collect fArg p.pargs) in

  (* Generate lemma prologue and boilerplate requires/ensures
      requires va_require(va_b0, va_code_Q(iii, va_op(dummy), va_op(dummy2)), va_s0, va_sN)
      ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
    ...
    reveal_va_code_Q();
    var va_old_s:va_state := va_s0;
    ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
    va_sM := va_ltmp1;
    va_bM := va_ltmp2;
    var va_b1:va_codes := va_get_block(va_cM);
  *)
  let total = benv.is_terminating in
  let (b0, r0, s0, f0) = (Reserved "b0", Reserved "r0", Reserved "s0", Reserved "f0") in
  let (bM, sM, fM, cM) = (Reserved "bM", Reserved "sM", Reserved "fM", Reserved "cM") in
  let sN = Reserved "sN" in
  let argB = (b0, (if total then tCode else tCodes), XPhysical, In, []) in
  let argS = (s0, tState, XPhysical, In, []) in
  let argF = (f0, tFuel, XPhysical, In, []) in
  let retB = (bM, tCodes, XPhysical, In, []) in
  let retS = (sM, tState, XPhysical, In, []) in
  let retF = (fM, tFuel, XPhysical, In, []) in
  let argR = (sN, tState, XPhysical, In, []) in
  let prets = make_proc_params true p.prets p.pargs in
  let pargs = make_proc_params false p.prets p.pargs in
  let pargs =
    match p.pghost with
    | Ghost -> pargs
    | NotGhost -> (if total then [argS] else [argS; argR]) @ pargs
    in
  let xReq = "require" + total_suffix total in
  let xEns = "ensure" + total_suffix total in
  let req = require (vaApp xReq ([evar b0; eapply codeName fArgs; evar s0] @ listIfNot total [evar sN])) in // va_require(va_b0, va_code_Q(iii, va_op(dummy), va_op(dummy2)), va_s0, va_sN)
  let ens = ensure (vaApp xEns (if total then [evar b0; evar s0; evar sM; evar fM] else [evar b0; evar bM; evar s0; evar sM; evar sN])) in // va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  let lCM  = (cM, Some (Some tCode, NotGhost)) in
  let sBlock = lemma_block total (sM, None) lCM (bM, None) (f0, None) (evar b0) (evar s0) (evar sN) in // ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  let eReveal = if !precise_opaque then eapply codeName fArgs else evar codeName in
  let sReveal = SAssign ([], eop (Uop UReveal) [eReveal]) in // reveal_va_code_Q();
  let sOldS = SVar (Reserved "old_s", Some tState, Immutable, XPhysical, [], Some (evar s0)) in
  let eb1 = vaApp "get_block" [evar (if total then b0 else cM)] in
  let sb1 = SVar (b1, Some tCodes, Immutable, XPhysical, [], Some eb1) in // var va_b1:va_codes := va_get_block(va_cM);

  let reqIsExps =
    (List.collect (reqIsArg s0 true) p.prets) @
    (List.collect (reqIsArg s0 false) p.pargs)
    in
  let reqsIs = List.map (fun e -> (loc, require e)) reqIsExps in

  let specModsIo = List.collect (specModIo env true) p.pspecs in
  let (eFrameExp, eFrame) = benv.frame_exp sM in

  (* Generate lemma for procedure p:
    lemma va_lemma_p(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
      returns (va_bM:va_codes, va_sM:va_state)
      requires va_require(va_b0, va_code_p(), va_s0, va_sN)
      ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
      requires ...
      ensures  ...
    {
      reveal_va_code_p();
      var va_old_s:va_state := va_s0;
      va_sM, (var va_cM:va_code), va_bM := va_lemma_block(va_b0, va_s0, va_sN);
      var va_b1:va_codes := va_get_block(va_cM);
      // this = va_s0
      ...
      va_sM := va_lemma_empty(va_s99, va_sM);
    }
  *)
  let pargs = match p.pghost with Ghost -> pargs | NotGhost -> argB::pargs in
  let prets =
    match p.pghost with
    | Ghost -> prets
    | NotGhost -> (if total then [retS; retF] else [retB; retS]) @ prets
    in
  let reqs = if benv.is_framed then reqsIs else [] in
  let ensFrame = if benv.is_framed then [(loc, ensure eFrame)] else [] in
  let (pspecs, pmods) = List.unzip (List.map (build_lemma_spec env s0 (evar sM)) p.pspecs) in
  let sStmts =
    if benv.is_instruction then
      // Body of instruction lemma
      let dummy = Reserved "dummy" in
      let sState = SAssign ([(sM, None); (fM, None)], vaApp "eval_ins" [evar b0; evar s0]) in
      let senv = { env = env; benv = benv; b1 = dummy; bM = dummy; code = evar dummy; s0 = sM; f0 = dummy; sM = sM; fM = dummy; sN = dummy; loc = loc;} in
      let ss = build_lemma_ghost_stmts senv stmts in
      [sReveal; sOldS] @ sBlock @ listIf total [sState] @ ss
    else if benv.is_quick then
      let range = evar (Id "range1") in
      let msg = EString ("***** MODIFIES CLAUSE NOT MET AT " + string_of_loc loc + " *****") in
      let eFrameX = vaApp "state_match" [evar sM; eFrameExp] in
      let eFrameL = eapply (Id "label") [range; msg; eFrameX] in
      let (_, enssL) = collect_specs true (List.concat pspecs) in
      let enssL = enssL @ (if !quick_mods then [] else [eFrameL]) in
      Emit_common_quick_code.build_proc_body env loc p (eapply codeName fArgs) (and_of_list enssL)
    else if benv.is_operand then
      err "operand procedures must be declared extern"
    else
      // Body of ordinary lemma
      let ss = stmts_refined bstmts in
      match p.pghost with
      | Ghost -> ss
      | NotGhost -> [sReveal; sOldS] @ sBlock @ [sb1] @ ss
    in
  let (req1, ens1) = match p.pghost with Ghost -> ([], []) | NotGhost -> ([(loc, req)], [(loc, ens)]) in
  let pLemmaSpecs = req1 @ reqs @ ens1 @ List.concat pspecs @ ensFrame in
  let exportSpecsDecls =
    let isExportSpecs = attrs_get_bool (Id "exportSpecs") false p.pattrs in
    if not isExportSpecs then [] else
    let fArg (x, t, _, _, _) = (x, Some t) in
    let reqArgs = List.map fArg pargs in
    let ensArgs = List.map fArg (pargs @ prets) in
    let spec (isReq:bool) (_, (s:spec)):exp list =
      match s with
      | Requires (_, e) when isReq -> [e]
      | Ensures (_, e) when not isReq -> [e]
      | _ -> []
      in
    let xReq = Reserved ("req_" + (string_of_id p.pname)) in
    let xEns = Reserved ("ens_" + (string_of_id p.pname)) in
    let eReqs = List.collect (spec true) pLemmaSpecs in
    let eEnss = List.collect (spec false) pLemmaSpecs in
    let eReqApp = eapply xReq (List.map (fun (x, t) -> EVar(x, t)) reqArgs) in
    let eEnss = eReqApp::eEnss in
    let eReq = and_of_list eReqs in
    let eEns = and_of_list eEnss in
    let fReq =
      {
        fname = xReq;
        fghost = Ghost;
        ftargs = [];
        fargs = reqArgs;
        fret_name = None;
        fret = tProp;
        fspecs = [];
        fbody = Some eReq;
        fattrs = attr_public p.pattrs;
      }
      in
    let fEns =
      {
        fname = xEns;
        fghost = Ghost;
        ftargs = [];
        fargs = ensArgs;
        fret = tProp;
        fret_name = None;
        fspecs = [];
        fbody = Some eEns;
        fattrs = attr_public p.pattrs;
      }
      in
    [(loc, DFun fReq); (loc, DFun fEns)]
    in
  let pLemma =
    {
      pname = match p.pghost with Ghost -> p.pname | NotGhost -> Reserved ("lemma_" + (string_of_id p.pname)); // REVIEW: ghost procedure names
      pghost = Ghost;
      pinline = Outline;
      ptargs = p.ptargs;
      pargs = pargs;
      prets = prets;
      pspecs = pLemmaSpecs;
      pbody = Some (sStmts);
      pattrs = List.filter filter_proc_attr p.pattrs @ attr_no_verify "admit" p.pattrs;
    }
    in
  exportSpecsDecls @ [(loc, DProc pLemma)]

let build_proc (envBody:env) (env:env) (loc:loc) (p:proc_decl):decls =
  gen_lemma_sym_count := 0;
  let isInstruction = List_mem_assoc (Id "instruction") p.pattrs in
  let isOperand = List_mem_assoc (Id "operand") p.pattrs in
  let codeName prefix = Reserved ("code_" + prefix + (string_of_id p.pname)) in
  let isQuick = is_quick_body p.pattrs in
  let reqs =
    List.collect (fun (loc, s) ->
        match s with
        | Requires (_, e) -> [ELoc (loc, e)]
        | _ -> []
      ) p.pspecs in
  let enss =
    List.collect (fun (loc, s) ->
        match s with
        | Ensures (_, e) -> [ELoc (loc, e)]
        | _ -> []
      ) p.pspecs in
  let bodyDecls =
    match p.pbody with
    | None -> []
    | Some stmts ->
        let (s0, f0, sM, fM) = (Reserved "s0", Reserved "f0", Reserved "sM", Reserved "fM") in
        let i1 = string (gen_lemma_sym ()) in
        let b1 = Reserved ("b" + i1) in
        let fGhost s xss =
          match s with
          | SVar (x, _, _, XGhost, _, _) -> x::(List.concat xss)
          | _ -> List.concat xss
          in
        let (gen_quick_block, gen_quick_block_funs) = Emit_common_quick_code.make_gen_quick_block loc p in
        let benv =
          {
            proc = p;
            loc = loc;
            is_instruction = isInstruction;
            is_quick = isQuick;
            is_operand = isOperand;
            is_framed = attrs_get_bool (Id "frame") (p.pghost = NotGhost) p.pattrs;
            is_terminating = attrs_get_bool (Id "terminates") !fstar p.pattrs;
            code_name = codeName;
            frame_exp = makeFrame env p s0;
            gen_quick_block = gen_quick_block;
            gen_quick_block_funs = gen_quick_block_funs;
            quick_code_funs = ref [];
          }
          in
        let rstmts = stmts_refined stmts in
        let fCodes = build_code loc env benv rstmts in
        let dummy = Reserved "dummy" in
        let senv = { env = env; benv = benv; b1 = b1; bM = dummy; code = evar dummy; s0 = s0; f0 = fM; sM = sM; fM = fM; sN = dummy; loc = loc;} in
        let bstmts =
          match p.pghost with
          | Ghost -> build_lemma_ghost_stmts senv stmts
          | NotGhost -> build_lemma_stmts senv stmts
          in
        let pLemma = build_lemma env benv b1 rstmts bstmts in
        let quickDecls =
          if isQuick then
            Emit_common_quick_code.build_qcode envBody loc p stmts
          else []
        fCodes @ (if !no_lemmas then [] else quickDecls @ (gen_quick_block_funs ()) @ pLemma)
    in
  bodyDecls //@ blockLemmaDecls
