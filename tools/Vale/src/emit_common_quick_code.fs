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

let rec build_qcode_stmt (s:stmt):exp =
  let err () = internalErr "make_gen_quick_block" in
  match skip_loc_stmt s with
  | SAssign ([], e) ->
    (
      match skip_loc e with
      | EApply(Id x, es) ->
          let es = List.filter (fun e -> match e with EOp (Uop UGhostOnly, _) -> false | _ -> true) es in
          let es = List.map get_code_exp es in
          let es = List.map (map_exp stateToOp) es in
          let es = List.map exp_refined es in
          vaApp ("quick_" + x) es
      | _ -> err ()
    )
  | _ -> err ()
and build_qcode_stmts (ss:stmt list):exp =
  let empty = EApply (Id "QEmpty", []) in
  let cons el e = EApply (Id "QSeq", [e; el]) in
  List.fold cons empty (List.rev (List.map build_qcode_stmt ss))
and build_qcode_block (ss:stmt list):exp =
  EApply (Id "qblock", [build_qcode_stmts ss])

let make_gen_quick_block (loc:loc) (p:proc_decl):((env -> quick_info -> lhs list -> exp list -> stmt list -> stmt list) * (unit -> decls)) =
  let funs = ref ([]:decls) in
  let fArgs = (List.collect fArg p.prets) @ (List.collect fArg p.pargs) in
  let fParams = make_fun_params p.prets p.pargs in
  let gen_quick_block env info outs args ss =
    let id = Reserved ("qcode_" + info.qsym + "_" + (string_of_id p.pname)) in
    let cid = Reserved ("code_" + info.qsym + "_" + (string_of_id p.pname)) in
    let tArgs = List.map (fun (x, _) -> TName x) fParams in
    let tCodeApp = TApp (TName cid, tArgs) in
//    let fBody = build_qcode_block ss in
    let fBody = build_qcode_stmts ss in
    let fCode =
      {
        fname = id;
        fghost = Ghost;
        fargs = fParams;
//        fret = TApp (TName (Reserved "quickCode"), [TName (Id "unit"); tCodeApp]);
        fret = TApp (TName (Id "quickCodes"), [TName (Id "unit"); tCodeApp]);
        fbody = Some fBody;
        fattrs = [(Id "opaque_to_smt", [])];
      }
      in
    let dFun = DFun fCode in
    funs := (loc, dFun)::!funs;
    (*
      let (va_s2, va_fc2, ()) = wp_run_code_norm (va_code_1_Incr3 ()) (va_quick_1_Incr3 ()) va_s0
        (fun (s0:state) (sN:state) -> va_update_reg Rax sN (va_update_flags sN s0))
        (fun (sN:state) (sN':state) -> va_get_reg Rax sN == va_get_reg Rax sN' /\ va_get_flags sN == va_get_flags sN')
    *)
    let eCode = EApply (cid, fArgs) in
    let eQCode = EApply (id, fArgs) in
    let s0 = Reserved "s0" in
    let sM = Reserved "sM" in
    let sN = Reserved "sN" in
    let eqMod x =
      let getM = stateGet {env with state = EVar sM} x in
      let getN = stateGet {env with state = EVar sN} x in
      EOp (Bop BEq, [getM; getN])
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
    let sLemma = SAssign (outs, EApply (Id "wp_run_norm", eCode::eQCode::args @ [fUpdate; fEq])) in
    [sLemma]
    in
  let gen_quick_block_funs () = List.rev !funs in
  (gen_quick_block, gen_quick_block_funs)

let build_qcode (env:env) (loc:loc) (p:proc_decl) (ss:stmt list):decls =
  (*
  [@"opaque_to_smt"]
  let va_qcode_Add3 () : quickCode unit (va_code_Add3 ()) = qblock (
    QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    QSeq (va_quick_Add64 (OReg Rax) (OConst 1)) (
    QEmpty ()
    )))
  )
  *)
  let fParams = [] in
  let cid = Reserved ("code_" + (string_of_id p.pname)) in
  let tArgs = List.map (fun (x, _) -> TName x) fParams in
  let tCodeApp = TApp (TName cid, tArgs) in
  let tRetQuick = TApp (TName (Id "quickCode"), [TName (Id "unit"); tCodeApp]) in
  let eQuick = build_qcode_block ss in
  let fCodes =
    {
      fname = Reserved ("qcode_" + (string_of_id p.pname));
      fghost = NotGhost;
      fargs = fParams;
      fret = tRetQuick;
      fbody = Some eQuick;
      fattrs = [(Id "opaque_to_smt", [])];
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
  let letGs = EBind (BindLet, [EVar g], gAssigns, [], ens) in
  let funCont = EBind (Lambda, [], [(s0, None); (sM, None); (g, None)], [], letGs) in
  let eWpSound = EApply (wpSound_X, [code; EApply (qCodes_X, args); EVar s0; funCont]) in
  let sWpSound = SAssign ([(sM, None); (fM, None); (g, None)], eWpSound) in
  let gAssigns = List.map (fun (x, _) -> (x, None)) ghostRets in
  let sAssignGs =
    match ghostRets with
    | [] -> []
    | _ -> [SAssign (gAssigns, EVar g)]
    in
  [sWpSound] @ sAssignGs
