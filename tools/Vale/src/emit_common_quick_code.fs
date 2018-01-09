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

let build_qcode (env:env) (loc:loc) (p:proc_decl):decls =
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
  let tRetQuick = TApp (TName (Id "quickCode"), []) in
  let eQuick = EApply (Id "QEmpty", []) in
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
  let wpSound_X = Reserved ("wpSound_" + (string_of_id p.pname)) in
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
