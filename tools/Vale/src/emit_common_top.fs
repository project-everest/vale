// Turn high-level AST into low-level lemmas:
//   - call transform.fs
//   - then generate lemmas

module Emit_common_top

open Ast
open Ast_util
open Parse
open Parse_util
open Transform
open Emit_common_base
open Microsoft.FSharp.Math
open System.Numerics

let add_reprint_decl (env:env) (loc:loc) (d:decl):unit =
  let new_decls =
    match d with
    | DVar _ | DFun _ -> if !reprint_ghost_decls then [d] else []
    | DVerbatim _ -> if !reprint_verbatims then [d] else []
    | DProc p ->
        let p = if !reprint_specs then p else {p with pspecs = []} in
        let fs (s:stmt):stmt list map_modify =
          let modGhost = if !reprint_ghost_stmts then Unchanged else Replace [] in
          match s with
          | SLoc _ | SLabel _ | SGoto _ | SReturn | SAlias _ | SLetUpdates _ | SBlock _ | SFastBlock _ -> Unchanged
          | SIfElse ((SmInline | SmPlain), _, _, _) -> Unchanged
          | SWhile _ when !reprint_loop_invs -> Unchanged
          | SWhile (e, _, (l, _), s) -> Replace [SWhile (e, [], (l, []), s)]
          | SAssign (_, e) ->
            (
              match skip_loc e with
              | EApply(x, _) when Map.containsKey x env.procs -> Unchanged
              | EOp (Uop (UCustomAssign s), [e]) -> Unchanged
              | _ -> modGhost
            )
          | SAssume _ | SAssert _ | SCalc _ | SVar _ -> modGhost
          | SIfElse (SmGhost, _, _, _) -> modGhost
          | SForall _ | SExists _ -> modGhost
          in
        let bodyOpt =
          match p.pbody with
          | None -> None
          | Some ss -> Some (List.collect (map_stmt (fun e -> e) fs) ss) in
        let p = {p with pbody = bodyOpt} in
        [DProc p]
    in
  reprint_decls_rev := (List.map (fun d -> (loc, d)) new_decls) @ (!reprint_decls_rev)

let build_decl (env:env) ((loc:loc, d1:decl), verify:bool):env * decls =
  try
    let (env, dReprint, d2) = transform_decl env loc d1 in
    let add_fun env f = {env with funs = Map.add f.fname f env.funs}
    let add_proc env p = {env with procs = Map.add p.pname p env.procs}
    let (env, decl) =
      match d2 with
      | DFun ({fbody = None} as f) -> (add_fun env f, [])
      | DProc ({pattrs = [(Reserved "alias", _)]} as p) -> (add_proc env p, [])
      | DProc p ->
          let isRecursive = attrs_get_bool (Id "recursive") false p.pattrs in
          let isQuick = List_mem_assoc (Id "quick") p.pattrs in
          let envp = add_proc env p in
          if verify then
            let build_proc = if !fstar then Emit_common_lemmas.build_proc else Emit_common_refine.build_proc in
            let envr = if isRecursive then envp else env in
            let ds_p = build_proc envr loc p in
            let ds_q = if isQuick then Emit_common_quick_export.build_proc envr loc p else [] in
            (envp, ds_p @ ds_q)
          else
            (envp, [])
      | _ -> (env, if verify then [(loc, d2)] else [])
      in
    (match (verify, !reprint_file) with (true, Some _) -> add_reprint_decl env loc dReprint | _ -> ());
    (env, decl)
  with err -> raise (LocErr (loc, err))

let build_decls (env:env) (ds:((loc * decl) * bool) list):decls =
  let (env, dss) = List_mapFoldFlip build_decl env ds in
  List.concat dss

