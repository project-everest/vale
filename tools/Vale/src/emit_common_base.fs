module Emit_common_base

open Ast
open Ast_util
open Parse
open Parse_util
open Transform
open Microsoft.FSharp.Math
open System.Numerics

let reprint_file = ref (None:string option);
let reprint_verbatims = ref true;
let reprint_ghost_decls = ref true;
let reprint_specs = ref true;
let reprint_ghost_stmts = ref true;
let reprint_loop_invs = ref true;
let reprint_blank_lines = ref true;
let concise_lemmas = ref true;
let precise_opaque = ref false;
let fstar = ref false;
let reprint_decls_rev = ref ([]:decls)

type print_state =
  {
    print_out:System.IO.TextWriter;
    print_interface:print_state option;
    cur_loc:loc ref;
    cur_indent:string ref;
  }
  member this.PrintUnbrokenLine (s:string) =
    let {loc_file = f; loc_line = i} = !this.cur_loc in (this.cur_loc := {loc_file = f; loc_line = i + 1; loc_col = 1; loc_pos = 0});
    this.print_out.WriteLine (!this.cur_indent + s);
  member this.PrintLine (s:string) = this.PrintBreakLine true s
  member this.PrintBreakLine (isFirst:bool) (s:string) =
    let breakCol = 100 in
    let s = s.TrimEnd() in
    let (sBreak1, sBreak2Opt) =
      if (!this.cur_indent + s).Length > breakCol && s.Contains(" ") && not (s.Contains("\"")) then
        // try to find last space in s[0 .. breakCol-indentsize]
        // if that fails, find first space in s
        let s1 = s.Substring(0, breakCol - (!this.cur_indent).Length) in
        let breakAt = if s1.Contains(" ") then s1.LastIndexOf(" ") else s.IndexOf(" ") in
        let sBreak1 = s.Substring(0, breakAt) in
        let sBreak2 = s.Substring(breakAt).Trim() in
        if sBreak1.Contains("//") then (s, None) else // don't break up a "//" comment
        (sBreak1, Some sBreak2)
      else (s, None)
      in
    this.PrintUnbrokenLine sBreak1;
    match (sBreak2Opt, isFirst) with
    | (None, _) -> ()
    | (Some s, false) -> this.PrintBreakLine false s
    | (Some s, true) -> this.Indent (); this.PrintBreakLine false s; this.Unindent ()
  member this.Indent () = this.cur_indent := "  " + !this.cur_indent
  member this.Unindent () = this.cur_indent := (!this.cur_indent).Substring(2)
  member this.SetLoc (({loc_file = f; loc_line = i} as l):loc) =
    let {loc_file = cf; loc_line = ci} as cl = !this.cur_loc in
    if l = cl then ()
    else if f <> cf || i < ci || i > ci + 8 then this.cur_loc := l; this.print_out.WriteLine ("#line " + (string i) + " " + f)
    else this.PrintLine ""; this.SetLoc l

let require e = Requires (Refined, e)
let ensure e = Ensures (Refined, e)

let gen_lemma_sym_count = ref 0
let gen_lemma_sym ():int = incr gen_lemma_sym_count; !gen_lemma_sym_count

let get_code_exp (e:exp):exp = map_exp (fun e -> match e with EOp (CodeLemmaOp, [ec; el]) -> Replace ec | _ -> Unchanged) e
let get_lemma_exp (e:exp):exp = map_exp (fun e -> match e with EOp (CodeLemmaOp, [ec; el]) -> Replace el | _ -> Unchanged) e

let stateToOp (e:exp):exp map_modify =
  match e with
  | EOp (OperandArg _, [e]) -> Replace e
  | EOp (StateOp (x, prefix, t), es) -> Replace (vaApp ("op_" + prefix) es)
  | _ -> Unchanged

// Turn multiple assignments into series of individual assignments
// Example: x, (ghost var y), z := e;
//  becomes (ghost var tx), (ghost var y), (ghost var tz) := e; x := tx; z := tz;
let eliminate_assign_lhss (s:stmt):stmt list =
  match s with
  | SAssign (lhss, e) ->
      let f (x, dOpt) =
        match dOpt with
        | None ->
            let itmp = string (gen_lemma_sym ()) in
            let xtmp = Reserved ("ltmp" + itmp) in
            let stmp = SAssign ([(x, None)], EVar xtmp) in
            ((xtmp, Some (None, Ghost)), [stmp])
        | Some _ -> ((x, dOpt), [])
      let (lhss, ss) = List.unzip (List.map f lhss) in
      (SAssign (lhss, e))::(List.concat ss)
  | _ -> [s]

let varLhsOfId (x:id):lhs = (x, Some (None, NotGhost))

let filter_proc_attr (x, es) =
  match x with
  | Id ("timeLimit" | "timeLimitMultiplier" | "tactic" | "fast_state") -> true
  | _ -> false
  in

// convert imperative updates to functional let assignments
let rec let_updates_stmts (scope:Map<id, typ option>) (ss:stmt list):(Set<id> * stmt list)=
  let (_, updates, ss_rev) = List.fold let_update_stmt_rev (scope, Set.empty, []) ss in
  let updates = Set.filter (fun x -> Map.containsKey x scope) updates in
  (updates, List.rev ss_rev)
and let_update_stmt_rev (scope:Map<id, typ option>, updates:Set<id>, ss_rev:stmt list) (s:stmt):(Map<id, typ option> * Set<id> * stmt list) =
  let (scope, updates, s) = let_update_stmt scope updates s in
  (scope, updates, s::ss_rev)
and let_update_stmt (scope:Map<id, typ option>) (updates:Set<id>) (s:stmt):(Map<id, typ option> * Set<id> * stmt) =
  let add_unique x t m =
    if Map.containsKey x m then err ("variable '" + (err_id x) + "' already in scope") else
    Map.add x t m
    in
  let find_scope x =
    if Map.containsKey x scope then (x, Map.find x scope)
    else err ("mutable variable '" + (err_id x) + "' not found")
    in
  let make_let updates s =
    let updates = List.map find_scope (Set.toList updates) in
    SLetUpdates (updates, s)
    in
  match s with
  | SLoc (loc, s) ->
      try
        let (scope, updates, s) = let_update_stmt scope updates s in
        (scope, updates, SLoc (loc, s))
      with err -> raise (LocErr (loc, err))
  | SLabel x -> notImplemented "labels"
  | SGoto x -> notImplemented "goto"
  | SReturn -> notImplemented "return"
  | SAssume _ | SAssert _ | SAlias _ | SCalc _ | SForall _ -> (scope, updates, s)
  | SVar (x, t, _, _, _, _) -> (add_unique x t scope, updates, s)
  | SAssign (lhss, e) ->
      let xs_update = List.collect (fun lhs -> match lhs with (x, None) -> [x] | _ -> []) lhss in
      let xs_decls = List.collect (fun lhs -> match lhs with (x, Some (t, _)) -> [(x, t)] | _ -> []) lhss in
      let scope = List.fold (fun scope (x, t) -> add_unique x t scope) scope xs_decls in
      let updates = Set.union (Set.ofList xs_update) updates in
      (scope, updates, s)
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SBlock b ->
      let (u, b) = let_updates_stmts scope b in
      (scope, Set.union updates u, make_let u (SBlock b))
  | SFastBlock b ->
      let (u, b) = let_updates_stmts scope b in
      (scope, Set.union updates u, make_let u (SFastBlock b))
  | SIfElse (g, e, b1, b2) ->
      let (u1, b1) = let_updates_stmts scope b1 in
      let (u2, b2) = let_updates_stmts scope b2 in
      (scope, Set.unionMany [updates; u1; u2], make_let (Set.union u1 u2) (SIfElse (g, e, b1, b2)))
  | SWhile (e, invs, ed, b) ->
      let (u, b) = let_updates_stmts scope b in
      (scope, Set.union updates u, make_let u (SWhile (e, invs, ed, b)))
  | SExists (xs, ts, e) ->
      let scope = List.fold (fun scope (x, t) -> add_unique x t scope) scope xs in
      (scope, updates, s)

