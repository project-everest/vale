module Ast_util

open Ast
open Microsoft.FSharp.Math

let List_mapFold (f:'s -> 't -> 'r * 's) (s:'s) (ts:'t list):('r list * 's) =
  let (rs_rev, s) = List.fold (fun (rs_rev, s) t -> let (r, s) = f s t in (r::rs_rev, s)) ([], s) ts in
  (List.rev rs_rev, s)

let List_mapFoldFlip (f:'s -> 't -> 's * 'r) (s:'s) (ts:'t list):('s * 'r list) =
  let (s, rs_rev) = List.fold (fun (s, rs_rev) t -> let (s, r) = f s t in (s, r::rs_rev)) (s, []) ts in
  (s, List.rev rs_rev)

let List_mapFoldFlip2 (f:'s -> 't -> 's * 'r0 * 'r1) (s:'s) (ts:'t list):('s * 'r0 list * 'r1 list) =
  let (s, rs0_rev, rs1_rev) = List.fold (fun (s, rs0_rev, rs1_rev) t -> let (s, r0, r1) = f s t in (s, r0::rs0_rev, r1::rs1_rev)) (s, [], []) ts in
  (s, List.rev rs0_rev, List.rev rs1_rev)

let mapOpt (f:'a -> 'a) (o:'a option) =
  match o with None -> None | Some a -> Some (f a)

let mapFst (f:'a -> 'c) (a:'a, b:'b):('c * 'b) = (f a, b)
let mapSnd (f:'b -> 'c) (a:'a, b:'b):('a * 'c) = (a, f b)

let List_mapFst (f:'a -> 'c) (l:('a * 'b) list):('c * 'b) list = List.map (mapFst f) l
let List_mapSnd (f:'b -> 'c) (l:('a * 'b) list):('a * 'c) list = List.map (mapSnd f) l

let list_of_opt (opt:'a option):'a list = match opt with None -> [] | Some a -> [a]

exception Err of string
exception InternalErr of string
exception LocErr of loc * exn
let err (s:string):'a = raise (Err s)
let internalErr (s:string):'a = raise (InternalErr s)
let notImplemented (s:string):'a = raise (InternalErr ("not implemented: " + s))

let string_of_loc (loc:loc):string =
  "line " + (string loc.loc_line) + " column " + (string loc.loc_col) + " of file " + loc.loc_file

let rec List_mem_assoc (a:'a) (l:('a * 'b) list):bool =
  match l with [] -> false | (h, _)::t -> h = a || List_mem_assoc a t

let rec List_assoc (a:'a) (l:('a * 'b) list):'b =
  match l with [] -> internalErr "List_assoc" | (ha, hb)::t -> if ha = a then hb else List_assoc a t

let string_of_id (x:id):string = match x with Id s -> s | _ -> internalErr (Printf.sprintf "string_of_id: %A" x)
let reserved_id (x:id):string = match x with Reserved s -> s | _ -> internalErr (Printf.sprintf "reserved_id: %A" x)
let err_id (x:id):string = match x with Id s -> s | Reserved s -> s | Operator s -> "operator(" + s + ")"

let binary_op_of_list (b:bop) (empty:exp) (es:exp list) =
  match es with
  | [] -> empty
  | h::t -> List.fold (fun accum e -> EOp (Bop b, [accum; e])) h t
let and_of_list = binary_op_of_list BLand (EBool true)
let or_of_list = binary_op_of_list BLor (EBool false)

let assert_attrs_default =
  {
    is_inv = false;
    is_split = false;
    is_refined = false;
    is_quickstart = false;
    is_quickend = false;
    is_quicktype = false;
  }

let rec exps_of_spec_exps (es:(loc * spec_exp) list):(loc * exp) list =
  match es with
  | [] -> []
  | (loc, SpecExp e)::es -> (loc, e)::(exps_of_spec_exps es)
  | (loc, SpecLet (x, t, e))::es ->
      let es = List.map snd (exps_of_spec_exps es) in
      [(loc, EBind (BindLet, [e], [(x, t)], [], and_of_list es))]

type 'a map_modify = Unchanged | Replace of 'a | PostProcess of ('a -> 'a)

let map_apply_modify (m:'a map_modify) (g:unit -> 'a):'a =
  match m with
  | Unchanged -> g ()
  | Replace e -> e
  | PostProcess p -> p (g ())

let map_apply_compose (f1:'a -> 'b map_modify) (f2:'a -> 'b map_modify) (x:'a):'b map_modify =
  match f1 x with
  | Unchanged -> f2 x
  | Replace y -> Replace y
  | PostProcess p1 ->
    (
      match f2 x with
      | Unchanged -> PostProcess p1
      | Replace y -> Replace (p1 y)
      | PostProcess p2 -> PostProcess (fun y -> p1 (p2 y))
    )

let map_apply_compose2 (f1:'a -> 'b -> 'c map_modify) (f2:'a -> 'b -> 'c map_modify) (x1:'a) (x2:'b):'c map_modify =
  match f1 x1 x2 with
  | Unchanged -> f2 x1 x2
  | Replace y -> Replace y
  | PostProcess p1 ->
    (
      match f2 x1 x2 with
      | Unchanged -> PostProcess p1
      | Replace y -> Replace (p1 y)
      | PostProcess p2 -> PostProcess (fun y -> p1 (p2 y))
    )

let rec map_exp (f:exp -> exp map_modify) (e:exp):exp =
  map_apply_modify (f e) (fun () ->
    let r = map_exp f in
    match e with
    | ELoc (loc, e) -> try ELoc (loc, r e) with err -> raise (LocErr (loc, err))
    | EVar _ | EInt _ | EReal _ | EBitVector _ | EBool _ | EString _ -> e
    | EBind (b, es, fs, ts, e) -> EBind (b, List.map r es, fs, List.map (List.map r) ts, r e)
    | EOp (op, es) -> EOp (op, List.map r es)
    | EApply (x, es) -> EApply (x, List.map r es)
  )

let rec gather_exp (f:exp -> 'a list -> 'a) (e:exp):'a =
  let r = gather_exp f in
  let children:'a list =
    match e with
    | ELoc (loc, e) -> try [r e] with err -> raise (LocErr (loc, err))
    | EVar _ | EInt _ | EReal _ | EBitVector _ | EBool _ | EString _ -> []
    | EBind (b, es, fs, ts, e) -> (List.map r es) @ (List.collect (List.map r) ts) @ [r e]
    | EOp (op, es) -> List.map r es
    | EApply (x, es) -> List.map r es
  in f e children

let gather_attrs (f:exp -> 'a list -> 'a) (attrs:attrs):'a list =
  List.collect (fun (x, es) -> List.map (gather_exp f) es) attrs

let map_attrs (fe:exp -> exp) (attrs:attrs):attrs =
  List.map (fun (x, es) -> (x, List.map fe es)) attrs

let gather_spec (f:exp -> 'a list -> 'a) (s:spec):'a list =
  match s with
  | Requires (_, e) -> [gather_exp f e]
  | Ensures (_, e) -> [gather_exp f e]
  | Modifies (_, e) -> [gather_exp f e]
  | SpecRaw _ -> internalErr "SpecRaw"

let gather_specs (f:exp -> 'a list -> 'a) (ss:spec list):'a list =
  List.collect (gather_spec f) ss

let rec skip_loc (e:exp):exp =
  match e with
  | ELoc (_, e) -> skip_loc e
  | _ -> e

let skip_loc_opt (e:exp option):exp option =
  match e with
  | None -> None
  | Some e -> Some (skip_loc e)

let rec skip_locs (e:exp):exp = map_exp (fun e -> match e with ELoc (_, e) -> Replace (skip_locs e) | _ -> Unchanged) e

let rec skip_loc_apply (e:exp) (f:exp->'a):'a =
  match e with
  | ELoc (loc, e) -> try skip_loc_apply e f with err -> raise (LocErr (loc, err))
  | _ -> f e

let rec loc_apply (loc:loc) (e:exp) (f:exp -> 'a):'a =
  try
    match e with
    | ELoc (loc, e) -> loc_apply loc e f
    | _ -> f e
  with err -> raise (LocErr (loc, err))

let locs_of_exp (e:exp):loc list =
  let f e locs =
    match e with
    | ELoc (l, e) -> [l]
    | _ -> List.concat locs
  in gather_exp f e

let one_loc_of_exp (defaultLoc:loc) (e:exp):loc =
  match locs_of_exp e with [] -> defaultLoc | h::t -> h

let skip_locs_attrs (a:attrs):attrs = List.map (fun (x, es) -> (x, List.map skip_locs es)) a

let rec map_stmt (fe:exp -> exp) (fs:stmt -> stmt list map_modify) (s:stmt):stmt list =
  map_apply_modify (fs s) (fun () ->
    match s with
    | SLoc (loc, s) -> try List.map (fun s -> SLoc (loc, s)) (map_stmt fe fs s) with err -> raise (LocErr (loc, err))
    | SLabel x -> [s]
    | SGoto x -> [s]
    | SReturn -> [s]
    | SAssume e -> [SAssume (fe e)]
    | SAssert (attrs, e) -> [SAssert (attrs, fe e)]
    | SCalc (oop, contents) -> [SCalc (oop, List.map (map_calc_contents fe fs) contents)]
    | SVar (x, t, m, g, a, eOpt) -> [SVar (x, t, m, g, map_attrs fe a, mapOpt fe eOpt)]
    | SAlias (x, y) -> [SAlias (x, y)]
    | SAssign (xs, e) -> [SAssign (xs, fe e)]
    | SLetUpdates _ -> internalErr "SLetUpdates"
    | SBlock b -> [SBlock (map_stmts fe fs b)]
    | SQuickBlock (x, b) -> [SQuickBlock (x, map_stmts fe fs b)]
    | SIfElse (g, e, b1, b2) -> [SIfElse (g, fe e, map_stmts fe fs b1, map_stmts fe fs b2)]
    | SWhile (e, invs, ed, b) ->
        [SWhile (
          fe e,
          List_mapSnd fe invs,
          mapSnd (List.map fe) ed,
          map_stmts fe fs b)]
    | SForall (xs, ts, ex, e, b) ->
        [SForall (xs, List.map (List.map fe) ts, fe ex, fe e, map_stmts fe fs b)]
    | SExists (xs, ts, e) ->
        [SExists (xs, List.map (List.map fe) ts, fe e)]
  )
and map_stmts (fe:exp -> exp) (fs:stmt -> stmt list map_modify) (ss:stmt list):stmt list = List.collect (map_stmt fe fs) ss
and map_calc_contents (fe:exp -> exp) (fs:stmt -> stmt list map_modify) (cc:calcContents): calcContents =
  let {calc_exp = e; calc_op = oop; calc_hints = hints} = cc in
  {calc_exp = fe e; calc_op = oop; calc_hints = List.map (map_stmts fe fs) hints}

let rec gather_stmt (fs:stmt -> 'a list -> 'a) (fe:exp -> 'a list -> 'a) (s:stmt):'a =
  let re = gather_exp fe in
  let r = gather_stmt fs fe in
  let rs = gather_stmts fs fe in
  let children:'a list =
    match s with
    | SLoc (loc, s) -> try [r s] with err -> raise (LocErr (loc, err))
    | SLabel _ | SGoto _ | SReturn -> []
    | SAssume e | SAssert (_, e) | SAssign (_, e) -> [re e]
    | SCalc (oop, contents) -> List.collect (gather_calc_contents fs fe) contents
    | SVar (x, t, m, g, a, eOpt) -> (gather_attrs fe a) @ (List.map re (list_of_opt eOpt))
    | SAlias (x, y) -> []
    | SLetUpdates _ -> internalErr "SLetUpdates"
    | SBlock b -> rs b
    | SQuickBlock (x, b) -> rs b
    | SIfElse (g, e, b1, b2) -> [re e] @ (rs b1) @ (rs b2)
    | SWhile (e, invs, ed, b) -> [re e] @ (List.map re (List.map snd invs)) @ (List.map re (snd ed)) @ (rs b)
    | SForall (xs, ts, ex, e, b) -> (List.collect (List.map re) ts) @ [re e] @ (rs b)
    | SExists (xs, ts, e) -> (List.collect (List.map re) ts) @ [re e]
  in fs s children
and gather_stmts (fs:stmt -> 'a list -> 'a) (fe:exp -> 'a list -> 'a) (ss:stmt list):'a list =
  List.map (gather_stmt fs fe) ss
and gather_calc_contents (fs:stmt -> 'a list -> 'a) (fe:exp -> 'a list -> 'a) (cc:calcContents):'a list =
  let {calc_exp = e; calc_op = oop; calc_hints = hints} = cc in
  [gather_exp fe e] @ (List.collect (gather_stmts fs fe) hints)

let rec skip_loc_stmt (s:stmt):stmt =
  match s with
  | SLoc (_, s) -> skip_loc_stmt s
  | _ -> s

let rec skip_locs_stmt (s:stmt):stmt list = map_stmt skip_locs (fun s -> match s with SLoc (_, s) -> Replace (skip_locs_stmt s) | _ -> Unchanged) s

let locs_of_stmt (s:stmt):loc list =
  let fs s locs =
    match s with
    | SLoc (l, _) -> [l]
    | _ -> List.concat locs
  let fe e locs =
    match e with
    | ELoc (l, _) -> [l]
    | _ -> List.concat locs
  in gather_stmt fs fe s

let one_loc_of_stmt (defaultLoc:loc) (s:stmt):loc =
  match locs_of_stmt s with [] -> defaultLoc | h::t -> h

// Substitute an expression for a reserved variable.
// This does *not* rename bound variables to avoid variable capture.
// Therefore, the map m should only contain reserved identifiers
// that will never appear in EBind expressions.
let subst_reserved_exp (m:Map<id, exp>) (e:exp):exp =
  let f e =
    match e with
    | EVar x when Map.containsKey x m -> Replace (Map.find x m)
    | _ -> Unchanged
    in
  map_exp f e

let rec free_vars_exp (e:exp):Set<id> =
  let f (e:exp) (xss:Set<id> list):Set<id> =
    match e with
    | EVar x -> Set.singleton x
    | EBind (_, es, fs, ts, e) ->
        let r = free_vars_exp in
        let rs es = Set.unionMany (List.map r es) in
        let xs = Set.union (Set.unionMany (List.map rs ts)) (r e) in
        let ys = Set.ofList (List.map fst fs) in
        let xs = Set.difference xs ys in
        Set.union xs (rs es)
    | _ -> Set.unionMany xss
  in gather_exp f e

let free_vars_spec (s:spec):Set<id> =
  let fe e xss = free_vars_exp e in
  Set.unionMany (gather_spec fe s)

let free_vars_specs (ss:spec list):Set<id> = Set.unionMany (List.map free_vars_spec ss)

let free_vars_stmt (s:stmt):Set<id> =
  let fs s xss = Set.unionMany xss in
  let fe e xss = free_vars_exp e in
  gather_stmt fs fe s

let free_vars_stmts (ss:stmt list):Set<id> = Set.unionMany (List.map free_vars_stmt ss)

let attrs_get_bool (x:id) (defaultVal:bool) (a:attrs):bool =
  let fErr () = err ("expected boolean value in attribute " + (err_id x)) in
  if List_mem_assoc x a then
    match List_assoc x a with
    | [] -> true
    | [e] -> (match skip_loc e with EBool b -> b | _ -> fErr ())
    | _ -> fErr ()
  else defaultVal

let attrs_get_exps_opt (x:id) (a:attrs):exp list option =
  if List_mem_assoc x a then Some (List_assoc x a) else None

let attrs_get_exp_opt (x:id) (a:attrs):exp option =
  if List_mem_assoc x a then
    match List_assoc x a with
    | [e] -> Some e
    | _ -> err ("attribute '" + (err_id x) + "' requires one argument here")
  else None

let attrs_get_exp (x:id) (a:attrs):exp =
  match attrs_get_exp_opt x a with
  | None -> err ("expected to find attribute '" + (err_id x) + "'")
  | Some e -> e

let attrs_get_id_opt (x:id) (a:attrs):id option =
  match skip_loc_opt (attrs_get_exp_opt x a) with
  | None -> None
  | Some (EVar x) -> Some x
  | Some _ -> err ("argument to attribute '" + (err_id x) + "' must be an identifier")

let attrs_get_id (x:id) (a:attrs):id =
  match skip_loc (attrs_get_exp x a) with
  | EVar x -> x
  | _ -> err ("argument to attribute '" + (err_id x) + "' must be an identifier")

let qprefix (s:string) (t:string):string = s + (t.Replace(".", "__"))

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
      if (!this.cur_indent + s).Length > breakCol then
        let space0 = s.IndexOf(" ") in
        let quote0 = s.IndexOf("\"") in
        let width = breakCol - (!this.cur_indent).Length in
        if space0 >= 0 && (quote0 < 0 || quote0 >= width) then
          // try to find last space in s[0 .. breakCol-indentsize]
          // if that fails, find first space in s
          let s1 = s.Substring(0, width) in
          let breakAt = if s1.Contains(" ") then s1.LastIndexOf(" ") else s.IndexOf(" ") in
          let sBreak1 = s.Substring(0, breakAt) in
          let sBreak2 = s.Substring(breakAt).Trim() in
          if sBreak1.Contains("//") then (s, None) else // don't break up a "//" comment
          (sBreak1, Some sBreak2)
        else if s.Contains("\"") && not (s.Contains("\\\"")) then
          // put strings on their own line
          let i1 = s.IndexOf("\"") in
          let i2 = s.IndexOf("\"", i1 + 1) + 1 in
          if i2 > 0 && (i2 - i1) < s.Length then
            if i1 = 0 then
              let s1 = s.Substring(0, i2) in
              let s2 = s.Substring(i2).Trim() in
              (s1, Some s2)
            else
              let s1 = s.Substring(0, i1).Trim() in
              let s2 = s.Substring(i1) in
              if s1.Contains("//") then (s, None) else
              (s1, Some s2)
          else (s, None)
        else (s, None)
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

let debug_print_state ():print_state =
  {
    print_out = System.Console.Out;
    print_interface = None;
    cur_loc = ref {loc_file = "<stdout>"; loc_line = 0; loc_col = 0; loc_pos = 0};
    cur_indent = ref "";
  }

let reprint_file = ref (None:string option);
let reprint_verbatims = ref true;
let reprint_ghost_decls = ref true;
let reprint_specs = ref true;
let reprint_ghost_stmts = ref true;
let reprint_loop_invs = ref true;
let reprint_blank_lines = ref true;
let gen_lemma_sym_count = ref 0
let gen_lemma_sym ():int = incr gen_lemma_sym_count; !gen_lemma_sym_count
