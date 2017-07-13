// Turn high-level AST into low-level lemmas:
//   - call transform.fs
//   - then generate lemmas

module Emit_common

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

type print_state =
  {
    print_out:System.IO.TextWriter;
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

let exp_of_conjuncts (es:exp list):exp =
  match es with
  | [] -> EBool true
  | h::t -> List.fold (fun conj e -> EOp (Bop BAnd, [conj; e])) h t

let gen_lemma_sym_count = ref 0
let gen_lemma_sym ():int = incr gen_lemma_sym_count; !gen_lemma_sym_count

let get_code_exp (e:exp):exp = map_exp (fun e -> match e with EOp (CodeLemmaOp, [ec; el]) -> Replace ec | _ -> Unchanged) e
let get_lemma_exp (e:exp):exp = map_exp (fun e -> match e with EOp (CodeLemmaOp, [ec; el]) -> Replace el | _ -> Unchanged) e

let stateToOp (e:exp):exp map_modify =
  match e with
  | EOp (OperandArg _, [e]) -> Replace e
  | EOp (StateOp (x, prefix, t), es) -> Replace (vaApp ("op_" + prefix) es)
  | _ -> Unchanged

type build_env =
  {
    proc:proc_decl;
    loc:loc;
    is_instruction:bool;
    is_operand:bool;
    is_refined:bool;
    is_refined_while_proc:bool;
    is_refined_while_ghosts:id list;
    is_inside_while:bool;
    is_bridge:bool;
    is_framed:bool;
    code_name:id;
    spec_name:id;
    frame_exp:id -> exp;
    eReq:bool -> exp;
    prefix:string; // for inline if/else
    conds:exp list; // for inline if/else
  }

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

(* Build code value for body of procedure Q:
function method{:opaque} va_code_Q(...):va_code
{
  va_Block(va_CCons(va_code_P(va_op_reg(EBX), 10), va_CCons(va_code_P(va_op_reg(EBX), 20), va_CCons(va_code_P(va_op_reg(EBX), 30), va_CNil()))))
}
*)
let rec build_code_stmt (env:env) (s:stmt):exp list =
  let rec assign e =
    match e with
    | ELoc (_, e) -> assign e
    | EApply (Id x, es) when Map.containsKey (Id x) env.procs ->
        let es = List.filter (fun e -> match e with EOp (Uop UGhostOnly, _) -> false | _ -> true) es in
        let es = List.map get_code_exp es in
        let es = List.map (map_exp stateToOp) es in
        [vaApp ("code_" + x) es]
    | _ -> []
    in
  match s with
  | SLoc (loc, s) ->
      try List.map (fun e -> ELoc (loc, e)) (build_code_stmt env s) with err -> raise (LocErr (loc, err))
  | SBlock b -> [build_code_block env b]
  | SIfElse (SmPlain, cmp, ss1, ss2) ->
      let e1 = build_code_block env ss1 in
      let e2 = build_code_block env ss2 in
      [vaApp "IfElse" [map_exp stateToOp cmp; e1; e2]]
  | SIfElse (SmInline, cmp, ss1, ss2) ->
      let e1 = build_code_block env ss1 in
      let e2 = build_code_block env ss2 in
      [EOp (Cond, [map_exp stateToOp cmp; e1; e2])]
  | SWhile (cmp, ed, invs, ss) ->
      let ess = build_code_block env ss in
      [vaApp "While" [map_exp stateToOp cmp; ess]]
  | SAssign (_, e) -> assign e
  | _ -> []
and build_code_block (env:env) (stmts:stmt list):exp =
  let empty = vaApp "CNil" [] in
  let cons el e = vaApp "CCons" [e; el] in
  let slist = List.collect (build_code_stmt env) stmts in
  let elist = List.fold cons empty (List.rev slist) in
  vaApp "Block" [elist]

let varLhsOfId (x:id):lhs = (x, Some (None, NotGhost))

type proc_arg =
| ArgOperand of id * string * typ
| ArgState of id * typ
| ArgExp of exp

type es_call =
  {
    esc_loc:loc;
    esc_proc:proc_decl;
    esc_call_id:int;
    esc_state:exp;
    esc_foralls:formal list;
    esc_nonmod_exps:exp list;
    esc_id_decls:formal list;
    esc_id_exps:exp list;
    //esc_procArgs:formal list;
    esc_specModsIo:(inout * proc_arg * id option) list;
    esc_specMods:proc_arg list;
    esc_stmts:stmt list;
    esc_ghost_ret:stmt list * formal list * exp * stmt list;
  }
and es_ifelse =
  {
    esi_kind:stmt_modifier;
    esi_formals:formal list;
    esi_replacements:(exp * id * id * id) list
  }
and estmt =
| EsLoc of loc * estmt
| EsCallProc of es_call
| EsGhost of stmt list
| EsStmts of stmt list
| EsIfElse of exp * estmt list * estmt list * es_ifelse
| EsWhile of exp * (loc * exp) list * (loc * exp list) * estmt list

type abstract_call_info =
| AciCall of exp list * es_call  // the expression list is a list of antecedent-guards
| AciIfElse of exp list * es_ifelse  // the expression list is a list of antecedent-guards

let formals_of_call aci =
  match aci with
  | AciCall (_, esc) -> esc.esc_id_decls
  | AciIfElse (_, esi) -> esi.esi_formals

let clean_unrefined (loc:loc, s:spec):(loc * spec) =
  match s with
  | Requires (EOp (Uop UUnrefinedSpec, [e])) -> (loc, Requires e)
  | Ensures  (EOp (Uop UUnrefinedSpec, [e])) -> (loc, Ensures e)
  | _ -> (loc, s)

let skip_unrefined (loc:loc, s:spec):(loc * spec) list =
  match s with
  | Requires (EOp (Uop UUnrefinedSpec, [e])) -> []
  | Ensures  (EOp (Uop UUnrefinedSpec, [e])) -> []
  | _ -> [(loc, s)]

let get_unrefined (loc:loc, s:spec):(loc * spec) list =
  match s with
  | Requires (EOp (Uop UUnrefinedSpec, [e])) -> [(loc, Requires e)]
  | Ensures  (EOp (Uop UUnrefinedSpec, [e])) -> [(loc, Ensures e)]
  | _ -> []

type emit_area_fun = EmitCode | EmitReq | EmitEns
type emit_area_proc = EmitAbstract | EmitConcrete | EmitLemma
type emit_area_mod = EmitModReq | EmitModEns | EmitModAbstract | EmitModRefined | EmitModCall

(*
We have to generate:
- function code
  - parameters, including operands
  - body (from procedure body)
- function req
  - parameters, including values in operands
  - body (from requires clauses)
- function ens
  - parameters, including values in operands
  - body (from ensures clauses)
- procedure abstract
  - parameters/returns
    - inputs/outputs to procedure, including values in operands
    - inputs/outputs to all calls inside the procedure, including values in operands
  - requires: for each call to other procedure:
    - forall ghostParams :: req(...) ==> exists ghostParams :: ens(...)
  - ensures: forall ghostParams :: req(...) ==> exists ghostParams :: ens(...)
- procedure concrete
  - parameters/returns, including operands
  - requires/ensures (boilerplate)
  - ensures: forall ghostParams :: req(...) ==> exists ghostParams :: ens(...)
  - body
    - calls to other concrete procedures
    - call abstract procedure
- procedure lemma
  - parameters/returns, including operands
  - requires/ensures (boilerplate)
  - requires/ensures (directly from requires/ensures)
  - body
    - for {:refined false}: directly
    - for {:refined true}:
      - assert req(...ghostParams...)
      - call concrete procedure
      - exists ghostsRets :: ens(...ghostParams, ghostRets...)

We divide parameters/returns into "non-modifies" and "modifies".
"modifies" includes:
  - parameters generated by modifies clauses
  - values contained in operands (e.g. the value 5 contained in register eax)
"non-modifies" are:
  - inline
  - ghost
  - operands themselves (e.g. the operand representing register eax)
For example, for an instruction:
   add(inout operand dst, in operand src, ghost g) modifies flags
In req/ens/abstract, add(eax, ebx) will lead to modifies parameters for eax, ebx, and flags but g will be non-modifies.
In code/concrete/lemma, flags will be modifies, while eax, ebx, and g will be non-modifies.

Parameters are always listed in the following order:
  (non-modifies returns)
@ (non-modifies params)
@ (modifies from returns)
@ (modifies from params)
@ (modifies from modifies clauses)
*)

// compute the parameters for functions (code/requires/ensures)
// pfIsRet == false ==> pf is input parameter
// pfIsRet == true ==> pf is output return value
let area_fun_param (modifies:bool) (pfIsRet:bool) (area:emit_area_fun) (pf:pformal):formal list =
  let (x, t, storage, io, attrs) = pf in
  let fx = (x, Some t) in
  let fOld = (old_id x, Some t) in
  match (area, storage, io, pfIsRet, modifies) with
  | (EmitCode, XInline, _, false, false) -> [fx]
  | (EmitCode, (XGhost | XAlias _), _, _, false) -> []
  | (EmitCode, XOperand xo, _, _, false) -> [(x, Some (tOperand xo))]
  | (EmitCode, _, _, _, true) -> []
  | (_, XOperand _, _, _, false) -> []
  | (_, (XInline | XGhost), _, _, true) -> []
  | ((EmitReq | EmitEns), XInline, _, false, false) -> [fx]
  | ((EmitReq | EmitEns), XGhost, _, _, false) -> [fx]
  | (EmitReq, XOperand _, (In | InOut), false, true) -> [fOld]
  | (EmitReq, XOperand _, Out, false, true) -> []
  | (EmitReq, XOperand _, _, true, true) -> []
  | (EmitEns, XOperand _, In, false, true) -> [fOld]
  | (EmitEns, XOperand _, InOut, false, true) -> [fOld; fx]
  | (EmitEns, XOperand _, Out, false, true) -> [fx]
  | (EmitEns, XOperand _, _, true, true) -> [fx]
  | ((EmitReq | EmitEns), XAlias _, _, _, _) -> notImplemented "alias arguments not yet supported for {:refined true} procedures"
  | (_, XInline, _, true, _) -> internalErr "XInline"
  | (_, XState _, _, _, _) -> internalErr "XState"
  | (_, XPhysical, _, _, _) -> internalErr "XPhysical"

let area_fun_params (area:emit_area_fun) (prets:pformal list) (pargs:pformal list):formal list =
  (List.collect (area_fun_param false true area) prets) @
  (List.collect (area_fun_param true true area) prets) @
  (List.collect (area_fun_param false false area) pargs) @
  (List.collect (area_fun_param true false area) pargs)

// compute parameters/returns for procedures (abstract/concrete/lemma) 
// pfIsRet == false ==> pf is input parameter
// pfIsRet == true ==> pf is output return value
// ret == false ==> generate parameters
// ret == true ==> generate return values
let area_proc_param (modifies:bool) (pfIsRet:bool) (ret:bool) (area:emit_area_proc) (pf:pformal):pformal list =
  let (x, t, storage, io, attrs) = pf in
  let pfOld () = (old_id x, t, storage, io, attrs) in
  let pfOp xo = (x, tOperand xo, XPhysical, In, attrs) in
  match (ret, area, storage, io, pfIsRet, modifies) with
  | (_, (EmitAbstract | EmitConcrete), XGhost, _, _, _) -> []
  | (_, EmitLemma, XGhost, _, _, false) -> if ret = pfIsRet then [pf] else []
  | (false, EmitAbstract, XInline, _, false, false) -> [pf]
  | (false, EmitAbstract, XInline, _, false, true) -> []
  | (false, EmitAbstract, XOperand _, _, _, false) -> []
  | (false, EmitAbstract, XOperand _, _, _, true) -> [pfOld ()]
  | (true, EmitAbstract, XOperand _, _, _, _) -> []
  | (_, (EmitConcrete | EmitLemma), _, _, _, true) -> []
  | (false, (EmitConcrete | EmitLemma), XInline, _, false, false) -> [pf]
  | (_, (EmitConcrete | EmitLemma), XOperand xo, _, _, false) -> if ret = pfIsRet then [pfOp xo] else []
  | (_, EmitLemma, XAlias _, _, _, false) -> []
  | (true, _, XInline, _, false, _) -> []
  | (_, (EmitAbstract | EmitConcrete), XAlias _, _, _, _) -> notImplemented "alias arguments not yet supported for {:refined true} procedures"
  | (_, _, XInline, _, true, _) -> internalErr "XInline"
  | (_, _, XState _, _, _, _) -> internalErr "XState"
  | (_, _, XPhysical, _, _, _) -> internalErr "XPhysical"

let area_proc_params (ret:bool) (area:emit_area_proc) (prets:pformal list) (pargs:pformal list):pformal list =
  (List.collect (area_proc_param false true ret area) prets) @
  (List.collect (area_proc_param true true ret area) prets) @
  (List.collect (area_proc_param false false ret area) pargs) @
  (List.collect (area_proc_param true false ret area) pargs)

type connect_env =
  {
    connect_typs:Map<id,typ>;
    connect_map:Map<id, id>;
    connect_subst:Map<id, exp>;
    connect_subst_ghost:Map<id, exp>;
  }

let connect_estmts (env:env) (p:proc_decl) (mods:id list) (ss:estmt list):(connect_env * estmt list) =
  let operandMap = Map.ofList (List.map (fun (x, t, s, _, _) -> (x, (t, s))) (p.pargs @ p.prets)) in
  let connect_estmt (cenv:connect_env) (s:estmt):(connect_env * estmt) =
    let rewrite (csubst:Map<id, exp>) (ss:stmt list):stmt list =
      map_stmts (subst_reserved_exp csubst) (fun _ -> Unchanged) ss in
    let rec f (cenv:connect_env) (s:estmt):(connect_env * estmt) =
      match s with
      | EsLoc (loc, s) -> let (m, s) = f cenv s in (m, EsLoc (loc, s))
      | EsCallProc c ->
          let xn = "x" + (string (gen_lemma_sym ())) + "_" in
          let new_id (x:id) =
            match x with Id x -> Reserved (xn + x) | Reserved x -> Reserved (xn + x) | Operator _ -> internalErr "EApply: Operator" in
          let specModsIo = c.esc_specModsIo in
          let getOpt u = match u with Some u -> u | None -> internalErr "getOpt" in
          let rewrite_mod (cenv_read:connect_env) (cenv_write:connect_env) (io:inout, arg:proc_arg, formal_id:id option):(connect_env * (formal list * proc_arg list * (id * exp) list) * (id * exp) list) =
            match arg with
            | ArgOperand (x, xo, t) ->
                let idExp = vaEvalOp xo t c.esc_state (EVar x) in
                let x1 = match Map.tryFind x cenv_read.connect_map with None -> old_id x | Some y -> y in
                match io with
                | In ->
                  let pairs = [(old_id (getOpt formal_id), EVar x1)] in
                  (cenv_write, ([], [ArgOperand (x1, xo, t)], []), pairs)
                | InOut | Out ->
                  let x2 = new_id x in
                  let cenv_write =
                    {
                      connect_typs = Map.add x t cenv_write.connect_typs;
                      connect_map = Map.add x x2 cenv_write.connect_map;
                      connect_subst = cenv_write.connect_subst;
                      connect_subst_ghost = Map.add x (EVar x2) cenv_write.connect_subst_ghost;
                    } in
                  let pairs = [(old_id (getOpt formal_id), EVar x1); (getOpt formal_id, EVar x2)] in
                  (cenv_write, ([(x2, Some t)], (if io = InOut then [ArgOperand (x1, xo, t); ArgOperand (x2, xo, t)] else [ArgOperand (x2, xo, t)]), [(x2, idExp)]), pairs)
            | ArgState (x, t) ->
                let idExp = stateGet {env with state = c.esc_state} x in
                //let x1 = match Map.tryFind x cenv.connect_map with None -> old_id x | Some y -> (match io with In -> old_id x | InOut | Out -> y) in
                let x1 = match Map.tryFind x cenv_read.connect_map with None -> old_id x | Some y -> y in
                let id = match formal_id with Some id -> id | None -> x in
                match io with
                | In ->
                  let pairs = [(old_id id, EVar x1)] in
                  (cenv_write, ([], [ArgState (x1, t)], []), pairs)
                | InOut | Out ->
                  let x2 = new_id x in
                  let cenv_write =
                    {
                      connect_typs = Map.add x t cenv_write.connect_typs;
                      connect_map = Map.add x x2 cenv_write.connect_map;
                      connect_subst = Map.add x (EVar x2) cenv_write.connect_subst;
                      connect_subst_ghost = Map.add x (EVar x2) cenv_write.connect_subst_ghost;
                    } in
                  let pairs = [(old_id id, EVar x1); (id, EVar x2)] in
                  (cenv_write, ([(x2, Some t)], (if io = InOut then [ArgState (x1, t); ArgState (x2, t)] else [ArgState (x2, t)]), [(x2,idExp)]), pairs)
            | ArgExp e -> (cenv_write, ([], [ArgExp e], []), [(getOpt formal_id, e)])
            in
          let rewrite_g_prev = rewrite cenv.connect_subst_ghost in
          let (cenv, idsSpecMods, pairs) = List_mapFoldFlip2 (rewrite_mod cenv) cenv specModsIo in
          let (ids, specMods, idExpAssigns) = List.unzip3 idsSpecMods in
          let (ids, specMods, idExpAssigns, pairs) = (List.concat ids, List.concat specMods, List.concat idExpAssigns, List.concat pairs) in
          let idExps = idExpAssigns |> List.map (fun (x,_) -> EVar x) in  // we choose the variable names, rather than the expressions they stand for
          let idExps = c.esc_id_exps @ idExps in
          let ens_subst (e:exp):exp =
            let m = Map.ofList pairs in
            subst_reserved_exp m e
            in
          let rewrite_s = rewrite cenv.connect_subst in
          let c =
            { c with
                esc_id_decls = ids;
                esc_id_exps = idExps;
                esc_specMods = specMods;
                esc_stmts = rewrite_s c.esc_stmts @ List.map (fun (x, e) -> SAssign ([(x, None)], e)) idExpAssigns;
                esc_ghost_ret = (let (s, tmps, ens, a) = c.esc_ghost_ret in (rewrite_g_prev s, tmps, ens_subst ens, a))
            } in
          (cenv, EsCallProc c)
      | EsGhost ss -> (cenv, EsGhost (rewrite cenv.connect_subst_ghost ss))
      | EsStmts ss -> (cenv, EsStmts (rewrite cenv.connect_subst ss))
      | EsIfElse (e, thn, els, { esi_kind = SmInline }) ->
          let (m0, thn) = List_mapFoldFlip f cenv thn in
          let (m1, els) = List_mapFoldFlip f cenv els in
          let Map_domain (A:Map<'key,'value>):Set<'key> =
            Map.fold (fun s k v -> Set.add k s) Set.empty A in
          let Map_combine (A:Map<'key,'value>) (B:Map<'key,'value>):Map<'key,'value> =
            Map.fold (fun m k v -> m.Add (k,v)) A B in
          let merge_maps (A:Map<id,'a>) (B:Map<id,'a>) (resolver:id -> 'a -> 'a option -> 'a):(Map<id,'a> * Map<id,'a>) =
            let ids = Set.union (Map_domain A) (Map_domain B) in
            let f (common_m:Map<id,'a>, new_m:Map<id,'a>) id =
              match Map.tryFind id A, Map.tryFind id B with
              | None, None -> internalErr "unexpected case"
              | Some x, None | None, Some x ->
                  (common_m, new_m.Add (id, resolver id x None))
              | Some x, Some y ->
                  if x = y then
                    (common_m.Add (id, x), new_m)
                  else
                    (common_m, new_m.Add (id, resolver id x (Some y)))
            in
            Set.fold f (Map.empty, Map.empty) ids in
          let merg_prefix = "merg" + (string (gen_lemma_sym ())) + "_" in
          let merge_connect_map id ax bx =
            match ax with Id x -> Reserved (merg_prefix + x) | Reserved x -> Reserved (merg_prefix + x) | Operator _ -> internalErr "EApply: Operator" in
          let (mm, mm_new) = merge_maps m0.connect_map m1.connect_map merge_connect_map in
          let mm = Map_combine mm mm_new in
          let merge_connect_expmap id ax bx =
            EVar (Map.find id mm)
          let blend (a:Map<id,exp>) (b:Map<id,exp>):Map<id,exp> =
            let (common_map,new_map) = merge_maps a b merge_connect_expmap in
            Map_combine common_map new_map in
          let cenv =
            {
                connect_typs = Map_combine m0.connect_typs m1.connect_typs;
                connect_map = mm;
                connect_subst = blend m0.connect_subst m1.connect_subst;
                connect_subst_ghost = blend m0.connect_subst_ghost m1.connect_subst_ghost
            } in
          let old_incarnation_exp id =
            match (Map.tryFind id operandMap, Map.tryFind id env.ids) with
            | (Some (t, XOperand xo), _) -> vaEvalOp xo t (EVar (Reserved "s0")) (EVar id)
            | (_, Some (StateInfo _)) -> stateGet {env with state = EVar (Reserved "s0")} id
            | _ -> internalErr ("old_incarnation: " + (err_id id))
            in
          let incarnation_exp id mp = match Map.tryFind id mp with None -> old_incarnation_exp id | Some y -> EVar y in
          let incarnation id mp = match Map.tryFind id mp with None -> old_id id | Some y -> y in
          let add_assignments (es:estmt list) (mp:Map<id,id>):estmt list =
            let f es id v = SAssign ([(v, None)], incarnation_exp id mp) :: es in
            let asgnmts = Map.fold f [] mm_new in
            es @ [EsStmts (List.rev asgnmts)]
            in
          let thn = add_assignments thn m0.connect_map in
          let els = add_assignments els m1.connect_map in
          let mm_new_list = Map.toList mm_new in
          let frmls = List.map (fun (k, v) -> (v, Some (Map.find k cenv.connect_typs))) mm_new_list in
          let replacements = List.map (fun (k, v) -> (e, v, incarnation k m0.connect_map, incarnation k m1.connect_map)) mm_new_list in
          (cenv, EsIfElse (e, thn, els, { esi_kind = SmInline; esi_formals = frmls; esi_replacements = replacements }))
      | EsIfElse _ -> raise (err "{:refined true} procedures may contain ghost and inline if/else anywhere, and may not contain ordinary if/else statements")
      | EsWhile _ -> raise (err "{:refined true} procedures with while statements must contain exactly one while statement, possible preceded by ghost statements, whose body consists of one procedure call")
      in
    f cenv s
  let subst_arg (x, _, storage, _, _):(id * exp) list =
    match storage with XOperand _ -> [(x, EVar (old_id x))] | _ -> []
    in
  let csubst_args = List.collect subst_arg p.pargs in
  let csubst_rets = List.collect subst_arg p.prets in
  let csubst_mod = List.map (fun x -> (x, EVar (old_id x))) mods in
  let csubst = Map.ofList csubst_mod in
  let csubst_ghost = Map.ofList (csubst_args @ csubst_rets @ csubst_mod) in
  let cenv = { connect_typs = Map.empty; connect_map = Map.empty; connect_subst = csubst; connect_subst_ghost = csubst_ghost } in
  List_mapFoldFlip connect_estmt cenv ss

let rec stmts_of_estmt (physical:bool) (ghost:bool) (s:estmt):stmt list =
  match s with
  | EsLoc (loc, s) -> List.map (fun s -> SLoc (loc, s)) (stmts_of_estmt physical ghost s)
  | EsCallProc {esc_proc = p; esc_stmts = ss; esc_ghost_ret = gr} ->
      match gr with
      | (sTrigger, tmps, ens, assigns) ->
          let ph = if physical then ss else [] in
          let tr = if ghost then sTrigger else [] in
          let gh =
            if ghost && tmps <> [] then
              let trEx = EApply (Reserved ("triggerexists_" + (string_of_id p.pname)), List.map (fun (x, _) -> EVar x) tmps) in
              SExists (tmps, [[trEx]], EOp (Bop BAnd, [trEx;ens])) :: assigns
            else
              []
          in
          ph @ tr @ gh
  | EsGhost ss -> if ghost then ss else []
  | EsStmts ss -> if physical then ss else []
  | EsIfElse (e, ss1, ss2, _) ->
      [SIfElse (SmPlain, e, stmts_of_estmts physical ghost ss1, stmts_of_estmts physical ghost ss2)]
  | EsWhile (e, invs, dec, ss) -> if physical then [SWhile (e, invs, dec, stmts_of_estmts physical ghost ss)] else []
and stmts_of_estmts (physical:bool) (ghost:bool) (ss:estmt list):stmt list = List.collect (stmts_of_estmt physical ghost) ss

let rec calls_of_estmt (guards:exp list) (s:estmt):abstract_call_info list =
  match s with
  | EsLoc (loc, s) -> calls_of_estmt guards s
  | EsCallProc c -> [AciCall (guards, c)]
  | EsGhost ss -> []
  | EsStmts ss -> []
  | EsIfElse (e, ss1, ss2, info) ->
      let thnGuards = e :: guards in
      let elsGuards = EOp (Uop UNot, [e]) :: guards in
      (calls_of_estmts thnGuards ss1) @ (calls_of_estmts elsGuards ss2) @ [AciIfElse (guards, info)]
  | EsWhile (e, invs, dec, ss) -> calls_of_estmts guards ss
and calls_of_estmts (guards:exp list) (ss:estmt list):abstract_call_info list = List.collect (calls_of_estmt guards) ss

let specArgEns (inSpec:bool) (s0:id option) (sM:id) (modifies:bool) (x, t, g, io, a):exp list =
  match g with
  | XGhost -> if inSpec && not modifies then [EVar x] else []
  | XInline -> if modifies then [] else [EVar x]
  | XOperand xo ->
    (
      if not modifies then [] else
      let f s = vaEvalOp xo t (EVar s) (EVar x) in
      if inSpec then
        match (s0, io) with
        | (None, _) | (Some _, Out) -> [f sM]
        | (Some s0, In) -> [f s0]
        | (Some s0, InOut) -> [f s0; f sM]
      else
        match s0 with None -> [] | Some s0 -> [f s0]
    )
  | XPhysical _ -> internalErr ("specArg: XPhysical: " + (err_id x))
  | XAlias _ -> notImplemented ("specArg: XAlias: " + (err_id x))
  | XState _ -> err ("unexpected state variable declaration: " + (err_id x))

let specArgEnss (inSpec:bool) (s0:id) (sM:id) (prets:pformal list) (pargs:pformal list):exp list =
  (List.collect (specArgEns inSpec None sM false) prets) @
  (List.collect (specArgEns inSpec (Some s0) sM false) pargs) @
  (List.collect (specArgEns inSpec None sM true) prets) @
  (List.collect (specArgEns inSpec (Some s0) sM true) pargs)

let specModIo (env:env) (area:emit_area_mod) (loc:loc, s:spec):(inout * (id * typ)) list =
  let (useOld, useNew, suppressRead) =
    match area with
    | EmitModRefined | EmitModCall -> (false, true, false)
    | EmitModAbstract -> (true, false, true)
    | EmitModReq -> (false, true, true)
    | EmitModEns -> (true, true, true)
    in
  match s with
  | Requires _ | Ensures _ -> []
  | Modifies (readWrite, e) ->
    (
      let io = if readWrite then InOut else In in
      match skip_loc (exp_abstract false e) with
      | EVar x ->
        (
          match Map.tryFind x env.ids with
          | Some (StateInfo (_, _, t)) ->
            (if useOld then [(io, (old_id x, t))] else []) @
            (if useNew && (not suppressRead || readWrite) then [(io, (x, t))] else [])
          | _ -> internalErr ("specMod: could not find variable " + (err_id x))
        )
      | _ -> []
    )

let specMod (env:env) (area:emit_area_mod) (loc:loc, s:spec):formal list =
  List.map (fun (_, (x, t)) -> (x, Some t)) (specModIo env area (loc, s))

let argModIo (e:exp) (formal_id, _, _, io:inout, _):(inout * proc_arg * id option) list =
  match skip_loc e with
  | EOp (OperandArg (x, xo, t), _) -> [(io, ArgOperand (x, xo, t), Some formal_id)]
  | EOp (StateOp (x, prefix, t), es) -> [(io, ArgState (x, t), Some formal_id)]
  | EOp (RefineOp, [EOp (Uop UConst, [c]); _; _]) -> [(io, ArgExp c, Some formal_id)]
  | _ -> []

let paramMod (pf:pformal):formal list =
  match pf with
  | (x, t, XOperand _, InOut, _) -> [(x, Some t)]
  | _ -> []

let ghostFormal (pf:pformal):formal list =
  match pf with
  | (x, t, XGhost, _, _) -> [(x, Some t)]
  | _ -> []

let is_ghost_formal (f:pformal):bool =
  match f with
  (_, _, XGhost, _ , _) -> true
  | _ -> false

let drop_ghosts (ff:pformal list):pformal list =
  List.filter (fun f -> not (is_ghost_formal f)) ff

let makeSpecTrigger (name:id) (id:exp) (es:exp list):exp =
  EApply (Reserved ("trigger_" + (string_of_id name)), id::es)

let makeSpecTriggerExists (name:id) (es:exp list):exp =
  EApply (Reserved ("triggerexists_" + (string_of_id name)), es)

let makeSpecForalls (names:(id * exp list) list) (id:int option) (xs:formal list) (e:exp):exp =
  let es = List.map (fun (x, _) -> EVar x) xs in
  let triggerList = List.map (fun x -> [x]) in
  match (id, xs) with
  | (_, []) -> e
  | (None, _::_) ->
      let xid = Reserved "id" in
      let triggers = List.map (fun (name, es2) -> makeSpecTrigger name (EVar xid) (es @ es2)) names in
      EBind (Forall, [], (xid, Some tInt)::xs, triggerList triggers, EOp (Bop BImply, [and_of_list triggers; e]))
  | (Some n, _::_) ->
      let triggers = List.map (fun (name, es2) -> makeSpecTrigger name (EInt (bigint n)) (es @ es2)) names in
      EBind (Forall, [], xs, triggerList triggers, EOp (Bop BImply, [and_of_list triggers; e]))

let makeSpecForall (name:id) (id:int option) (xs:formal list) (e:exp):exp = makeSpecForalls [(name, [])] id xs e

let lemma_block (sM:lhs) (cM:lhs) (bM:lhs) (eb:exp) (es0:exp) (esN:exp):stmt list =
  if !concise_lemmas then
    let eBlock = vaApp "lemma_block" [eb; es0; esN] in
    [SAssign ([sM; cM; bM], eBlock)] // ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  else
    let cM = (fst cM, None) in
    let eBlock = vaApp "lemma_block" [EVar (fst cM); EVar (fst bM); es0; esN] in
    [SAssign ([cM], vaApp "block_head" [eb]); SAssign ([bM], vaApp "block_tail" [eb]); SAssign ([sM], eBlock)]

let rec build_lemma_stmt (env:env) (benv:build_env) (block:id) (b1:id) (code:id) (src:id) (res:id) (resIn:id) (loc:loc) (s:stmt):ghost * bool * estmt list =
  let sub es e = subst_reserved_exp (Map.ofList [(Reserved "s", es)]) e in
  let sub_src e = sub (EVar src) e in
  let rec assign lhss e =
    let lhss = List.map (fun xd -> match xd with (Reserved "s", None) -> (src, None) | _ -> xd) lhss in
    match e with
    | ELoc (loc, e) -> try assign lhss e with err -> raise (LocErr (loc, err))
    | EApply (x, es) when Map.containsKey x env.procs ->
        let p = Map.find x env.procs in
        let pargs = List.filter (fun (_, _, storage, _, _) -> match storage with XAlias _ -> false | _ -> true) p.pargs in
        let (pretsOp, pretsNonOp) = List.partition (fun (_, _, storage, _, _) -> match storage with XOperand _ -> true | _ -> false) p.prets in
        let pretsArgs = pretsOp @ pargs in
//        let procArgs = (List.collect (area_proc_fret EmitCall) p.prets) @ (List.collect (area_proc_farg EmitCall) p.pargs) in
        let specModsIo:(inout * proc_arg * id option) list = List.map (fun (io, f) -> (io, ArgState f, None)) (List.collect (specModIo env EmitModCall) p.pspecs) in
        let argModsIo = List.concat (List.map2 argModIo es pretsArgs) in
        let new_id (x:id) =
          let xn = "x" + (string (gen_lemma_sym ())) + "_" in
          match x with Id x -> Reserved (xn + x) | Reserved x -> Reserved (xn + x) | Operator _ -> internalErr "EApply: Operator" in
//        let procArgs = List.map (fun (x, t) -> (new_id x, t)) procArgs in
//        let specMods = List.map (fun (x, t) -> (new_id x, t)) specMods in
        let es = List.map (fun e -> match e with EOp (Uop UGhostOnly, [e]) -> sub_src e | _ -> e) es in
        let es = List.map (fun e -> match e with EOp (CodeLemmaOp, [_; e]) -> sub_src e | _ -> e) es in
//        let es = List.map get_lemma_exp es in
        let es = List.map (map_exp stateToOp) es in
        let foralls = List.collect ghostFormal pargs in
        let eNonMod (ghostExp:bool) (x, _, storage, _, _) e =
          match storage with
          | XInline -> if ghostExp then [] else [e]
          | XGhost -> if ghostExp then [e] else [EVar x]
          | _ -> []
          in
        let esNonMod = List.concat (List.map2 (eNonMod false) pretsArgs es) in
        let esGhost = List.concat (List.map2 (eNonMod true) pretsArgs es) in
        let lemmaPrefix = if benv.is_refined then "refined_" else "lemma_" in
        let eLem (_, _, storage, _, _) e = match storage with XGhost -> [] | _ -> [e] in
        let esLem = if benv.is_refined then List.concat (List.map2 eLem pretsArgs es) else es in
        let lem = vaApp (lemmaPrefix + (string_of_id x)) ([EVar block; EVar src; EVar resIn] @ esLem) in
        let blockIntros = if !concise_lemmas then [] else [SAssign ([varLhsOfId b1], vaApp "block_tail" [EVar block])] in
        let blockLhss = List.map varLhsOfId (if !concise_lemmas then [b1; res] else [res]) in
        let (callId, sTrigger) =
          match (benv.is_refined && not benv.is_refined_while_proc, foralls) with
          | (true, _::_) ->
              let callId = gen_lemma_sym () in
              let trigger = makeSpecTrigger p.pname (EInt (bigint callId)) esGhost in
              (callId, [SAssert (assert_attrs_default, trigger)])
          | _ -> (0, [])
          in
        let drop_ghost_args (f:pformal) (l:lhs) =
          match (f, benv.is_refined) with ((_,_,XGhost,_,_), true) -> [] | _ -> [l]
          in
        let get_ghost_out_arg_actual_formal (f:pformal) (l:lhs) =
          match f with
          | (id,tp,XGhost,_,_) ->
              let itmp = string (gen_lemma_sym ()) in
              let gtmp = Reserved ("gtmp" + itmp) in
              [(f,l,(gtmp,Some tp))]
          | _ -> [] in
        let ghost_out_map = List.concat (List.map2 get_ghost_out_arg_actual_formal pretsNonOp lhss) in
        let lhss = List.concat (List.map2 drop_ghost_args pretsNonOp lhss) in
        let assign_ghost_outs =
          match (benv.is_refined, benv.is_refined_while_proc, ghost_out_map) with
          | (false, _, _) | (_, true, _) | (_, _, []) -> (sTrigger, [], EBool true, [])
          | _ ->
              let pspecs = List.collect skip_unrefined p.pspecs in
              let posts = List.collect (fun (_, sp) -> match sp with Ensures e -> [e] | _ -> []) pspecs in
              let inp = List.concat (List.map2 (fun (fid, _, storage, _, _) actl -> if storage = XGhost || storage = XInline then [(fid, actl)] else []) p.pargs es) in
              let outp = List.map (fun ((fid, _, _, _, _), _, (id, _)) -> (fid, EVar id)) ghost_out_map in
              let m = Map.ofList (inp @ outp) in
              let ens = subst_reserved_exp m (exp_of_conjuncts posts) in
              let ens = exp_abstract true ens in
              let ghost_tmps_exists_lhss = List.map (fun (pf, l, f) -> f) ghost_out_map in
              let assignments_from_tmps_to_ghost_actuals = List.map (fun a -> match a with (_, l, (rid, _)) -> SAssign ([l], EVar rid)) ghost_out_map in
              (sTrigger, ghost_tmps_exists_lhss, ens, assignments_from_tmps_to_ghost_actuals)
          in
        let esc_call =
          {
            esc_loc = loc;
            esc_proc = p;
            esc_call_id = callId;
            esc_state = EVar res;
            esc_foralls = foralls;
            esc_nonmod_exps = esNonMod;
            esc_id_decls = [];
            esc_id_exps = [];
            //esc_procArgs = []; //procArgs;
            esc_specModsIo = argModsIo @ specModsIo;
            esc_specMods = [];
            esc_stmts = blockIntros @ [SAssign (blockLhss @ lhss, lem)];
            esc_ghost_ret = assign_ghost_outs;
          } in
        (NotGhost, false, [EsCallProc esc_call])
    | _ -> (Ghost, false, if benv.is_refined_while_proc && not benv.is_inside_while then [] else [EsGhost [SAssign (lhss, sub_src e)]])
    in
  match s with
  | SLoc (loc, s) ->
      try
        let (g, b, ss) = build_lemma_stmt env benv block b1 code src res resIn loc s in
        (g, b, List.map (fun s -> EsLoc (loc, s)) ss)
      with err -> raise (LocErr (loc, err))
  | SLabel _ -> err "unsupported feature: labels (unstructured code)"
  | SGoto _ -> err "unsupported feature: 'goto' (unstructured code)"
  | SReturn _ -> err "unsupported feature: 'return' (unstructured code)"
  | SAssume e -> (Ghost, false, [EsGhost [SAssume (sub_src e)]])
  | SAssert (attrs, e) ->
      if attrs.is_refined then (Ghost, false, [EsStmts [SAssert (attrs, sub_src e)]])
      else (Ghost, false, [EsGhost [SAssert (attrs, sub_src e)]])
  | SCalc (oop, contents) ->
      let ccs = List.map (build_lemma_calcContents env benv src res loc sub_src) contents in
      (Ghost, false, [EsGhost [SCalc (oop, ccs)]])
  | SVar (_, _, _, (XPhysical | XOperand _ | XInline | XAlias _), _, _) -> (Ghost, false, [])
  | SVar (x, t, m, g, a, eOpt) -> (Ghost, false, [EsGhost [SVar (x, t, m, g, a, mapOpt sub_src eOpt)]])
  | SAlias _ -> (Ghost, false, [])
  | SBlock b -> (NotGhost, true, build_lemma_block env benv (EVar code) src res loc b)
  | SIfElse (SmGhost, e, ss1, ss2) ->
      let e = sub_src e in
      let ss1 = build_lemma_ghost_stmts env benv src res loc ss1 in
      let ss2 = build_lemma_ghost_stmts env benv src res loc ss2 in
      (Ghost, false, [EsGhost [SIfElse (SmGhost, e, ss1, ss2)]])
  | SIfElse (SmPlain, e, ss1, ss2) ->
      let cond = Reserved ("cond_" + (reserved_id code)) in
      let i1 = string (gen_lemma_sym ()) in
      let s1 = Reserved("s" + i1) in
      let codeCond = vaApp "get_ifCond" [EVar code] in
      let codet = vaApp "get_ifTrue" [EVar code] in
      let codef = vaApp "get_ifFalse" [EVar code] in
      let lem = vaApp "lemma_ifElse" [codeCond; codet; codef; EVar src; EVar res] in
      let s1Lhs = (s1, Some (Some tState, Ghost)) in
      let sb1 = SAssign ([varLhsOfId cond; s1Lhs], lem) in
      let sbT = build_lemma_block env benv codet s1 res loc ss1 in
      let sbF = build_lemma_block env benv codef s1 res loc ss2 in
      (NotGhost, true, [EsStmts [sb1]; EsIfElse (EVar cond, sbT, sbF, { esi_kind = SmPlain; esi_formals = []; esi_replacements = [] })])
  | SIfElse (SmInline, e, ss1, ss2) ->
      let sbT = build_lemma_block env benv (EVar code) src res loc ss1 in
      let sbF = build_lemma_block env benv (EVar code) src res loc ss2 in
      (NotGhost, true, [EsIfElse (e, sbT, sbF, { esi_kind = SmInline; esi_formals = []; esi_replacements = [] })])
  | SWhile (e, invs, ed, ss) ->
      let codeCond = vaApp "get_whileCond" [EVar code] in
      let codeBody = vaApp "get_whileBody" [EVar code] in
      let i1 = string (gen_lemma_sym ()) in
      let i2 = string (gen_lemma_sym ()) in
      let (n1, s1, r1) = (Reserved ("n" + i1), Reserved ("s" + i1), Reserved ("sW" + i1)) in
      let r2 = (Reserved ("sW" + i2)) in
      let lem = vaApp "lemma_while" [codeCond; codeBody; EVar src; EVar res] in
      let lemTrue = vaApp "lemma_whileTrue" [codeCond; codeBody; EVar n1; EVar r1; EVar res] in
      let lemFalse = vaApp "lemma_whileFalse" [codeCond; codeBody; EVar r1; EVar res] in
      let n1Lhs = (n1, Some (Some tInt, Ghost)) in
      let s1Lhs = (s1, Some (Some tState, Ghost)) in
      let r1Lhs = (r1, Some (Some tState, Ghost)) in
      let r2Lhs = (r2, Some (Some tState, Ghost)) in
      let slem = SAssign ([n1Lhs; r1Lhs], lem) in
      let slemTrue = SAssign ([s1Lhs; r2Lhs], lemTrue) in
      let slemFalse = SAssign ([(res, None)], lemFalse) in
      let whileInv = vaApp "whileInv" [codeCond; codeBody; EVar n1; EVar r1; EVar res] in
      let r1Update = SAssign ([(r1, None)], EVar r2) in
      let n1Update = SAssign ([(n1, None)], EOp (Bop BSub, [EVar n1; EInt bigint.One])) in
      let sbBody = build_lemma_block env {benv with is_inside_while = true} codeBody s1 r2 loc ss in
      let nCond = EOp (Bop BGt, [EVar n1; EInt bigint.Zero]) in
      let invFrame = (loc, benv.frame_exp r1) in
      let invFrames = if benv.is_framed || benv.is_refined_while_proc then [invFrame] else [] in
      let (refinedStmts, wPre, wPost, invs, ed) =
        if not benv.is_refined_while_proc then ([], [], [], invs, ed) else
        let whileErr () = err "while statement in {:refined} procedure must contain exactly one procedure call with no return values, followed by zero or more ghost statements" in
        let assignList =
          match benv.proc.pbody with
          | None -> internalErr "SWhile"
          | Some allSs ->
              List.collect (fun s -> match skip_locs_stmt s with [SAssign ([(x1, None)], EVar x2)] -> [(x1, x2)] | _ -> []) allSs
          in
        let assignMap = List.map (fun (x1, x2) -> (x1, EVar x2)) assignList in
        let assignRevMap = List.map (fun (x1, x2) -> (x2, EVar x1)) assignList in
        match ss with
        | s::ghost_ss ->
          (
            match skip_loc_stmt s with
            | SAssign (xs, e) ->
              (
                match skip_loc e with
                | EApply (xf, es) ->
                    // Reveal specs of current procedure Q and called procedure P:
                    //   reveal_va_spec_P();
                    //   reveal_va_spec_Q();
                    let ghosts = benv.is_refined_while_ghosts in
                    let ghostOlds = List.map (fun x -> SVar (old_id x, None, Immutable, XGhost, [], Some (EVar x))) ghosts in
                    let ghostMap = List.map (fun x -> (x, EVar (old_id x))) ghosts in
                    let ghostExps = List.map EVar ghosts in
                    let reveal_of_spec x = SAssign ([], EOp(Uop UReveal, [EVar x])) in
                    let reveals = [reveal_of_spec benv.spec_name; reveal_of_spec (Reserved ("spec_" + (string_of_id xf)))] in
                    let foralls = List.collect ghostFormal benv.proc.pargs in
                    // exists h2:int {:trigger va_triggerexists_Loop(h2)}{:trigger va_triggerexists_LoopBody(h2)}{:trigger va_trigger_Loop(va_id, g, h2)} ::
                    // va_triggerexists_Loop(h2) && va_triggerexists_LoopBody(h2) &&
                    let exFormal (x1, x2) =
                      let f y (x, t, _, _, _) = if x = y then [t] else [] in
                      match (List.collect (f x1) benv.proc.prets, List.collect (f x2) benv.proc.pargs) with
                      | ([t], [_]) -> (x1, Some t)
                      | _ -> err ("variable " + (err_id x1) + " must be a return value, initialized with an argument")
                      in
                    let exFormals = List.map exFormal assignList in
                    let exTrig xp = makeSpecTriggerExists xp (List.map (fun (x, _) -> EVar x) assignList) in
                    let exTrig1 = exTrig benv.proc.pname in
                    let exTrig2 = exTrig xf in
                    let eForalls = List.map (fun (x, _) -> EVar x) foralls in
                    let fTrigger = makeSpecTrigger benv.proc.pname (EVar (Reserved "id")) eForalls in
                    let fTrigger = subst_reserved_exp (Map.ofList assignRevMap) fTrigger in
                    let ex e =
                      match exFormals with
                      | [] -> e
                      | _ -> EBind (Exists, [], exFormals, [[exTrig1]; [exTrig2]; [fTrigger]], and_of_list [exTrig1; exTrig2; e])
                      in
                    // invariant forall id, g {:trigger va_trigger_Q(id, g)}{:trigger va_trigger_P(id, g, i)}
                    //  :: va_trigger_Q(id, g) && va_trigger_P(id, g, i)
                    //  ==> va_get_ok(src) && invs(src) ==> va_get_ok(r1) && invs(r1)
                    // where i represents is_refined_while_ghosts
                    let invs = (loc, stateGet env (Id "ok"))::invs in
                    let invs0Map = Map.ofList (ghostMap @ assignMap) in
                    let invs0 = List_mapSnd (fun e -> subst_reserved_exp invs0Map (sub (EVar src) e)) invs in
                    let invs1 = List_mapSnd (sub (EVar r1)) invs in
                    let fromInvs invs = and_of_list (List.map (fun (loc, e) -> ELoc (loc, e)) invs) in
                    let invExp = EOp (Bop BImply, [fromInvs invs0; ex (fromInvs invs1)]) in
                    let invInvs = (loc, makeSpecForalls [(benv.proc.pname, []); (xf, ghostExps)] None foralls invExp) in
                    let wPre = List.map (fun x -> SVar (prev_id x, None, Immutable, XGhost, [], Some (EVar x))) ghosts in
                    // assert forall id, g :: va_trigger_P(va_id, g, i) ==> va_trigger_P(id, g, prev_i);
                    let esPost = (List.map (fun (x, _) -> EVar x) foralls) @ (List.map (fun x -> EVar (prev_id x)) ghosts) in
                    let ePost = makeSpecTrigger xf (EVar (Reserved "id")) esPost in
                    let eForall = makeSpecForalls [(xf, ghostExps)] None foralls ePost in
                    let wPost = match ghosts with [] -> [] | _ -> [SAssert (assert_attrs_default, eForall)] in
                    // work around Dafny issue, also generate better diagnostics:
                    // forall id, g {:trigger va_trigger_Q(id, g)}{:trigger va_trigger_P(id, g, i)}
                    //  | va_trigger_Q(id, g) && va_trigger_P(id, g, i) ==> va_get_ok(src) && invs(src)
                    // ensures va_get_ok(r1) && invs(r1)
                    // { assert va_get_ok(r1) && invs(r1); }
                    let sForall =
                      match invInvs with
                      | (_, EBind (Forall, [], xs, triggers, EOp (Bop BImply, [lhs; rhs]))) ->
                        let sAssert = SAssert (assert_attrs_default, rhs) in
                        [SForall (xs, triggers, lhs, rhs, [sAssert])]
                      | _ -> []
                      in
                    (reveals @ ghostOlds, wPre, wPost @ sForall, [invInvs], (loc, []))
                | _ -> whileErr ()
              )
            | _ -> whileErr ()
          )
        | _ -> whileErr ()
        in
      let invs = List_mapSnd (sub (EVar r1)) invs in
      let ed =
        match ed with
        | (loc, []) -> (loc, [EVar n1])
        | (loc, es) -> (loc, List.map (sub (EVar r1)) es)
        in
      let whileBody = (EsStmts (slemTrue::wPre))::sbBody @ [EsStmts (r1Update::n1Update::wPost)] in
      let sWhile = EsWhile (nCond, (loc, whileInv)::invs @ invFrames, ed, whileBody) in
      (NotGhost, true, [EsStmts (refinedStmts @ [slem]); sWhile; EsStmts [slemFalse]])
  | SAssign (lhss, e) -> assign lhss e
  | SForall (xs, ts, ex, e, ss) ->
      let ts = List.map (List.map sub_src) ts in
      let ex = sub_src ex in
      let e = sub_src e in
      let ss = build_lemma_ghost_stmts env benv src res loc ss in
      (Ghost, false, [EsGhost [SForall (xs, ts, ex, e, ss)]])
  | SExists (xs, ts, e) ->
      let ts = List.map (List.map sub_src) ts in
      let e = sub_src e in
      (Ghost, false, [EsGhost [SExists (xs, ts, e)]])
and build_lemma_ghost_stmt (env:env) (benv:build_env) (src:id) (res:id) (loc:loc) (s:stmt):stmt list =
  let dummyId = Reserved "dummy" in
  let (g, _, ss) = build_lemma_stmt env benv dummyId dummyId dummyId src res res loc s in
  (match g with Ghost -> () | NotGhost -> err "Only ghost statements allowed here.  Ghost statements include 'forall', 'ghost if', lemma calls, assignments to ghost variables, assertions, etc, but not 'while' or 'if' or procedure calls.");
  stmts_of_estmts false true ss
and build_lemma_ghost_stmts (env:env) (benv:build_env) (src:id) (res:id) (loc:loc) (stmts:stmt list):stmt list =
  List.collect (build_lemma_ghost_stmt env benv src res loc) stmts
and build_lemma_calcContents (env:env) (benv:build_env) (src:id) (res:id) (loc:loc) (sub_src:exp -> exp) (cc:calcContents):calcContents =
  let {calc_exp = e; calc_op = oop; calc_hints = hints} = cc in
  {calc_exp = sub_src e; calc_op = oop; calc_hints = List.map (build_lemma_ghost_stmts env benv src res loc) hints}
and build_lemma_stmts (env:env) (benv:build_env) (block:id) (src:id) (res:id) (loc:loc) (stmts:stmt list):estmt list =
  match stmts with
  | [] ->
      let lem = vaApp "lemma_empty" [EVar src; EVar res] in
      [EsStmts [SAssign ([(res, None)], lem)]]
  | hd::tl ->
    (
      let i1 = string (gen_lemma_sym ()) in
      let (r1, c1, b1) = (Reserved ("s" + i1), Reserved ("c" + i1), Reserved ("b" + i1)) in
      let (ghost, addBlockLemma, sb2) = build_lemma_stmt env benv block b1 c1 src r1 res loc hd in
      match (ghost, addBlockLemma) with
      | (Ghost, _) ->
          let sb3 = build_lemma_stmts env benv block src res loc tl in
          sb2 @ sb3
      | (NotGhost, true) ->
          let sLoc = one_loc_of_stmt loc hd in
          let sb1 = lemma_block (varLhsOfId r1) (varLhsOfId c1) (varLhsOfId b1) (EVar block) (EVar src) (EVar res) in
          let sb3 = build_lemma_stmts env benv b1 r1 res loc tl in
          (EsStmts sb1)::(sb2 @ sb3)
      | (NotGhost, false) ->
          let sb3 = build_lemma_stmts env benv b1 r1 res loc tl in
          sb2 @ sb3
    )
and build_lemma_block (env:env) (benv:build_env) (code:exp) (src:id) (res:id) (loc:loc) (stmts:stmt list):estmt list =
  let i0 = string (gen_lemma_sym ()) in
  let b0 = Reserved ("b" + i0) in
  let codeCond = vaApp "get_block" [code] in
  let sb1 = SAssign (List.map varLhsOfId [b0], codeCond) in
  let sb2 = build_lemma_stmts env benv b0 src res loc stmts in
  (EsStmts [sb1])::sb2

let build_lemma_spec (env:env) (src:id) (res:exp) (loc:loc, s:spec):((loc * spec) list * exp list) =
  try
    match s with
    | Requires e ->
        let e = exp_refined e in
        let m = Map.ofList [(Reserved "old_s", EVar src); (Reserved "s", EVar src)] in
        ([(loc, Requires (subst_reserved_exp m e))], [])
    | Ensures e ->
        let e = exp_refined e in
        let m = Map.ofList [(Reserved "old_s", EVar src); (Reserved "s", res)] in
        ([(loc, Ensures (subst_reserved_exp m e))], [])
    | Modifies (readWrite, e) ->
        let e = exp_refined e in
        let m = Map.ofList [(Reserved "old_s", EVar src); (Reserved "s", EVar src)] in
        ([], [subst_reserved_exp m e])
  with err -> raise (LocErr (loc, err))

let filter_proc_attr (x, es) =
  match x with
  | Id ("timeLimit" | "timeLimitMultiplier" | "tactic") -> true
  | _ -> false
  in

let fArg (x, t, g, io, a):exp list =
  match g with
  | XInline -> [EVar x]
  | XOperand _ -> [EVar x]
//  | XOperand _ -> [vaApp "op" [EVar x]]
  | _ -> []
  in

// Generate framing postcondition, which limits the variables that may be modified:
//   ensures  va_state_eq(va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_ok(va_sM, va_update(dummy2, va_sM, va_update(dummy, va_sM, va_s0))))))
let makeFrame (env:env) (p:proc_decl) (s0:id) (sM:id) =
  let specModsIo = List.collect (specModIo env EmitModCall) p.pspecs in
  let frameArg (isRet:bool) e (x, _, storage, io, _) =
    match (isRet, storage, io) with
    | (true, XOperand xo, _) | (_, XOperand xo, (InOut | Out)) -> vaApp ("update_" + xo) [EVar x; EVar sM; e]
    | _ -> e
    in
  let frameMod e (io, (x, _)) =
    match io with
    | (InOut | Out) ->
      (
        match Map.tryFind x env.ids with
        | Some (StateInfo (prefix, es, t)) -> vaApp ("update_" + prefix) (es @ [EVar sM; e])
        | _ -> internalErr ("frameMod: could not find variable " + (err_id x))
      )
    | _ -> e
    in
  let e = EVar s0 in
  let e = List.fold (frameArg true) e p.prets in
  let e = List.fold (frameArg false) e p.pargs in
  let e = List.fold frameMod e specModsIo in
  vaApp "state_eq" [EVar sM; e]

(* Build function for code for procedure Q
function method{:opaque} va_code_Q(iii:int, dummy:va_operand, dummy2:va_operand):va_code
{
  va_Block(...)
}
*)
let build_code (env:env) (benv:build_env) (stmts:stmt list):fun_decl =
  let p = benv.proc in
  let fParams = area_fun_params EmitCode p.prets p.pargs in
  {
    fname = benv.code_name;
    fghost = NotGhost;
    fargs = fParams;
    fret = tCode;
    fbody =
      if benv.is_instruction then Some (attrs_get_exp (Id "instruction") p.pattrs)
      else Some (build_code_block env stmts);
    fattrs = [(Id "opaque", [])];
  }

// Declare abstract lemma for procedure Q
//   lemma{:warnShadowing false} va_abstract_Q(iii:int, va_old_dummy:int, dummy:int, ..., va_x23_ok:bool, va_x23_eax:int)
let build_abstract (env:env) (benv:build_env) (cenv:connect_env) (estmts:estmt list):proc_decl =
  let p = benv.proc in
  let loc = benv.loc in
  let prets = area_proc_params true EmitAbstract p.prets p.pargs in
  let pargs = area_proc_params false EmitAbstract p.prets p.pargs in

  // For each call:
  //   P(ebx, 10, 100);
  // guarded by inline-if conditions
  //   IIC
  // generate one precondition:
  //   requires IIC ==> forall g:int{:trigger va_trigger_P(4, g)} :: va_trigger_P(4, g) ==> va_spec_P(10, g, va_old_ebx, va_x21_ebx, va_old_ok, va_x21_ok, va_old_eax, va_x21_eax)
  let calls = calls_of_estmts [] estmts in
  let pformal_of_formal (x, t) =
    let t = match t with Some t -> t | None -> internalErr "pformal_of_formal" in
    (x, t, XPhysical, In, [])
    in
  let pformals_calls = List.map pformal_of_formal (List.collect formals_of_call calls) in
  let spec_of_call c = Reserved ("spec_" + (string_of_id c.esc_proc.pname)) in
  let make_arg arg =
    match arg with
    | ArgOperand (x, _, _) | ArgState (x, _) -> EVar x
    | ArgExp e -> e
  let req_of_call aci =
    let rec add_antecedents_aux ants e =
      match ants with
      | [] -> e
      | a::ants -> EOp (Bop BImply, [a; add_antecedents_aux ants e])
      in
    let add_antecedents ants_rev e = add_antecedents_aux (List.rev ants_rev) e in
    match aci with
    | AciCall (guards, c) ->
        let args = List.map make_arg ((*List.map ArgState c.esc_procArgs @*) c.esc_specMods) in
        let args = c.esc_nonmod_exps @ args in
        let e = makeSpecForall c.esc_proc.pname (Some c.esc_call_id) c.esc_foralls (EApply (spec_of_call c, args)) in
        [(c.esc_loc, Requires (add_antecedents guards e))]
    | AciIfElse (guards, i) ->
        let build_ite (e, i, x, y) = EOp (Bop BEq, [EVar i; EOp (Cond, [e; EVar x; EVar y])]) in
        List.map (fun q -> (loc, Requires (add_antecedents guards (build_ite q)))) i.esi_replacements
    in
  let opaqueReqs = List.collect req_of_call calls in

  // Reveal specs of current procedure Q and called procedures P:
  //   reveal_va_spec_P();
  //   reveal_va_spec_Q();
  let reveal_of_spec x = SAssign ([], EOp(Uop UReveal, [EVar x])) in
  let specs =
    let spcs = List.collect (fun aci -> match aci with AciCall(_, c) -> [spec_of_call c] | _ -> []) calls in
    Set.toList (Set.ofList ((Reserved ("spec_" + (string_of_id p.pname)))::spcs)) in
  let reveals = List.map reveal_of_spec specs in

  let specArgs = area_fun_params EmitEns (drop_ghosts p.prets) p.pargs in
  let specArgEns (x, _) =
    if Map.containsKey x cenv.connect_subst_ghost
    then match Map.tryFind x cenv.connect_map with None -> old_id x | Some x -> x
    else x
    in
//  let specArgs = (List.collect specArg p.prets) @ (List.collect specArg p.pargs) in
  let specModsIo = List.collect (specModIo env EmitModCall) p.pspecs in
  let specModsOld = List.collect (specMod env EmitModAbstract) p.pspecs in
  let pspecMods = List.map pformal_of_formal specModsOld in
  let specModsEns =
    let f (io, (x, _)) =
      let new_id x = match Map.tryFind x cenv.connect_map with None -> old_id x | Some x -> x in
      match io with
      | In -> [old_id x]
      | Out -> [new_id x]
      | InOut -> [old_id x; new_id x]
      in
    List.collect f specModsIo in

  // Generate single postcondition for procedure Q:
  //    ensures  forall va_id:va_int, g:int{:trigger va_trigger_Q(va_id, g)} :: va_trigger_Q(va_id, g) ==> va_spec_Q(iii, g, va_old_dummy, dummy, ..., va_x23_ebx)
  let ensForalls = List.collect ghostFormal p.pargs in
  let eEns = EApply (benv.spec_name, List.map (fun x -> EVar x) ((List.map specArgEns specArgs) @ specModsEns)) in
  let opaqueEnss = [(loc, Ensures (makeSpecForall p.pname None ensForalls eEns))] in

  (* Generate body of abstract lemma Q as a forall statement:
  forall va_id:va_int, g:int
    {:trigger va_trigger_Q(va_id, g)}
    | (va_old_ok && F(va_old_eax + 3)) && g >= 0
    ensures va_spec_Q(iii, g, va_old_dummy, dummy, dummy2, va_old_ok, va_x23_ok, va_old_eax, va_x23_eax, va_old_ebx, va_x23_ebx)
  {
    ...ghost statements from Q...
  }
  *)
  let formal_to_var (f:pformal) =
    match f with
    | (id, t, vstorag, _, attrs) -> SVar (id, Some t, Immutable, vstorag, attrs, None)
  let ghost_returns_var_decls = List.map formal_to_var (List.filter is_ghost_formal p.prets) in
  let trEx = makeSpecTriggerExists p.pname (List.map (fun (x, _) -> EVar x) (List.collect ghostFormal p.prets)) in
  let forallBody = ghost_returns_var_decls @ (stmts_abstract true (stmts_of_estmts false true estmts)) @ [SAssert (assert_attrs_default, trEx)] in
  let forallStmt =
    match ensForalls with
    | [] -> SIfElse (SmGhost, benv.eReq true, forallBody, [])
    | _::_ ->
        let trigger = makeSpecTrigger p.pname (EVar (Reserved "id")) (List.map (fun (x, _) -> EVar x) ensForalls) in
        SForall ((Reserved "id", Some tInt)::ensForalls, [[trigger]], benv.eReq true, eEns, forallBody)
    in
  let condReqs = List.map (fun e -> (loc, Requires e)) benv.conds in
  {
    pname = Reserved (benv.prefix + "abstract_" + (string_of_id p.pname));
    pghost = Ghost;
    pinline = Outline;
    pargs = pargs @ pspecMods @ pformals_calls;
    prets = prets;
    palias = [];
    pspecs = condReqs @ opaqueReqs @ opaqueEnss;
    pbody = Some (reveals @ [forallStmt]);
    pattrs = (Id "warnShadowing", [EBool false])::(List.filter filter_proc_attr p.pattrs);
  }

let build_lemma (env:env) (benv:build_env) (b1:id) (stmts:stmt list) (estmts:estmt list):proc_decl =
  // generate va_lemma_Q or va_refined_Q
  let p = benv.proc in
  let loc = benv.loc in
  let codeName = benv.code_name in
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
  let (b0, s0, bM, sM, cM, sN) = (Reserved "b0", Reserved "s0", Reserved "bM", Reserved "sM", Reserved "cM", Reserved "sN") in
  let argB = (b0, tCodes, XPhysical, In, []) in
  let retB = (bM, tCodes, XPhysical, In, []) in
  let retR = (sM, tState, XPhysical, In, []) in
  let argS = (s0, tState, XPhysical, In, []) in
  let argR = (sN, tState, XPhysical, In, []) in
  let isRefined = benv.is_refined in
  let emitArea = if isRefined then EmitConcrete else EmitLemma in
  let prets = area_proc_params true emitArea p.prets p.pargs in
  let pargs = area_proc_params false emitArea p.prets p.pargs in
  let pargs = [argS; argR] @ pargs in
  let req = Requires (vaApp "require" [EVar b0; EApply (codeName, fArgs); EVar s0; EVar sN]) in // va_require(va_b0, va_code_Q(iii, va_op(dummy), va_op(dummy2)), va_s0, va_sN)
  let ens = Ensures (vaApp "ensure" ([EVar b0] @ (if !concise_lemmas then [EVar bM] else []) @ [EVar s0; EVar sM; EVar sN])) in // va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  let lCM  = (cM, Some (Some tCode, NotGhost)) in
  let sBlock = lemma_block (sM, None) lCM (bM, None) (EVar b0) (EVar s0) (EVar sN) in // ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  let sReveal = SAssign ([], EOp (Uop UReveal, [EVar codeName])) in // reveal_va_code_Q();
  let sOldS = SVar (Reserved "old_s", (if !concise_lemmas then Some tState else None), Immutable, XPhysical, [], Some (EVar s0)) in
  let eb1 = vaApp "get_block" [EVar cM] in
  let sb1 = SVar (b1, (if !concise_lemmas then Some tCodes else None), Immutable, XPhysical, [], Some eb1) in // var va_b1:va_codes := va_get_block(va_cM);

  // Generate well-formedness for operands:
  //   requires va_is_dst_int(dummy, s0)
  let reqIsArg (isRet:bool) (x, t, storage, io, _) =
    match (isRet, storage, io) with
    | (true, XOperand xo, _) | (false, XOperand xo, (InOut | Out)) -> [vaAppOp ("is_dst_" + xo + "_") t [EVar x; EVar s0]]
    | (false, XOperand xo, In) -> [vaAppOp ("is_src_" + xo + "_") t [EVar x; EVar s0]]
    | _ -> []
    in
  let reqIsExps =
    (List.collect (reqIsArg true) p.prets) @
    (List.collect (reqIsArg false) p.pargs)
    in
  let reqsIs = List.map (fun e -> (loc, Requires e)) reqIsExps in

  let reveal_spec = SAssign ([], EOp(Uop UReveal, [EVar benv.spec_name])) in

  let specModsIo = List.collect (specModIo env EmitModCall) p.pspecs in
  let eFrame = benv.frame_exp sM in

  if isRefined then
    (* Generate lemma for {:refined true} procedure Q:
    lemma va_refined_Q(va_b0:va_codes, va_s0:va_state, va_sN:va_state, iii:int, dummy:va_operand_lemma, dummy2:va_operand_lemma)
      returns (va_bM:va_codes, va_sM:va_state)
      requires va_require(va_b0, va_code_Q(iii, va_op(dummy), va_op(dummy2)), va_s0, va_sN)
      requires va_is_dst_int(dummy, s0)
      requires va_is_dst_int(dummy2, s0)
      ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
      ensures  forall va_id:va_int, g:int{:trigger va_trigger_Q(va_id, g)} :: va_trigger_Q(va_id, g) ==> va_spec_Q(iii, g, va_eval_operand_int(va_s0, dummy), va_eval_operand_int(va_sM, dummy), va_eval_operand_int(va_sM, dummy2), va_get_ok(va_s0), va_get_ok(va_sM), va_get_reg(EAX, va_s0), va_get_reg(EAX, va_sM), va_get_reg(EBX, va_s0), va_get_reg(EBX, va_sM))
      ensures  va_state_eq(va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_ok(va_sM, va_update(dummy2, va_sM, va_update(dummy, va_sM, va_s0))))))
      {
        ...calls to other procedures P...
        ...call to va_abstract_Q...
      }
    *)
    let reqs = reqsIs in
    let specArgsEns = specArgEnss true s0 sM (drop_ghosts p.prets) p.pargs in
    let specModsEns =
      let f env s x = stateGet {env with state = EVar s} x in
      let g (io, (x, t)) =
        match io with
        | In -> [f env s0 x]
        | Out -> [f env sM x]
        | InOut -> [f env s0 x; f env sM x]
        in
      List.collect g specModsIo
      in
    let ensForalls = List.collect ghostFormal p.pargs in // ensures forall va_id:va_int, g:int ...
    let eEns = EApply (benv.spec_name, specArgsEns @ specModsEns) in // ensures ... va_spec_Q(iii, g, va_eval_operand_int(va_s0, dummy), va_eval_operand_int(va_sM, dummy), va_eval_operand_int(va_sM, dummy2), va_get_ok(va_s0), va_get_ok(va_sM), va_get_reg(EAX, va_s0), va_get_reg(EAX, va_sM), va_get_reg(EBX, va_s0), va_get_reg(EBX, va_sM))
    let enss = [(loc, Ensures (makeSpecForall p.pname None ensForalls eEns)); (loc, Ensures eFrame)] in

    let (sLocalsToAbstract, sStmts) =
      if benv.is_instruction then
        ([], reveal_spec::(build_lemma_ghost_stmts env benv sM sM loc stmts))
      else if benv.is_refined_while_proc then
        let ss = stmts_refined (stmts_of_estmts true true estmts) in
        ([], ss)
      else
        let ss = stmts_refined (stmts_of_estmts true false estmts) in
        let calls = calls_of_estmts [] estmts in
        let specMods = List.collect (specMod env EmitModRefined) p.pspecs in
        let absArgsIo = specArgEnss false s0 sM p.prets p.pargs in
        let absArgsMods = List.map (fun (x, _) -> stateGet {env with state = EVar s0} x) specMods in
        let args_of_call aci =
          match aci with
          | AciCall (_, esc) -> esc.esc_id_exps
          | AciIfElse (_, esi) -> List.map (fun (x,_) -> EVar x) esi.esi_formals
          in
        let absArgsCalls = List.collect args_of_call calls in
        let sLocalsToAbstract = List.collect formals_of_call calls |> List.map (fun (x,t) -> SVar (x, t, Immutable, XPhysical, [], None)) in
        let absArgs = absArgsIo @ absArgsMods @ absArgsCalls in
        // Generate call from concrete lemma to abstract lemma:
        //   va_abstract_Q(iii, va_eval_operand_int(va_s0, dummy), va_eval_operand_int(va_sM, dummy), va_eval_operand_int(va_sM, dummy2), va_get_ok(va_s0), va_get_reg(EAX, va_s0), ..., va_get_reg(EAX, va_s17));
        let sAbstract = SAssign ([], EApply (Reserved (benv.prefix + "abstract_" + (string_of_id p.pname)), absArgs)) in
        (sLocalsToAbstract, ss @ [sAbstract])
      in
    let pspecs_unrefined = List.collect get_unrefined p.pspecs in
    let (pspecs_unrefined, pmods) = List.unzip (List.map (build_lemma_spec env s0 (EVar sM)) pspecs_unrefined) in
    let pspecs_unrefined = List.concat pspecs_unrefined in
    let (pspecs_u_reqs, pspecs_u_enss) = List.partition (fun s -> match s with (_, Requires _) -> true | _ -> false) pspecs_unrefined in
    {
      pname = Reserved ("refined_" + (string_of_id p.pname));
      pghost = Ghost;
      pinline = Outline;
      pargs = argB::pargs;
      prets = retB::retR::prets;
      palias = [];
      pspecs = (loc, req)::(List.map clean_unrefined reqs) @ pspecs_u_reqs @ (loc, ens)::pspecs_u_enss @ enss;
      pbody = Some ([sReveal; sOldS] @ sLocalsToAbstract @ sBlock @ (if benv.is_instruction then [] else [sb1]) @ sStmts);
      pattrs = List.filter filter_proc_attr p.pattrs;
    }
  else
    (* Generate lemma for {:refined false} procedure p:
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
    let pargs = argB::pargs in
    let prets = (if !concise_lemmas then [retB] else []) @ retR::prets in
    let reqs = if benv.is_bridge || benv.is_framed then reqsIs else [] in
    let sStmts =
      if benv.is_bridge then
        (* Generate body of bridge lemma:
        lemma va_lemma_Q(va_b0:va_codes, va_s0:va_state, va_sN:va_state, iii:int, dummy:va_operand_lemma, dummy2:va_operand_lemma, ghost g:int)
        ...
        {
          reveal_va_spec_Q();
          va_bM, va_sM := va_refined_Q(va_b0, va_s0, va_sN, iii, dummy, dummy2);
          assert va_trigger_Q(0, g);
        }
        *)
        let args = List.collect (fun (x, _, storage, _, _) -> match storage with XGhost -> [] | _ -> [EVar x]) pargs in
        let rets = List.map (fun (x, _, _, _, _) -> (x, None)) prets in
        let ghostArgs = ghostFormal
        let sRefined = SAssign (rets, EApply (Reserved ("refined_" + (string_of_id p.pname)), args)) in
        let ghostArgs = List.map (fun (x, _) -> EVar x) (List.collect ghostFormal p.pargs) in
        let sTrigger = SAssert (assert_attrs_default, makeSpecTrigger p.pname (EInt (bigint.Zero)) ghostArgs) in
        [reveal_spec; sRefined] @ (match ghostArgs with [] -> [] | _::_ -> [sTrigger])
      else if benv.is_instruction then
        // Body of instruction lemma
        let ss = build_lemma_ghost_stmts env benv sM sM loc stmts in
        [sReveal; sOldS] @ sBlock @ ss
      else if benv.is_operand then
        err "operand procedures must be declared extern"
      else
        // Body of ordinary lemma
        let ss = stmts_refined (stmts_of_estmts true true estmts) in
        [sReveal; sOldS] @ sBlock @ [sb1] @ ss
      in
    let ensFrame = if benv.is_bridge || benv.is_framed then [(loc, Ensures eFrame)] else [] in
    let (pspecs, pmods) = List.unzip (List.map (build_lemma_spec env s0 (EVar sM)) p.pspecs) in
    {
      pname = Reserved ("lemma_" + (string_of_id p.pname));
      pghost = Ghost;
      pinline = Outline;
      pargs = pargs;
      prets = prets;
      palias = [];
      pspecs = (loc, req)::(List.map clean_unrefined reqs) @ (loc, ens)::(List.map clean_unrefined (List.concat pspecs)) @ ensFrame;
      pbody = Some (sStmts);
      pattrs = List.filter filter_proc_attr p.pattrs;
    }

let build_proc (env:env) (loc:loc) (p:proc_decl):decls =
  gen_lemma_sym_count := 0;
  let isInstruction = List_mem_assoc (Id "instruction") p.pattrs in
  let isOperand = List_mem_assoc (Id "operand") p.pattrs in
  let isRefined = attrs_get_bool (Id "refined") false p.pattrs in
  let codeName = Reserved ("code_" + (string_of_id p.pname)) in
//  let specArgs = (List.collect specArg p.prets) @ (List.collect specArg p.pargs) in
//  let specMods = List.collect (specMod env false true) p.pspecs in
  let specId = Reserved ("spec_" + (string_of_id p.pname)) in
//  let paramMods = List.collect paramMod p.pargs in
//  let paramModsInOut = List.collect (fun (x, t) -> [(old_id x, t); (x, t)]) paramMods in
//  let reqArgs = List.collect specArg p.pargs in
  let reqMods = List.collect (specMod env EmitModReq) p.pspecs in
  let reqs =
    List.collect (fun (loc, s) ->
        match s with
        | Requires (EOp (Uop UUnrefinedSpec, _)) when isRefined -> []
        | Requires e -> [ELoc (loc, e)]
        | _ -> []
      ) p.pspecs in
  let enss =
    List.collect (fun (loc, s) ->
        match s with
        | Ensures (EOp (Uop UUnrefinedSpec, _)) when isRefined -> []
        | Ensures e -> [ELoc (loc, e)]
        | _ -> []
      ) p.pspecs in
  let eReq use_old = and_of_list (List.map (exp_abstract use_old) reqs) in
  let build_specs () =
    let reqArgs = area_fun_params EmitReq p.prets p.pargs in
    let ensArgs = area_fun_params EmitEns (drop_ghosts p.prets) p.pargs in
    let eSpecReq = and_of_list (List.map (exp_abstract true) reqs) in
    let eSpecEns = and_of_list (List.map (exp_abstract true) enss) in
    let ghostRets = List.collect ghostFormal p.prets in
    let eSpecEns =
      match ghostRets with
      | [] -> eSpecEns
      | _ ->
          let trEx = makeSpecTriggerExists p.pname (List.map (fun (x, _) -> EVar x) ghostRets) in
          EBind (Exists, [], ghostRets, [[trEx]], EOp (Bop BAnd, [trEx; eSpecEns]))
      in
    let eSpec = EOp (Bop BImply, [eSpecReq; eSpecEns]) in
    let specModsInOut = List.collect (specMod env EmitModEns) p.pspecs in
    let ghostArgs = List.collect ghostFormal p.pargs in
    let fTrigger =
      (* For procedures with ghost arguments g, generate a triggering function
      function va_trigger_Q(va_id:va_int, g:int):va_bool
      {
        true
      }
      *)
      {
        fname = Reserved ("trigger_" + (string_of_id p.pname));
        fghost = Ghost;
        fargs = (Reserved "id", Some tInt)::ghostArgs;
        fret = tBool;
        fbody = Some (EBool true);
        fattrs = [];
      }
    let fTriggerExists =
      (* For procedures with ghost return arguments h, generate a triggering function
      function va_triggerexists_Q(h:int):va_bool
      {
        true
      }
      *)
      {
        fname = Reserved ("triggerexists_" + (string_of_id p.pname));
        fghost = Ghost;
        fargs = ghostRets;
        fret = tBool;
        fbody = Some (EBool true);
        fattrs = [];
      }
    let fReq =
      // REVIEW: this is currently unused
      {
        fname = Reserved ("req_" + (string_of_id p.pname));
        fghost = Ghost;
        fargs = reqArgs (*@ paramMods*) @ reqMods;
        fret = tBool;
        fbody = Some (eReq false);
        fattrs = [(Id "opaque", [])];
      } in
    let fSpec =
      (* Generate spec for procedure Q, with the form: requires_1 && ... && requires_m ==> ensures_1 && ... && ensures_n
      function{:opaque} va_spec_Q(iii:int, g:int, va_old_dummy:int, dummy:int, dummy2:int, va_old_ok:bool, ok:bool, va_old_eax:int, eax:int, va_old_ebx:int, ebx:int):va_bool
      {
        (va_old_ok && F(va_old_eax + 3)) && g >= 0 ==> ok && G(eax)
      }
      *)
      {
        fname = specId;
        fghost = Ghost;
        fargs = ensArgs (*@ paramModsInOut*) @ specModsInOut;
        fret = tBool;
        fbody = Some eSpec;
        fattrs = [(Id "opaque", [])];
      } in
    (match ghostArgs with [] -> [] | _::_ -> [(loc, DFun fTrigger)]) @ [(loc, DFun fTriggerExists); (loc, DFun fSpec)]
    in
  let fSpecs = if isRefined then build_specs () else [] in
  let bodyDecls =
    match p.pbody with
    | None -> []
    | Some stmts ->
        let s0 = Reserved "s0" in
        let i1 = string (gen_lemma_sym ()) in
        let b1 = Reserved ("b" + i1) in
        let is_refined_while_proc = isRefined && (is_while_proc stmts) in
        let fGhost s xss =
          match s with
          | SVar (x, _, _, XGhost, _, _) -> x::(List.concat xss)
          | _ -> List.concat xss
          in
        let benv =
          {
            proc = p;
            loc = loc;
            is_instruction = isInstruction;
            is_operand = isOperand;
            is_refined = isRefined;
            is_bridge = false;
            is_framed = attrs_get_bool (Id "frame") true p.pattrs;
            is_refined_while_proc = is_refined_while_proc;
            is_refined_while_ghosts = if is_refined_while_proc then List.concat (gather_stmts fGhost (fun _ _ -> []) stmts) else [];
            is_inside_while = false;
            code_name = codeName;
            spec_name = specId;
            frame_exp = makeFrame env p s0;
            eReq = eReq;
            prefix = "";
            conds = [];
          }
          in
        let rstmts = stmts_refined stmts in
        let fCode = build_code env benv rstmts in
        let gen_estmts ss = build_lemma_stmts env benv b1 (Reserved "s0") (Reserved "sM") loc ss in
        if isRefined then
          if benv.is_refined_while_proc then
            let pLemma = build_lemma env benv b1 rstmts (gen_estmts stmts) in
            [(loc, DFun fCode); (loc, DProc pLemma)]
          else
            let rec expandInlineIf (loc:loc) (ss:stmt list) (conds:exp list) (prefix:string):proc_decl * decls =
              match ss with
              | (SLoc (loc, s))::posts -> expandInlineIf loc (s::posts) conds prefix
              | (SIfElse (SmInline, e, ss1, ss2))::posts when (List.forall (fun s -> match s with SForall _ -> true | _ -> false) posts) ->
                  let (pr1, ds1) = expandInlineIf loc (ss1 @ posts) (conds @ [e]) (prefix + "if_") in
                  let (pr2, ds2) = expandInlineIf loc (ss2 @ posts) (conds @ [EOp (Uop UNot, [e])]) (prefix + "else_") in
                  match (pr1.pbody, pr2.pbody) with
                  | (Some ss1, Some ss2) ->
                    let ss12 = SIfElse (SmPlain, e, ss1, ss2) in
                    let pr12 = {pr1 with pbody = Some [ss12]} in
                    (pr12, ds1 @ ds2)
                  | _ -> internalErr "expandInlineIf"
              | _ ->
                let rec blockify conds ss = match conds with [] -> ss | h::t -> blockify t [SBlock ss] in
                let ss = blockify conds ss in
                let benv = {benv with conds = conds; prefix = prefix} in
                let specModsConnect = List.collect (specMod env EmitModCall) p.pspecs in
                let estmts = gen_estmts ss in
                let (cenv, estmts) = connect_estmts env p (List.map fst specModsConnect) estmts in
                let pAbstract = build_abstract env benv cenv estmts in
                let dAbstract = if isInstruction then [] else [(loc, DProc pAbstract)] in
                let pRefined = build_lemma env benv b1 rstmts estmts in
                (pRefined, dAbstract)
            let (pRefined, dAbstracts) = expandInlineIf loc stmts [] "" in
            let dBridge =
              if attrs_get_bool (Id "bridge") false p.pattrs then
                let benvBridge = {benv with is_refined = false; is_bridge = true;} in
                let pBridge = build_lemma env benvBridge b1 rstmts (gen_estmts stmts) in
                [(loc, DProc pBridge)]
              else []
              in
            [(loc, DFun fCode)] @ dAbstracts @ [(loc, DProc pRefined)] @ dBridge
        else
          let pLemma = build_lemma env benv b1 rstmts (gen_estmts stmts) in
          [(loc, DFun fCode); (loc, DProc pLemma)]
    in
  fSpecs @ bodyDecls //@ blockLemmaDecls

let reprint_decls_rev = ref ([]:decls)

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
          | SLoc _ | SLabel _ | SGoto _ | SReturn | SBlock _ | SAlias _ -> Unchanged
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
          let envp = add_proc env p in
          (envp, if verify then build_proc (if isRecursive then envp else env) loc p else [])
      | _ -> (env, if verify then [(loc, d2)] else [])
      in
    (match (verify, !reprint_file) with (true, Some _) -> add_reprint_decl env loc dReprint | _ -> ());
    (env, decl)
  with err -> raise (LocErr (loc, err))

let build_decls (env:env) (ds:((loc * decl) * bool) list):decls =
  let (env, dss) = List_mapFoldFlip build_decl env ds in
  List.concat dss

