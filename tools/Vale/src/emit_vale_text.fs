module Emit_vale_text

open Ast
open Ast_util
open Parse_util
open Transform
open Emit_common
open Microsoft.FSharp.Math

let sid (x:id):string =
  match x with
  | Id s -> s
  | Reserved "this" -> "this"
  | Reserved s -> qprefix "va_" s
  | Operator s -> "operator(" + s + ")"

// non-associative: (n, n+1, n+1)
// left-associative: (n, n, n+1)
// right-associative: (n, n+1, n)
let prec_of_bop (op:bop):(int * int * int) =
  match op with
  | BEquiv -> (10, 10, 11)
  | BImply -> (12, 13, 13)
  | BExply -> (14, 14, 15)
  | BOr -> (16, 16, 17)
  | BAnd -> (18, 18, 19)
  | BEq | BNe -> (20, 20, 21)
  | BLe | BGe | BLt | BGt -> (25, 25, 25)
  | BAdd | BSub -> (30, 30, 31)
  | BMul | BDiv | BMod -> (40, 40, 41)
  | BIn | BOldAt | BCustom _ -> internalErr ("binary operator")

let string_of_bop (op:bop):string =
  match op with
  | BEquiv -> "<==>"
  | BImply -> "==>"
  | BExply -> "<=="
  | BAnd -> "&&"
  | BOr -> "||"
  | BEq -> "=="
  | BNe -> "!="
  | BLt -> "<"
  | BGt -> ">"
  | BLe -> "<="
  | BGe -> ">="
  | BAdd -> "+"
  | BSub -> "-"
  | BMul -> "*"
  | BDiv -> "/"
  | BMod -> "%"
  | BIn | BOldAt | BCustom _ -> internalErr "binary operator"

let rec string_of_typ (t:typ):string =
  match t with
  | TName x -> sid x
  | TApp (t, ts) -> (string_of_typ t) + "(" + (String.concat ", " (List.map string_of_typ ts)) + ")"

let rec string_of_exp_prec prec e =
  let r = string_of_exp_prec in
  let (s, ePrec) =
    let qbind q xs ts e = (q + " " + (string_of_formals xs) + (string_of_triggers ts) + " :: " + (r 5 e), 6) in
    match e with
    | ELoc (loc, ee) -> try (r prec ee, prec) with err -> raise (LocErr (loc, err))
    | EVar x -> (sid x, 99)
    | EInt i -> (string i, 99)
    | EReal r -> (r, 99)
    | EBitVector (n, i) -> ("bv" + (string n) + "(" + (string i) + ")", 99)
    | EBool true -> ("true", 99)
    | EBool false -> ("false", 99)
    | EString s -> ("\"" + s + "\"", 99)
    | EOp (Uop UReveal, [EVar x]) -> ("reveal " + (sid x) + "()", 99)
    | EOp (Uop UNot, [e]) -> ("!" + (r 99 e), 90)
    | EOp (Uop UNeg, [e]) -> ("-" + (r 99 e), 0)
    | EOp (Uop (UIs x), [e]) -> ((r 90 e) + " is " + (sid x), 90)
    | EOp (Uop UToOperand, [e]) -> ("@" + (r 99 e), 90)
    | EOp (Uop UOld, [e]) -> ("old(" + (r 99 e) + ")", 90)
    | EOp (Uop UConst, [e]) -> ("const(" + (r 99 e) + ")", 90)
    | EOp (Uop (UReveal | UGhostOnly | UCustom _ | UCustomAssign _), [_]) -> internalErr (sprintf "unary operator:%A" e)
    | EOp (Uop _, ([] | (_::_::_))) -> internalErr "unary operator"
    | EOp (Bop BIn, [e1; e2]) ->
        ((r 90 e1) + "?[" + (r 5 e2) + "]", 90)
    | EOp (Bop BOldAt, [e1; e2]) ->
        ("old[" + (r 5 e1) + "](" + (r 5 e2) + ")", 90)
    | EOp (Bop op, [e1; e2]) ->
        let (pe, p1, p2) = prec_of_bop op in
        ((r p1 e1) + " " + (string_of_bop op) + " " + (r p2 e2), pe)
    | EOp (Bop _, ([] | [_] | (_::_::_::_))) -> internalErr "binary operator"
    | EOp (Subscript, [e1; e2]) -> ((r 90 e1) + "[" + (r 90 e2) + "]", 90)
    | EOp (Update, [e1; e2; e3]) -> ((r 90 e1) + "[" + (r 90 e2) + " := " + (r 90 e3) + "]", 90)
    | EOp (Cond, [e1; e2; e3]) -> ("if " + (r 90 e1) + " then " + (r 90 e2) + " else " + (r 90 e3), 0)
    | EOp (FieldOp x, [e]) -> ((r 90 e) + "." + (sid x), 90)
    | EOp (FieldUpdate x, [e1; e2]) -> ((r 90 e1) + ".(" + (sid x) + " := " + (r 90 e2) + ")", 90)
    | EOp ((Subscript | Update | Cond | FieldOp _ | FieldUpdate _ | CodeLemmaOp | RefineOp | StateOp _ | OperandArg _), _) -> internalErr (sprintf "EOp:%A" e)
    | EApply (x, es) -> ((sid x) + "(" + (String.concat ", " (List.map (r 5) es)) + ")", 90)
    | EBind (Forall, [], xs, ts, e) -> qbind "forall" xs ts e
    | EBind (Exists, [], xs, ts, e) -> qbind "exists" xs ts e
    | EBind (Lambda, [], xs, _, e) -> ("(" + (string_of_formals xs) + " => " + (r 5 e) + ")", 90)
    | EBind (BindLet, [ex], [x], [], e) -> ("let " + (string_of_formal x) + " := " + (r 5 ex) + " in " + (r 5 e), 6)
    | EBind (BindSet, [], xs, ts, e) -> ("iset " + (string_of_formals xs) + (string_of_triggers ts) + " | " + (r 5 e), 6)
    | EBind ((Forall | Exists | Lambda | BindLet | BindAlias | BindSet), _, _, _, _) -> internalErr "EBind"
  in if prec <= ePrec then s else "(" + s + ")"
and string_of_ghost (g:ghost) = match g with Ghost -> "ghost " | NotGhost -> ""
and string_of_stmt_modifier (sm:stmt_modifier) = match sm with SmPlain -> "" | SmGhost -> "ghost " | SmInline -> "inline "
and string_of_var_storage (g:var_storage) =
  match g with
  | XGhost -> "ghost "
  | XPhysical -> ""
  | XOperand x -> x + " "
  | XInline -> "inline "
  | XAlias _ -> "{:alias}" // TODO
  | XState e -> "{:state" + (string_of_exp_prec 5 e) + "}"
and string_of_formal (x:id, t:typ option) = (sid x) + (match t with None -> "" | Some t -> ":" + (string_of_typ t))
and string_of_formals (xs:formal list):string = String.concat ", " (List.map string_of_formal xs)
and string_of_pformal (x:id, t:typ, g:var_storage, _, _) = (string_of_var_storage g) + (sid x) + ":" + (string_of_typ t)
and string_of_pformals (xs:pformal list):string = String.concat ", " (List.map string_of_pformal xs)
and string_of_trigger (es:exp list):string = "{:trigger " + (string_of_exps es) + "}"
and string_of_triggers (ts:exp list list):string = String.concat " " (List.map string_of_trigger ts)
and string_of_exp (e:exp):string = string_of_exp_prec 5 e
and string_of_exps (es:exp list):string = String.concat ", " (List.map string_of_exp es)
and string_of_exps_tail (es:exp list):string = String.concat "" (List.map (fun e -> ", " + string_of_exp e) es)
and string_of_args (es:exp list):string = "(" + String.concat ", " (List.map string_of_exp es) + ")"

let string_of_lhs_formal ((x, tOpt):lhs):string =
  match tOpt with
  | None -> sid x
  | Some (t, g) -> "(" + (string_of_ghost g) + "var " + (string_of_formal (x, t)) + ")"

let rec emit_stmt (ps:print_state) (s:stmt):unit =
  match s with
  | SLoc (loc, s) -> try ps.cur_loc := loc; emit_stmt ps s with err -> raise (LocErr (loc, err))
  | SLabel x -> ps.PrintLine (sid x + ":")
  | SGoto x -> ps.PrintLine ("goto " + sid x + ";")
  | SReturn -> ps.PrintLine ("return;")
  | SAssume e -> ps.PrintLine ("assume " + (string_of_exp e) + ";")
  | SAssert (attrs, e) ->
      let sAssert = if attrs.is_inv then "invariant" else "assert" in
      let sSplit = if attrs.is_split then "{:split_here}" else "" in
      let sRefined = if attrs.is_refined then "{:refined}" else "" in
      ps.PrintLine (sAssert + sSplit + sRefined + " " + (string_of_exp e) + ";")
  | SCalc (oop, contents) ->
      ps.PrintLine ("calc " + (match oop with None -> "" | Some op -> string_of_bop op + " ") + "{");
      ps.Indent();
      List.iter (fun {calc_exp = e; calc_op = oop; calc_hints = hints} ->
        ps.PrintLine ((string_of_exp e) + ";");
        (match oop with | None -> () | Some op -> ps.Unindent(); ps.PrintLine(string_of_bop op); ps.Indent());
        List.iter (emit_block ps) hints
      ) contents;
      ps.Unindent();
      ps.PrintLine("}")
  | SVar (x, tOpt, Immutable, XGhost, [], Some e) ->
      let st = match tOpt with None -> "" | Some t -> ":" + (string_of_typ t) in
      ps.PrintLine ("let " + (sid x) + st + " := " + (string_of_exp e) + ";")
  | SVar (x, tOpt, _, g, a, eOpt) ->
      let st = match tOpt with None -> "" | Some t -> ":" + (string_of_typ t) in
      let rhs = match eOpt with None -> "" | Some e -> " := " + (string_of_exp e) in
      ps.PrintLine ((string_of_var_storage g) + "var " + (sid x) + st + rhs + ";")
  | SAlias (x, y) ->
      ps.PrintLine ("let " + (sid x) + " @= " + (sid y) + ";")
  | SAssign ([], EOp (Uop (UCustomAssign s), [e])) ->
      ps.PrintLine ((string_of_exp e) + " " + s + ";")
  | SAssign (lhss, EOp (Uop (UCustomAssign s), [e])) ->
      ps.PrintLine ((String.concat ", " (List.map string_of_lhs_formal lhss)) + " " + s + " " + (string_of_exp e) + ";")
  | SAssign ([], e) -> ps.PrintLine ((string_of_exp e) + ";")
  | SAssign (lhss, e) ->
      ps.PrintLine ((String.concat ", " (List.map string_of_lhs_formal lhss)) + " := " + (string_of_exp e) + ";")
  | SBlock ss -> emit_block ps ss
  | SIfElse (sm, e, ss1, []) ->
      ps.PrintLine ((string_of_stmt_modifier sm) + "if (" + (string_of_exp e) + ")");
      emit_block ps ss1
  | SIfElse (sm, e, ss1, ss2) ->
      ps.PrintLine ((string_of_stmt_modifier sm) + "if (" + (string_of_exp e) + ")");
      emit_block ps ss1;
      ps.PrintLine ("else");
      emit_block ps ss2
  | SWhile (e, invs, (_, ed), ss) ->
      ps.PrintLine ("while (" + (string_of_exp e) + ")");
      ps.Indent ();
      List.iter (fun (_, e) -> ps.PrintLine ("invariant " + (string_of_exp e))) invs;
      ps.PrintLine ("decreases " + (match ed with [] -> "*" | es -> string_of_exps es));
      ps.Unindent ();
      emit_block ps ss;
  | SForall (xs, ts, ex, e, ss) ->
      ps.PrintLine ("forall " + (string_of_formals xs));
      ps.Indent ();
      List.iter (fun es -> ps.PrintLine (string_of_trigger es)) ts;
      (match skip_loc ex with EBool true -> () | _ -> ps.PrintLine ("| " + (string_of_exp ex)));
      ps.PrintLine (":: " + (string_of_exp e));
      ps.Unindent ();
      emit_block ps ss;
  | SExists (xs, ts, e) ->
      ps.PrintLine ("exists " + (string_of_formals xs) + (string_of_triggers ts) + " :: " + (string_of_exp e) + ";")
and emit_stmts (ps:print_state) (stmts:stmt list) = List.iter (emit_stmt ps) stmts
and emit_block (ps:print_state) (stmts:stmt list) =
  ps.PrintLine "{";
  ps.Indent ();
  emit_stmts ps stmts;
  ps.Unindent ();
  ps.PrintLine "}"

let string_of_is_refined (r:is_refined) =
  match r with
  | Refined -> ""
  | Unrefined -> "{:refined false}"

let string_of_raw_spec_kind (r:raw_spec_kind) =
  match r with
  | RRequires r -> "requires" + (string_of_is_refined r)
  | REnsures r -> "ensures" + (string_of_is_refined r)
  | RRequiresEnsures -> "requires/ensures"
  | RModifies false -> "reads"
  | RModifies true -> "modifies"

let emit_spec_exp (ps:print_state) (loc:loc, s:spec_exp):unit =
  match s with
  | SpecExp e -> ps.PrintLine ((string_of_exp e) + ";")
  | SpecLet (x, t, e) -> ps.PrintLine ("let " + (string_of_formal (x, t)) + " := " + (string_of_exp e) + ";")

let rec emit_lets (ps:print_state) (ls:lets list) (aliases:(id * id) list):unit =
  let flush () =
    match aliases with
    | [] -> ()
    | _ ->
        let f (x, y) = (sid x) + " @= " + (sid y) + ";" in
        ps.PrintLine (String.concat " " (List.map f (List.rev aliases)))
    in
  match ls with
  | [] -> flush ()
  | (LetsVar (x, t, e))::ls ->
      flush ();
      ps.PrintLine ((string_of_formal (x, t)) + " := " + (string_of_exp e) + ";");
      emit_lets ps ls []
  | (LetsAlias (x, y))::ls ->
      emit_lets ps ls ((x, y)::aliases)

let emit_spec (ps:print_state) (loc:loc, s:spec):unit =
  try
    match s with
    | Requires (r, e) ->
        ps.PrintLine ("requires" + (string_of_is_refined r) + " " + (string_of_exp e) + ";")
    | Ensures (r, e) ->
        ps.PrintLine ("ensures" + (string_of_is_refined r) + "  " + (string_of_exp e) + ";")
    | Modifies (false, e) -> ps.PrintLine ("reads " + (string_of_exp e) + ";")
    | Modifies (true, e) -> ps.PrintLine ("modifies " + (string_of_exp e) + ";")
    | SpecRaw (RawSpec ((RModifies _) as r, es)) ->
        ps.PrintLine (string_of_raw_spec_kind r);
        ps.Indent ();
        let es = exps_of_spec_exps es in
        let ses = List.map (fun (_, e) -> (string_of_exp e) + ";") es in
        ps.PrintLine (String.concat " " ses);
        ps.Unindent()
    | SpecRaw (RawSpec (r, es)) ->
        ps.PrintLine (string_of_raw_spec_kind r);
        ps.Indent ();
        List.iter (emit_spec_exp ps) es;
        ps.Unindent()
    | SpecRaw (Lets ls) ->
        ps.PrintLine "lets";
        ps.Indent ();
        emit_lets ps (List.map snd ls) [];
        ps.Unindent()
  with err -> raise (LocErr (loc, err))

let string_of_attr (x:id, es:exp list):string =
  "{:" + (sid x) + " " + (String.concat ", " (List.map string_of_exp es)) + "}"
let string_of_attrs (attrs:attrs):string = String.concat "" (List.map string_of_attr attrs)

let emit_fun (ps:print_state) (loc:loc) (f:fun_decl):unit =
  (if !reprint_blank_lines then ps.PrintLine (""));
  let sFun = "function" in
  ps.PrintLine (sFun + (string_of_attrs f.fattrs) + " " + (sid f.fname) + "(" + (string_of_formals f.fargs) + "):" + (string_of_typ f.fret));
  ( match f.fbody with
    | None -> ()
    | Some e ->
        ps.PrintLine "{";
        ps.Indent ();
        ps.PrintLine (string_of_exp e);
        ps.Unindent ();
        ps.PrintLine "}"
  )

let emit_proc (ps:print_state) (loc:loc) (p:proc_decl):unit =
  gen_lemma_sym_count := 0;
  (if !reprint_blank_lines then ps.PrintLine (""));
  let sAttrs = string_of_attrs p.pattrs in
  let sProc = string_of_ghost p.pghost + "procedure" in
  ps.PrintLine (sProc + sAttrs + " " + (sid p.pname) + "(" + (string_of_pformals p.pargs) + ")");
  ps.Indent ();
  (match p.prets with [] -> () | rs -> ps.PrintLine ("returns (" + (string_of_pformals rs) + ")"));
  List.iter (emit_spec ps) p.pspecs;
  ps.Unindent ();
  ( match p.pbody with
    | None -> ()
    | Some ss ->
        ps.PrintLine "{";
        ps.Indent ();
        emit_stmts ps ss;
        ps.Unindent ();
        ps.PrintLine "}"
  )

let emit_decl (ps:print_state) (loc:loc, d:decl):unit =
  try
    match d with
    | DVerbatim lines ->
        ps.PrintLine("#verbatim");
        List.iter ps.PrintUnbrokenLine lines;
        ps.PrintLine("#endverbatim")
    | DVar (x, t, XState e, attrs) ->
        ps.PrintLine ("var" + (string_of_attrs ((Id "state", [e])::attrs)) + " " + (sid x) + ":" + (string_of_typ t) + ";")
    | DVar (x, t, storage, attrs) ->
        ps.PrintLine ((string_of_var_storage storage) + "var" + (string_of_attrs attrs) + " " + (sid x) + ":" + (string_of_typ t) + ";")
    | DFun f -> emit_fun ps loc f
    | DProc p -> emit_proc ps loc p
  with err -> raise (LocErr (loc, err))

let emit_decls (ps:print_state) (ds:decls):unit =
  List.iter (emit_decl ps) ds

