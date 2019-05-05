module Emit_dafny_text

open Ast
open Ast_util
open Transform
open Emit_common_base
open Microsoft.FSharp.Math

let sid (x:id):string =
  match x with
  | Id s -> s
  | Reserved s -> qprefix "va_" s
  | Operator s -> internalErr ("custom operator " + s)

// Dafny precedences
let prec_of_bop (op:bop):(int * int * int) =
  match op with
  | BEquiv | BImply | BExply -> (10, 11, 11)
  | BAnd _ | BOr _ -> (15, 16, 16) // TODO
  | BLe | BGe | BLt | BGt | BIn -> (20, 20, 20)
  | BEq _ | BNe _ -> (25, 25, 26)
  | BAdd | BSub -> (30, 30, 31)
  | BMul | BDiv | BMod -> (40, 40, 41)
  | BOldAt | BCustom _ -> internalErr ("binary operator " + (sprintf "%A" op))

let string_of_bop (op:bop):string =
  match op with
  | BEquiv -> "<==>"
  | BImply -> "==>"
  | BExply -> "<=="
  | BAnd _ -> "&&"
  | BOr _ -> "||"
  | BEq _ -> "=="
  | BNe _ -> "!="
  | BLt -> "<"
  | BGt -> ">"
  | BLe -> "<="
  | BGe -> ">="
  | BIn -> "in"
  | BAdd -> "+"
  | BSub -> "-"
  | BMul -> "*"
  | BDiv -> "/"
  | BMod -> "%"
  | BOldAt | BCustom _ -> internalErr ("binary operator " + (sprintf "%A" op))

let string_of_ghost (g:ghost) = match g with Ghost -> "ghost " | NotGhost -> ""
let string_of_var_storage (g:var_storage) = match g with XGhost -> "ghost " | _ -> ""

let rec string_of_typ (t:typ):string =
  match t with
  | TName x -> sid x
  | TApply (x, ts) -> (sid x) + "<" + (String.concat ", " (List.map string_of_typ ts)) + ">"
  | TBool _ -> "bool"
  | TInt (b1, b2) -> "int"
  | TFun (ts, t) -> "(" + (String.concat ", " (List.map string_of_typ ts)) + ") " + (string_of_typ t)
  | TTuple ts -> "(" + (String.concat ", " (List.map string_of_typ ts)) + ")"
  | TDependent x -> sid x
  | TVar _ -> internalErr "string_of_typ: TVar"

let rec string_of_exp_prec prec e =
  let r = string_of_exp_prec in
  let (s, ePrec) =
    let qbind q xs ts e = (q + " " + (string_of_formals xs) + (string_of_triggers ts) + " :: " + (r 5 e), 6) in
    match e with
    | ELoc (loc, ee) -> try (r prec ee, prec) with err -> raise (LocErr (loc, err))
    | EVar (x, _) -> (sid x, 99)
    | EInt i -> (string i, 99)
    | EReal r -> (r, 99)
    | EBitVector (n, i) -> ("bv" + (string n) + "(" + (string i) + ")", 99)
    | EBool true -> ("true", 99)
    | EBool false -> ("false", 99)
    | EString s -> ("\"" + s + "\"", 99)
    | EOp (Uop UReveal, [EVar (x, _)], _) -> ("reveal_" + (sid x) + "()", 99)
    | EOp (Uop (UNot _), [e], _) -> ("!" + (r 99 e), 90)
    | EOp (Uop UNeg, [e], _) -> ("-" + (r 99 e), 0)
    | EOp (Uop (UIs x), [e], _) -> ((r 90 e) + "." + (sid x) + "?", 0)
    | EOp (Uop (UReveal | UOld | UConst | UGhostOnly | UToOperand | UCustom _), [_], _) -> internalErr ("unary operator " + (sprintf "%A" e))
    | EOp (Uop _, ([] | (_::_::_)), _) -> internalErr ("unary operator " + (sprintf "%A" e))
    | EOp (Bop op, [e1; e2], _) ->
        let (pe, p1, p2) = prec_of_bop op in
        ((r p1 e1) + " " + (string_of_bop op) + " " + (r p2 e2), pe)
    | EOp (Bop _, ([] | [_] | (_::_::_::_)), _) -> internalErr ("binary operator " + (sprintf "%A" e))
    | EOp (TupleOp _, es, _) -> ("(" + (String.concat ", " (List.map (r 5) es)) + ")", 90)
    | EApply (e, _, es, _) when is_id e && id_of_exp e = (Id "seq") -> ("[" + (String.concat ", " (List.map (r 5) es)) + "]", 90)
    | EApply (e, _, es, _)  when is_id e && id_of_exp e = (Id "set") -> ("{" + (String.concat ", " (List.map (r 5) es)) + "}", 90)
    | EOp (Subscript, [e1; e2], _) -> ((r 90 e1) + "[" + (r 90 e2) + "]", 90)
    | EOp (Update, [e1; e2; e3], _) -> ((r 90 e1) + "[" + (r 90 e2) + " := " + (r 90 e3) + "]", 90)
    | EOp (Cond, [e1; e2; e3], _) -> ("if " + (r 90 e1) + " then " + (r 90 e2) + " else " + (r 90 e3), 0)
    | EOp (FieldOp x, [e], _) -> ((r 90 e) + "." + (sid x), 90)
    | EOp (FieldUpdate x, [e1; e2], _) -> ((r 90 e1) + ".(" + (sid x) + " := " + (r 90 e2) + ")", 90)
    | EOp ((Subscript | Update | Cond | FieldOp _ | FieldUpdate _ | CodeLemmaOp | RefineOp | StateOp _ | OperandArg _), _, _) -> internalErr ("EOp " + (sprintf "%A" e))
    | EApply (e, _, es, _) -> ((r 90 e) + "(" + (String.concat ", " (List.map (r 5) es)) + ")", 90)
    | EBind (Forall, [], xs, ts, e, _) -> qbind "forall" xs ts e
    | EBind (Exists, [], xs, ts, e, _) -> qbind "exists" xs ts e
    | EBind (Lambda, [], xs, _, e, _) -> ("(" + (string_of_formals xs) + " => " + (r 5 e) + ")", 90)
    | EBind (BindLet, [ex], [x], [], e, _) -> ("var " + (string_of_formal x) + " := " + (r 5 ex) + "; " + (r 5 e), 6)
    | EBind (BindAlias, _, _, _, e, _) -> (r prec e, prec)
    | EBind (BindSet, [], xs, ts, e, _) -> ("iset " + (string_of_formals xs) + (string_of_triggers ts) + " | " + (r 5 e), 6)
    | EBind ((Forall | Exists | Lambda | BindLet | BindSet), _, _, _, _, _) -> internalErr ("EBind " + (sprintf "%A" e))
    | ECast (e, _) -> (r prec e, 0)
    | ELabel (l, e) -> (r prec e, prec)
    | _ -> internalErr (sprintf "unexpected exp %A " e)
  in if prec <= ePrec then s else "(" + s + ")"
and string_of_formal (x:id, t:typ option) = (sid x) + (match t with None -> "" | Some t -> ":" + (string_of_typ t))
and string_of_formals (xs:formal list):string = String.concat ", " (List.map string_of_formal xs)
and string_of_pformal (x:id, t:typ, g:var_storage, _, _) = (sid x) + ":" + (string_of_typ t)
and string_of_pformals (xs:pformal list):string = String.concat ", " (List.map string_of_pformal xs)
and string_of_trigger (es:exp list):string = "{:trigger " + (string_of_exps es) + "}"
and string_of_triggers (ts:exp list list):string = String.concat " " (List.map string_of_trigger ts)
and string_of_exp (e:exp):string = string_of_exp_prec 5 e
and string_of_exps (es:exp list):string = String.concat ", " (List.map string_of_exp es)
and string_of_exps_tail (es:exp list):string = String.concat "" (List.map (fun e -> ", " + string_of_exp e) es)
and string_of_args (es:exp list):string = "(" + String.concat ", " (List.map string_of_exp es) + ")"

let string_of_lhs_formal ((x, tOpt):lhs):string = (sid x) + (match tOpt with Some (Some t, _) -> ":" + (string_of_typ t) | _ -> "")

let rec emit_stmt (ps:print_state) (s:stmt):unit =
  match s with
  | SLoc (loc, s) -> try ps.cur_loc := loc; emit_stmt ps s with err -> raise (LocErr (loc, err))
  | SLabel _ -> err "unsupported feature: labels (unstructured code)"
  | SGoto _ -> err "unsupported feature: 'goto' (unstructured code)"
  | SReturn _ -> err "unsupported feature: 'return' (unstructured code)"
  | SAssume e -> ps.PrintLine ("assume " + (string_of_exp e) + ";")
  | SAssert (attrs, e) ->
      let sSplit = if attrs.is_split then "{:split_here}" else "" in
      ps.PrintLine ("assert" + sSplit + " " + (string_of_exp e) + ";" + "  // " + (string_of_loc !ps.cur_loc))
  | SCalc (op, contents, e) ->
      ps.PrintLine ("calc " + string_of_bop op + " {");  
      ps.Indent();
      List.iter (fun {calc_exp = e; calc_op = op; calc_hints = hints} ->
        ps.PrintLine ((string_of_exp e) + ";");
        ps.Unindent(); ps.PrintLine(string_of_bop op); ps.Indent();
        List.iter (emit_block ps) hints
      ) contents;
      ps.PrintLine((string_of_exp e) + ";")
      ps.Unindent();
      ps.PrintLine("}")
  | SVar (x, tOpt, _, g, a, eOpt) ->
      let st = match tOpt with None -> "" | Some t -> ":" + (string_of_typ t) in
      let rhs = match eOpt with None -> "" | Some e -> " := " + (string_of_exp e) in
      ps.PrintLine ((string_of_var_storage g) + "var " + (sid x) + st + rhs + ";")
  | SAlias _ -> internalErr "SAlias"
  | SAssign ([], e) -> ps.PrintLine ((string_of_exp e) + ";")
  | SAssign (lhss, e) when List.forall (fun (x, d) -> d = None) lhss ->
      ps.PrintLine ((String.concat ", " (List.map (fun (x, _) -> sid x) lhss)) + " := " + (string_of_exp e) + ";")
  | SAssign (lhss, e) when List.forall (fun (x, d) -> d <> None) lhss ->
      ps.PrintLine ("ghost var " + (String.concat ", " (List.map string_of_lhs_formal lhss)) + " := " + (string_of_exp e) + ";")
  | SAssign _ -> emit_stmts ps (eliminate_assign_lhss s)
  | SLetUpdates _ -> internalErr "SLetUpdates"
  | SBlock ss -> notImplemented "block"
  | SQuickBlock _ -> internalErr "quick_block"
  | SIfElse (_, e, ss1, []) ->
      ps.PrintLine ("if (" + (string_of_exp e) + ")");
      emit_block ps ss1
  | SIfElse (_, e, ss1, ss2) ->
      ps.PrintLine ("if (" + (string_of_exp e) + ")");
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
      (match skip_loc ex with EBool true | ECast (EBool true, _) -> () | _ -> ps.PrintLine ("| " + (string_of_exp ex)));
      ps.PrintLine ("ensures " + (string_of_exp e));
      ps.Unindent ();
      emit_block ps ss;
  | SExists (xs, ts, e) ->
      ps.PrintLine ("ghost var " + (string_of_formals xs) + (string_of_triggers ts) + " :| " + (string_of_exp e) + ";")
and emit_stmts (ps:print_state) (stmts:stmt list) = List.iter (emit_stmt ps) stmts
and emit_block (ps:print_state) (stmts:stmt list) =
  ps.PrintLine "{";
  ps.Indent ();
  emit_stmts ps stmts;
  ps.Unindent ();
  ps.PrintLine "}"

let emit_spec (ps:print_state) (loc:loc, s:spec):unit =
  try
    match s with
    | Requires (_, e) -> ps.PrintLine ("requires " + (string_of_exp e))
    | Ensures (_, e) -> ps.PrintLine ("ensures  " + (string_of_exp e))
    | Modifies _ -> ()
    | SpecRaw _ -> internalErr "SpecRaw"
  with err -> raise (LocErr (loc, err))

let emit_fun (ps:print_state) (loc:loc) (f:fun_decl):unit =
  ps.PrintLine ("");
  let sFun = match f.fghost with Ghost -> "function" | NotGhost -> "function method" in
  let sAttr (x, es) =
    match (x, es) with
    | (Id "opaque", ([] | [EBool true])) -> "{:opaque}"
    | _ -> err ("unknown function attribute " + (sid x) + " on function " + (sid f.fname))
    in
  let sAttrs = List.map sAttr f.fattrs in
  ps.PrintLine (sFun + (String.concat "" sAttrs) + " " + (sid f.fname) + "(" + (string_of_formals f.fargs) + "):" + (string_of_typ f.fret));
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
  ps.PrintLine ("");
  let sAttr (x, es) = "{:" + (err_id x) + " " + (String.concat ", " (List.map string_of_exp es)) + "}" in
  let sAttrs = String.concat "" (List.map sAttr p.pattrs) in
  let sProc = match p.pghost with Ghost -> "lemma" | NotGhost -> "method" in
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
    | DVerbatim (_, lines) -> List.iter ps.PrintUnbrokenLine lines
    | DPragma _ -> ()
    | DVar _ -> ()
    | DFun f -> emit_fun ps loc f
    | DProc p -> emit_proc ps loc p
    | DConst _ -> ()
    | DType _ -> ()
    | DOperandType _ -> ()
    | DUnsupported _ -> ()
  with err -> raise (LocErr (loc, err))

let emit_decls (ps:print_state) (ds:decls):unit =
  List.iter (emit_decl ps) ds

