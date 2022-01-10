module Emit_vale_text

open System
open Ast
open Ast_util
open Parse_util
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
  | BOr _ -> (16, 16, 17)
  | BAnd _ -> (18, 18, 19)
  | BEq _ | BNe _ -> (20, 20, 21)
  | BLe | BGe | BLt | BGt -> (25, 25, 25)
  | BAdd | BSub -> (30, 30, 31)
  | BMul | BDiv | BMod -> (40, 40, 41)
  | BIn | BOldAt | BCustom _ -> internalErr ("binary operator")

let string_of_bop (op:bop):string =
  match op with
  | BEquiv -> "<==>"
  | BImply -> "==>"
  | BExply -> "<=="
  | BAnd _ -> "&&"
  | BOr _ -> "||"
  | BEq BpBool -> "="
  | BEq BpProp -> "=="
  | BNe BpBool -> "<>"
  | BNe BpProp -> "!="
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

let string_of_kind (k:kind):string =
  match k with
  | KType i -> "Type(" + string i + ")"
  | KDependent i -> "Dependent(" + string i + ")"

let rec string_of_typ_prec (prec:int) (t:typ):string =
  let r = string_of_typ_prec in
  let s_bnd (b:bnd):string =
    match b with
    | Int i when i < bigint.Zero -> "(" + string i + ")"
    | Int i -> string i
    | NegInf | Inf -> "_"
    in
  let (s, tPrec) =
    match t with
    | TName x -> (sid x, 20)
    | TApply (x, ts) -> (sid x + "(" + (String.concat ", " (List.map (r 0) ts)) + ")", 10)
    | TBool BpBool -> ("bool", 99)
    | TBool BpProp -> ("prop", 99)
    | TInt (NegInf, Inf) -> ("int", 0)
    | TInt (b1, b2) -> ("int_range(" + s_bnd b1 + ", " + s_bnd b2 + ")", 0)
    | TTuple ts -> ("tuple(" + (String.concat ", " (List.map (r 0) ts)) + ")", 10)
    | TFun (ts, t) -> ("fun(" + (String.concat ", " (List.map (r 0) ts)) + ") -> " + (r 0 t), 0)
    | TDependent x -> ("dependent(" + sid x + ")", 10)
    | TVar (x, _) -> (sid x, 20)
  in if prec <= tPrec then s else "(" + s + ")"
let string_of_typ (t:typ):string = string_of_typ_prec 0 t

let rec string_of_exp_prec (prec:int) (e:exp):string =
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
    | EOp (Uop UReveal, [EVar (x, _)], _) -> ("reveal " + (sid x) + "()", 99)
    | EOp (Uop (UNot _), [e], _) -> ("!" + (r 99 e), 90)
    | EOp (Uop UNeg, [e], _) -> ("-" + (r 99 e), 0)
    | EOp (Uop (UIs x), [e], _) -> ((r 90 e) + " is " + (sid x), 90)
    | EOp (Uop UToOperand, [e], _) -> ("@" + (r 99 e), 90)
    | EOp (Uop UOld, [e], _) -> ("old(" + (r 99 e) + ")", 90)
    | EOp (Uop UConst, [e], _) -> ("const(" + (r 99 e) + ")", 90)
    | EOp (Uop (UReveal | UGhostOnly | UCustom _), [_], _) -> internalErr (sprintf "unary operator:%A" e)
    | EOp (Uop _, ([] | (_::_::_)), _) -> internalErr "unary operator"
    | EOp (Bop BIn, [e1; e2], _) ->
        ((r 90 e1) + "?[" + (r 5 e2) + "]", 90)
    | EOp (Bop BOldAt, [e1; e2], _) ->
        ("old[" + (r 5 e1) + "](" + (r 5 e2) + ")", 90)
    | EOp (Bop op, [e1; e2], _) ->
        let (pe, p1, p2) = prec_of_bop op in
        ((r p1 e1) + " " + (string_of_bop op) + " " + (r p2 e2), pe)
    | EOp (Bop _, ([] | [_] | (_::_::_::_)), _) -> internalErr "binary operator"
    | EOp (Subscript, [e1; e2], _) -> ((r 90 e1) + "[" + (r 90 e2) + "]", 90)
    | EOp (Update, [e1; e2; e3], _) -> ((r 90 e1) + "[" + (r 90 e2) + " := " + (r 90 e3) + "]", 90)

    | EOp (Slice, [e1; e2; e3], _) -> ((r 90 e1) + "[" + (r 90 e2) + " .. " + (r 90 e3) + "]", 90)
    | EOp (SlicePrefix, [e1; e2], _) -> ((r 90 e1) + "[" + " .. " + (r 90 e2) + "]", 90)
    | EOp (SliceSuffix, [e1; e2], _) -> ((r 90 e1) + "[" + (r 90 e2) + " .. " + "]", 90)

    | EOp (Cond, [e1; e2; e3], _) -> ("if " + (r 90 e1) + " then " + (r 90 e2) + " else " + (r 90 e3), 0)
    | EOp (FieldOp x, [e], _) -> ((r 90 e) + "." + (sid x), 90)
    | EOp (FieldUpdate x, [e1; e2], _) -> ((r 90 e1) + ".(" + (sid x) + " := " + (r 90 e2) + ")", 90)
    | EOp ((Subscript | Update | Cond | FieldOp _ | FieldUpdate _ | CodeLemmaOp | RefineOp | StateOp _ | OperandArg _), _, _) -> internalErr (sprintf "EOp:%A" e)
    | EApply (e, None, es, _) -> ((r 90 e) + "(" + (String.concat ", " (List.map (r 5) es)) + ")", 90)
    | EApply (e, Some ts, es, _) ->
        ((r 90 e) + "#[" + String.concat ", " (List.map string_of_typ (List.map snd ts)) + "]("
          + String.concat ", " (List.map (r 5) es) + ")", 90)
    | EBind (Forall, [], xs, ts, e, _) -> qbind "forall" xs ts e
    | EBind (Exists, [], xs, ts, e, _) -> qbind "exists" xs ts e
    | EBind (Lambda, [], xs, _, e, _) -> ("(" + (string_of_formals xs) + " => " + (r 5 e) + ")", 90)
    | EBind (BindLet, [ex], [x], [], e, _) -> ("let " + (string_of_formal x) + " := " + (r 5 ex) + " in " + (r 5 e), 6)
    | EBind (BindSet, [], xs, ts, e, _) -> ("iset " + (string_of_formals xs) + (string_of_triggers ts) + " | " + (r 5 e), 6)
    | EBind ((Forall | Exists | Lambda | BindLet | BindAlias | BindSet), _, _, _, _, _) -> internalErr "EBind"
    | ECast (_, e, t) -> ("#" + string_of_typ_prec 20 t + "(" + r 5 e + ")", 90)
    | ELabel (l, e) -> (r prec e, prec)
    | _ -> internalErr (sprintf "unexpected exp %A " e)
  in if prec <= ePrec then s else "(" + s + ")"
and string_of_ghost (g:ghost) = match g with Ghost -> "ghost " | NotGhost -> ""
and string_of_stmt_modifier (sm:stmt_modifier) = match sm with SmPlain -> "" | SmGhost -> "ghost " | SmInline -> "inline "
and string_of_var_storage (g:var_storage) =
  match g with
  | XGhost -> "ghost "
  | XPhysical -> ""
  | XOperand -> ""
  | XInline -> "inline "
  | XAlias _ -> "{:alias}" // TODO
  | XState e -> "{:state" + (string_of_exp_prec 5 e) + "}"
and string_of_formal (x:id, t:typ option) = (sid x) + (match t with None -> "" | Some t -> ":" + (string_of_typ t))
and string_of_formals (xs:formal list):string = String.concat ", " (List.map string_of_formal xs)

and string_of_pformal (x:id, t:typ, g:var_storage, _, _) = (string_of_var_storage g) + (sid x) + ":" + (string_of_typ t)
and ast_of_pformal (x:id, t:typ, g:var_storage, _, _) = ("{'storage':'" + string_of_var_storage g) + "','name':'" + (sid x) + "','type':'" + (string_of_typ t) + "'}"

and string_of_pformals (xs:pformal list):string = String.concat ", " (List.map string_of_pformal xs)
and ast_of_pformals (xs:pformal list):string = String.concat ", " (List.map ast_of_pformal xs)

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
      ps.PrintLine (sAssert + sSplit + " " + (string_of_exp e) + ";")
  | SCalc (op, contents, e) ->
      ps.PrintLine ("calc " +  string_of_bop op  + " {");
      ps.Indent();
      List.iter (fun {calc_exp = e; calc_op = op; calc_hints = hints} ->
        ps.PrintLine ((string_of_exp e) + ";");
        ps.Unindent(); ps.PrintLine(string_of_bop op); ps.Indent();
        List.iter (emit_block ps) hints
      ) contents;
      ps.PrintLine((string_of_exp e) + ";")
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
  | SAssign ([], e) -> ps.PrintLine ((string_of_exp e) + ";")
  | SAssign (lhss, e) ->
      ps.PrintLine ((String.concat ", " (List.map string_of_lhs_formal lhss)) + " := " + (string_of_exp e) + ";")
  | SLetUpdates _ -> internalErr "SLetUpdates"
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

let rec dump_exp_ast (e:exp): string =
  let r = dump_exp_ast in
  match e with
  | ELoc (loc, ee) -> try (r ee) with err -> raise (LocErr (loc, err))
  | EOp (op, es, _) -> 
      String.Format("{{'ntype':'EOp', 'op':'{0}', 'es':{1}}}", op, dump_exps_ast es)
  | EVar (var, _) ->
    String.Format("{{'ntype':'EVar', 'name':'{0}'}}", (sid var))
  | EInt (value) -> 
    String.Format("{{'ntype':'EInt', 'value':'{0}'}}", value)
  | EApply (e, _, es, _) ->
    String.Format("{{'ntype':'EApply', 'fun':{0}, 'formals':{1}}}", (dump_exp_ast e), dump_exps_ast es)
  | ECast (_, e, _) ->
      String.Format("{{'ntype':'ECast', 'exp':{0}}}", (dump_exp_ast e))
  | _ ->  failwith (String.Format("unhandled {0}", e))
and dump_exps_ast (es:exp list) = "[" + String.concat "," (List.map dump_exp_ast es) + "]"

let rec dump_stmt_ast (s:stmt):string =
  match s with
    | SLoc (loc, s) -> try dump_stmt_ast s with err -> raise (LocErr (loc, err))
    | SAssign ([], e) -> dump_exp_ast e
    // ps.PrintLine ((string_of_exp e) + ";")
    // | SAssign (lhss, e) ->
    //     ps.PrintLine ((String.concat ", " (List.map string_of_lhs_formal lhss)) + " := " + (string_of_exp e) + ";")
    | _ -> failwith (String.Format("unhandled {0}", s.GetType()))
and dump_stmts_ast (stmts:stmt list) = "[" + String.concat "," (List.map dump_stmt_ast stmts) + "]"

let string_of_raw_spec_kind (r:raw_spec_kind) =
  match r with
  | RRequires r -> "requires"
  | REnsures r -> "ensures"
  | RRequiresEnsures -> "requires/ensures"
  | RModifies Read -> "reads"
  | RModifies Modify -> "modifies"
  | RModifies Preserve -> "preserves"

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
    // | Requires (r, e) ->
    //     ps.PrintLine ("requires" + " " + (string_of_exp e) + ";")
    // | Ensures (r, e) ->
    //     ps.PrintLine ("ensures" + "  " + (string_of_exp e) + ";")
    // | Modifies (Read, e) -> ps.PrintLine ("reads " + (string_of_exp e) + ";")
    // | Modifies (Modify, e) -> ps.PrintLine ("modifies " + (string_of_exp e) + ";")
    // | Modifies (Preserve, e) -> ps.PrintLine ("preserves " + (string_of_exp e) + ";")
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
    | _ -> failwith (String.Format("unhandled {0}", s.GetType()))
    // | SpecRaw (Lets ls) ->
    //     ps.PrintLine "lets";
    //     ps.Indent ();
    //     emit_lets ps (List.map snd ls) [];
    //     ps.Unindent()

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

let map_requires (p: loc * spec):(loc * spec_exp) list = 
  let (_, s) = p in 
  match s with
  | SpecRaw (RawSpec (r, es)) ->
    match r with
    | RRequires (_) -> es
    | REnsures (_) -> []
    | RRequiresEnsures -> failwith "requires/ensures"
    | RModifies (kind) ->  []
  | _ -> failwith "unhandled spec"

let dump_spec (p: loc * spec_exp): string =
  let (_, s) = p in 
  match s with
  | SpecExp e -> dump_exp_ast e
  | SpecLet _ -> failwith "unhandled spec"

let emit_proc (ps:print_state) (loc:loc) (p:proc_decl):unit =
  gen_lemma_sym_count := 0;
  (if !reprint_blank_lines then ps.PrintLine (""));
  let sAttrs = string_of_attrs p.pattrs in
  let sProc = string_of_ghost p.pghost + "procedure" in
  ps.DumpAST("{'ntype':'proc','name':'" + sid p.pname + "',");
  ps.DumpAST("'formals':[" + (ast_of_pformals p.pargs) + "],");
  ps.PrintLine (sProc + sAttrs + " " + (sid p.pname) + "(" + (string_of_pformals p.pargs) + ")");
  ps.Indent ();
  assert (p.prets = []);
  (match p.prets with [] -> () | rs -> ps.PrintLine ("returns (" + (string_of_pformals rs) + ")"));
  List.iter (emit_spec ps) p.pspecs;

  let reqs = List.concat (List.map map_requires p.pspecs);
  ps.DumpAST("'requires':[")
  ps.DumpAST(String.concat "," (List.map dump_spec reqs));
  ps.DumpAST("],");

  ps.Unindent ();
  ( match p.pbody with
    | None -> ()
    | Some ss ->
        ps.PrintLine "{";
        ps.Indent ();
        emit_stmts ps ss;
        ps.DumpAST("'body':" + (dump_stmts_ast ss));
        ps.Unindent ();
        ps.PrintLine "}"
  )
  ps.DumpAST("}")

let emit_decl (ps:print_state) (loc:loc, d:decl):unit =
  try
    match d with
    | DPragma (ModuleName s) ->
        ps.PrintLine ("module " + s);
    | DPragma (PushOptions _) -> ()
    | DVerbatim (attrs, lines) ->
        ps.PrintLine("#verbatim" + (string_of_attrs attrs));
        List.iter ps.PrintUnbrokenLine lines;
        ps.PrintLine("#endverbatim")
    | DVar (x, t, XState e, attrs) ->
        ps.PrintLine ("var" + (string_of_attrs ((Id "state", [e])::attrs)) + " " + (sid x) + ":" + (string_of_typ t) + ";")
    | DVar (x, t, storage, attrs) ->
        ps.PrintLine ((string_of_var_storage storage) + "var" + (string_of_attrs attrs) + " " + (sid x) + ":" + (string_of_typ t) + ";")
    | DFun f -> emit_fun ps loc f
    | DProc p -> emit_proc ps loc p
    | DConst _ -> ()
    | DType _ -> ()
    | DOperandType _ -> ()
    | DUnsupported _ -> ()
  with err -> raise (LocErr (loc, err))

let emit_decls (ps:print_state) (ds:decls):unit =
  List.iter (emit_decl ps) ds

