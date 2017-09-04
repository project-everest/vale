module Emit_fstar_text

open Ast
open Ast_util
open Transform
open Emit_common
open Microsoft.FSharp.Math

let sid (x:id):string =
  match x with
  | Id s -> s
  | Reserved s -> qprefix "va_" s
  | Operator s -> internalErr "custom operator"

// non-associative: (n, n+1, n+1)
// left-associative: (n, n, n+1)
// right-associative: (n, n+1, n)
let prec_of_bop (op:bop):(int * int * int) =
  match op with
  | BEquiv -> (10, 11, 11)
  | BImply -> (12, 13, 12)
  | BExply -> notImplemented "<=="
  | BOr -> (16, 16, 17)
  | BAnd -> (18, 18, 19)
  | BLe | BGe | BLt | BGt | BEq | BNe -> (20, 20, 21)
  | BAdd -> (30, 31, 30)
  | BSub -> (35, 35, 36)
  | BMul | BDiv | BMod -> (40, 41, 40)
  | BOldAt | BIn | BCustom _ -> internalErr ("binary operator")

let string_of_bop (op:bop):string =
  match op with
  | BEquiv -> "<==>"
  | BImply -> "==>"
  | BExply -> notImplemented "<=="
  | BOr -> "\\/"
  | BAnd -> "/\\"
  | BEq -> "=="
  | BNe -> "=!="
  | BLt -> "<"
  | BGt -> ">"
  | BLe -> "<="
  | BGe -> ">="
  | BAdd -> "+"
  | BSub -> "-"
  | BMul -> "`op_Multiply`"
  | BDiv -> "`op_Division`"
  | BMod -> "`op_Modulus`"
  | BOldAt | BIn | BCustom _ -> internalErr "binary operator"

let string_of_ghost (g:ghost) = ""
let string_of_var_storage (g:var_storage) = ""

let rec string_of_typ (t:typ):string =
  match t with
  | TName x -> sid x
  | TApp (TName (Id "tuple"), ts) -> "(" + (String.concat " * " (List.map string_of_typ ts)) + ")"
  | TApp (t, ts) -> "(" + (string_of_typ t) + " " + (String.concat " " (List.map string_of_typ ts)) + ")"

let rec string_of_exp_prec prec e =
  let r = string_of_exp_prec in
  let (s, ePrec) =
    let qbind q qsep xs ts e = (q + " " + (string_of_formals xs) + (string_of_triggers ts) + qsep + (r 5 e), 6) in
    match e with
    | ELoc (loc, ee) -> try (r prec ee, prec) with err -> raise (LocErr (loc, err))
    | EVar x -> (sid x, 99)
    | EInt i -> (string i, 99)
    | EReal r -> (r, 99)
    | EBitVector (n, i) -> ("bv" + (string n) + "(" + (string i) + ")", 99)
    | EBool true -> ("True", 99)
    | EBool false -> ("False", 99)
    | EString s -> ("\"" + s + "\"", 99)
    | EOp (Uop UReveal, [EVar x]) -> ("()", 90) // TODO
    | EOp (Uop UNot, [e]) -> ("~" + (r 99 e), 90)
    | EOp (Uop UNeg, [e]) -> ("-" + (r 99 e), 0)
    | EOp (Uop (UIs x), [e]) -> ((r 90 e) + "." + (sid x) + "?", 0)
    | EOp (Uop (UReveal | UOld | UConst | UGhostOnly | UToOperand | UCustom _ | UCustomAssign _), [_]) -> internalErr "unary operator"
    | EOp (Uop _, ([] | (_::_::_))) -> internalErr "unary operator"
    | EOp (Bop op, [e1; e2]) ->
        let (pe, p1, p2) = prec_of_bop op in
        ((r p1 e1) + " " + (string_of_bop op) + " " + (r p2 e2), pe)
    | EOp (Bop _, ([] | [_] | (_::_::_::_))) -> internalErr "binary operator"
    | EApply (Id "tuple", es) -> ("(" + (String.concat ", " (List.map (r 5) es)) + ")", 90)
    | EApply (Id "list", es) -> ("[" + (String.concat "; " (List.map (r 5) es)) + "]", 90)
//    | EOp (MultiOp MSet, es) -> notImplemented "MSet"
    | EOp (Subscript, [e1; e2]) -> (r prec (vaApp "subscript" [e1; e2]), prec)
    | EOp (Update, [e1; e2; e3]) -> (r prec (vaApp "update" [e1; e2; e3]), prec)
    | EOp (Cond, [e1; e2; e3]) -> ("if " + (r 90 e1) + " then " + (r 90 e2) + " else " + (r 90 e3), 0)
    | EOp (FieldOp x, [e]) -> ((r 90 e) + "." + (sid x), 90)
    | EOp (FieldUpdate x, [e1; e2]) -> ("{" + (r 90 e1) + " with " + (sid x) + " = " + (r 90 e2) + "}", 90)
    | EOp ((Subscript | Update | Cond | FieldOp _ | FieldUpdate _ | CodeLemmaOp | RefineOp | StateOp _ | OperandArg _), _) -> internalErr "EOp"
    | EApply (x, es) -> ("(" + (sid x) + " " + (string_of_args es) + ")", 90)
    | EBind (Forall, [], xs, ts, e) -> qbind "forall" " . " xs ts e
    | EBind (Exists, [], xs, ts, e) -> qbind "exists" " . " xs ts e
    | EBind (Lambda, [], xs, ts, e) -> qbind "fun" " -> " xs ts e
    | EBind (BindLet, [ex], [x], [], e) -> ("let " + (string_of_formal x) + " = " + (r 5 ex) + " in " + (r 5 e), 6)
    | EBind (BindAlias, _, _, _, e) -> (r prec e, prec)
    | EBind (BindSet, [], xs, ts, e) -> notImplemented "iset"
    | EBind ((Forall | Exists | Lambda | BindLet | BindSet), _, _, _, _) -> internalErr "EBind"
  in if prec <= ePrec then s else "(" + s + ")"
and string_of_formal (x:id, t:typ option) = match t with None -> sid x | Some t -> "(" + (sid x) + ":" + (string_of_typ t) + ")"
and string_of_formals (xs:formal list):string = String.concat " " (List.map string_of_formal xs)
and string_of_formal_bare (x:id, t:typ option) = match t with None -> sid x | Some t -> (sid x) + ":" + (string_of_typ t)
and string_of_pformal (x:id, t:typ, _, _, _) = string_of_formal (x, Some t)
and string_of_pformals (xs:pformal list):string = String.concat " " (List.map string_of_pformal xs)
and string_of_trigger (es:exp list):string = "" // TODO
and string_of_triggers (ts:exp list list):string = "" // TODO
and string_of_exp (e:exp):string = string_of_exp_prec 90 e
and string_of_exps (es:exp list):string = String.concat " " (List.map string_of_exp es)
and string_of_exps_tail (es:exp list):string = String.concat "" (List.map (fun e -> " " + string_of_exp e) es)
and string_of_args (es:exp list):string = match es with [] -> "()" | _ -> string_of_exps es

let string_of_lhs_formal ((x, tOpt):lhs):string = match tOpt with Some (t, _) -> string_of_formal (x, t) | _ -> sid x

let rec emit_stmt (ps:print_state) (s:stmt):unit =
  match s with
  | SLoc (loc, s) -> try emit_stmt ps s with err -> raise (LocErr (loc, err))
  | SLabel _ -> err "unsupported feature: labels (unstructured code)"
  | SGoto _ -> err "unsupported feature: 'goto' (unstructured code)"
  | SReturn _ -> err "unsupported feature: 'return' (unstructured code)"
  | SAssume e -> ps.PrintLine ("assume " + (string_of_exp e) + ";")
  | SAssert (_, e) -> ps.PrintLine ("assert " + (string_of_exp e) + ";")
  | SCalc _ -> err "unsupported feature: 'calc' for F*"
  | SVar (x, tOpt, _, g, a, eOpt) ->
      let sf = string_of_formal (x, tOpt) in
      let rhs = match eOpt with Some e -> " = " + (string_of_exp e) | None -> err "right-hand side required in variable declaration" in
      ps.PrintLine ((string_of_var_storage g) + "let " + sf + rhs + " in")
  | SAlias _ -> internalErr "SAlias"
  | SAssign ([], e) -> ps.PrintLine ((string_of_exp e) + ";")
  | SAssign ([lhs], e) ->
      ps.PrintLine ("let " + (string_of_lhs_formal lhs) + " = " + (string_of_exp e) + " in")
  | SAssign ((_::_::_) as lhss, e) ->
      ps.PrintLine ("let (" + (String.concat ", " (List.map string_of_lhs_formal lhss)) + ") = " + (string_of_exp e) + " in")
  | SBlock ss -> notImplemented "block"
  | SIfElse (_, e, ss1, ss2) -> notImplemented "if-else"
  | SWhile (e, invs, (_, ed), ss) -> notImplemented "while"
  | SForall ([], [], EBool true, e, ss) ->
      // TODO
      ps.PrintLine "(";
      ps.Indent ();
      emit_stmts ps ss;
      ps.PrintLine ("assert " + (string_of_exp e) + ";");
      ps.Unindent ();
      ps.PrintLine ");";
      ps.PrintLine ("assume " + (string_of_exp e) + ";");
  | SForall (xs, ts, ex, e, ss) -> notImplemented "forall statements"
  | SExists (xs, ts, e) -> notImplemented "exists statements"
and emit_stmts (ps:print_state) (stmts:stmt list) = List.iter (emit_stmt ps) stmts
and emit_block (ps:print_state) (stmts:stmt list) =
  ps.PrintLine "(";
  ps.Indent ();
  emit_stmts ps stmts;
  ps.Unindent ();
  ps.PrintLine ");"

let collect_spec (loc:loc, s:spec):(exp list * exp list) =
  try
    match s with
    | Requires (_, e) -> ([e], [])
    | Ensures (_, e) -> ([], [e])
    | Modifies _ -> ([], [])
    | SpecRaw _ -> internalErr "SpecRaw"
  with err -> raise (LocErr (loc, err))

let collect_specs (ss:(loc * spec) list):(exp list * exp list) =
  let (rs, es) = List.unzip (List.map collect_spec ss) in
  (List.concat rs, List.concat es)

let val_string_of_formals (xs:formal list) =
  match xs with
  | [] -> (sid (Reserved "dummy")) + ":unit"
  | _ -> String.concat " -> " (List.map string_of_formal_bare xs)

let let_string_of_formals (useTypes:bool) (xs:formal list) =
  match xs with
  | [] -> "()"
  | _ -> string_of_formals (List.map (fun (x, t) -> (x, if useTypes then t else None)) xs)

let emit_fun (ps:print_state) (loc:loc) (f:fun_decl):unit =
  ps.PrintLine ("");
  let sg = match f.fghost with Ghost -> "GTot" | NotGhost -> "Tot" in
  ps.PrintLine ("val " + (sid f.fname) + " : " + (val_string_of_formals f.fargs) + " -> " + sg + " " + (string_of_typ f.fret));
  // TODO: opaque
  ( match f.fbody with
    | None -> ()
    | Some e ->
        ps.PrintLine ("let " + (sid f.fname) + " " + (let_string_of_formals false f.fargs) + " =");
        ps.Indent ();
        ps.PrintLine (string_of_exp e);
        ps.Unindent ()
  )

let emit_proc (ps:print_state) (loc:loc) (p:proc_decl):unit =
  gen_lemma_sym_count := 0;
  let (rs, es) = collect_specs p.pspecs in
  let (rs, es) = (exp_of_conjuncts rs, exp_of_conjuncts es) in
  ps.PrintLine ("");
  let tactic = match p.pbody with None -> None | Some _ -> attrs_get_exp_opt (Id "tactic") p.pattrs in
  let args = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.pargs in
  let printPType s =
    ps.Indent ();
    let st = String.concat " * " (List.map string_of_pformal p.prets) in
    ps.PrintLine (s + "Ghost (" + st + ")");
    ps.PrintLine ("(requires " + (string_of_exp rs) + ")");
    let sprets = String.concat ", " (List.map string_of_pformal p.prets) in
    ps.PrintLine ("(ensures (fun (" + sprets + ") -> " + (string_of_exp es) + "))");
    ps.Unindent ();
    in
  ( match tactic with
    | None ->
        ps.PrintLine ("irreducible val " + (sid p.pname) + " : " + (val_string_of_formals args));
        printPType "-> "
    | Some _ -> ()
  );
  ( match p.pbody with
    | None -> ()
    | Some ss ->
        let formals = let_string_of_formals (match tactic with None -> false | Some _ -> true) args in
        ps.PrintLine ("irreducible let " + (sid p.pname) + " " + formals + " =");
        (match tactic with None -> () | Some _ -> ps.PrintLine "(");
        ps.Indent ();
        emit_stmts ps ss;
        let eRet = EApply (Id "tuple", List.map (fun (x, _, _, _, _) -> EVar x) p.prets) in
        ps.PrintLine (string_of_exp_prec 0 eRet)
        ps.Unindent ();
        ( match tactic with
          | None -> ()
          | Some e ->
              ps.PrintLine ") <: ("
              printPType "";
              ps.PrintLine (") by " + (string_of_exp_prec 99 e))
        )
  )

let emit_decl (ps:print_state) (loc:loc, d:decl):unit =
  try
    match d with
    | DVerbatim lines -> List.iter ps.PrintUnbrokenLine lines
    | DVar _ -> ()
    | DFun f -> emit_fun ps loc f
    | DProc p -> emit_proc ps loc p
  with err -> raise (LocErr (loc, err))

let emit_decls (ps:print_state) (ds:decls):unit =
  List.iter (emit_decl ps) ds

