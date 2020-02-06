module Emit_fstar_text

open Ast
open Ast_util
open Transform
open Emit_common_base
open Microsoft.FSharp.Math

let sid (x:id):string =
  match x with
  | Id s -> if s.StartsWith("uu___") then "_" + s else s
  | Reserved s -> qprefix "va_" s
  | Operator s -> internalErr (sprintf "custom operator: %A" x)

let prefix_id (prefix:string) (x:id):id =
  match x with
  | Id s -> Id (prefix + s)
  | Reserved s -> Reserved (prefix + s)
  | Operator s -> internalErr (sprintf "prefix_id: %A %A" prefix s)

let irreducible_id (x:id):id = prefix_id "irreducible_" x
let internal_id (x:id):id = prefix_id "internal_" x

// non-associative: (n, n+1, n+1)
// left-associative: (n, n, n+1)
// right-associative: (n, n+1, n)
let prec_of_bop (op:bop):(int * int * int) =
  match op with
  | BEquiv -> (10, 11, 11)
  | BImply -> (12, 13, 13)
  | BExply -> notImplemented "<=="
  | BOr _ -> (16, 16, 17)
  | BAnd _ -> (18, 18, 19)
  | BLe | BGe | BLt | BGt | BEq _ | BNe _ -> (20, 20, 21)
  | BAdd -> (30, 30, 31)
  | BSub -> (30, 30, 31)
  | BMul | BDiv | BMod -> (40, 40, 41)
  | BOldAt | BIn | BCustom _ -> internalErr (sprintf "binary operator: %A" op)

let string_of_bop (op:bop):string =
  match op with
  | BEquiv -> "<==>"
  | BImply -> "==>"
  | BExply -> internalErr "<=="
  | BOr BpBool -> "||"
  | BOr BpProp -> "\\/"
  | BAnd BpBool -> "&&"
  | BAnd BpProp -> "/\\"
  | BEq BpBool -> "="
  | BEq BpProp -> "=="
  | BNe BpBool -> "<>"
  | BNe BpProp -> "=!="
  | BLt -> "<"
  | BGt -> ">"
  | BLe -> "<="
  | BGe -> ">="
  | BAdd -> "+"
  | BSub -> "-"
  | BMul -> "`op_Multiply`"
  | BDiv -> "`op_Division`"
  | BMod -> "`op_Modulus`"
  | BOldAt | BIn | BCustom _ -> internalErr (sprintf "binary operator: %A" op)

let string_of_ghost (g:ghost) = ""
let string_of_var_storage (g:var_storage) = ""

let string_of_int (i:bigint):string =
  if i < bigint.Zero then "(" + string i + ")" else string i

let rec string_of_typ (t:typ):string =
  match t with
  | TName (Id "state") -> sid (Reserved "state")
  | TName x -> sid x
  | TApply (x, []) -> "(" + (sid x) + " ())"
  | TApply (x, ts) -> "(" + (sid x) + " " + (String.concat " " (List.map string_of_typ ts)) + ")"
  | TBool BpBool -> "bool"
  | TBool BpProp -> "prop"
  | TInt (Int k1, Int k2) -> "(va_int_range " + string_of_int k1 + " " + string_of_int k2 + ")"
  | TInt (Int k1, Inf) -> "(va_int_at_least " + string_of_int k1 + ")"
  | TInt (NegInf, Int k2) -> "(va_int_at_most " + string_of_int k2 + ")"
  | TInt (_, _) -> "int"
  | TTuple [] -> "unit"
  | TTuple ts -> "(" + (String.concat " & " (List.map string_of_typ ts)) + ")"
  | TFun (ts, t) -> "(" + (String.concat " -> " (List.map string_of_typ (ts @ [t]))) + ")"
  | TDependent x -> sid x
  | TVar _ -> internalErr "string_of_typ: TVar"
let string_of_type_argument ((q:tqual), (t:typ)):string =
  match q with
  | TqExplicit -> string_of_typ t
  | TqImplicit -> "#" + string_of_typ t
let string_of_type_arguments (ts:(tqual * typ) list option):string = 
  match ts with 
  | None -> ""
  | Some [] -> "" 
  | Some ts -> " " + String.concat " " (List.map string_of_type_argument ts)


let rec string_of_exp_prec prec e =
  let r = string_of_exp_prec in
  let (s, ePrec) =
    let qbind q qsep xs ts e = (q + " " + (string_of_formals xs) + qsep + (string_of_triggers ts) + (r 5 e), 6) in
    match e with
    | ELoc (loc, ee) -> try (r prec ee, prec) with err -> raise (LocErr (loc, err))
    | EVar (x, _) -> (sid x, 99)
    | EInt i -> (string_of_int i, 99)
    | EReal r -> (r, 99)
    | EBitVector (n, i) -> ("bv" + (string n) + "(" + (string i) + ")", 99)
    | EBool true -> ("true", 99)
    | EBool false -> ("false", 99)
    | EString s -> ("\"" + s.Replace("\\", "\\\\") + "\"", 99)
    | EOp (Uop (UCall CallGhost), [e], t) -> (r prec e, prec)
    | EOp (Uop UReveal, [EApply (e, _, es, t1) as ea], t) when is_id e -> (r prec (eapply (Reserved "reveal_opaque") [EOp (Uop UFStarNameString, [e], None); ea]), prec)
    | EOp (Uop UReveal, [EVar (x, _) as e], t) -> (r prec (eapply (Reserved "reveal_opaque") [EOp (Uop UFStarNameString, [e], None); e]), prec)
    | EOp (Uop UFStarNameString, [e], _) -> ("`%" + r 99 e, 0)
    | EOp (Uop (UNot BpBool), [e], t) -> ("not " + (r 99 e), 90)
    | EOp (Uop (UNot BpProp), [e], t) -> ("~" + (r 99 e), 90)
    | EOp (Uop UNeg, [e], t) -> ("-" + (r 99 e), 0)
    | EOp (Uop (UIs x), [e], t) -> ((sid x) + "? " + (r 90 e), 0)
    | EOp (Uop (UReveal | UOld | UConst | UGhostOnly | UToOperand | UCustom _), [_], _) -> internalErr (sprintf "unary operator: %A" e)
    | EOp (Uop _, ([] | (_::_::_)), _) -> internalErr (sprintf "unary operator: %A" e)
    | EOp (Bop BExply, [e1; e2], t) -> (r prec (EOp (Bop BImply, [e2; e1], t)), prec)
    | EOp (Bop BIn, [e1; e2], t) ->
      let t = exp_typ e2 in
      match t with
      | Some (TApply (x, _) | TName x) ->
        (r prec (vaApp_t ("contains_" + (sid x)) [e2; e1] t), prec)
      | _ -> internalErr (sprintf "overloaded Operator ?[] missing type info: %A : %A" e t)
    | EOp (Bop op, [e1; e2], t) ->
      (
        let isChainOp (op:bop):bool =
          match op with
          | BLe | BGe | BLt | BGt -> true
          | _ -> false
          in
        match (op, skip_loc e1) with
        | (op, EOp (Bop op1, [e11; e12], t)) when isChainOp op && isChainOp op1 ->
            // Convert (a <= b) < c into (a <= b) && (b < c)
            let e2 = EOp (Bop op, [e12; e2], t) in
            (r prec (EOp (Bop (BAnd BpBool), [e1; e2], t)), 0)
        | _ ->
            let (pe, p1, p2) = prec_of_bop op in
            ((r p1 e1) + " " + (string_of_bop op) + " " + (r p2 e2), pe)
      )
    | EOp (Bop _, ([] | [_] | (_::_::_::_)), _) -> internalErr (sprintf "binary operator: %A" e)
    | EOp (TupleOp _, es, t) -> ("(" + (String.concat ", " (List.map (r 5) es)) + ")", 90)
    | EApply (e, ts, es, t) when is_id e && id_of_exp e = (Id "list") -> ("[" + (String.concat "; " (List.map (r 5) es)) + "]", 90)
    | EOp (Subscript, [e1; e2], t) -> 
      let t = exp_typ e1 in
      match t with
      | Some (TApply (x, _) | TName x) ->
        (r prec (vaApp_t ("subscript_" + (sid x)) [e1; e2] t), prec)
      | _ ->
        internalErr (sprintf "overloaded Operator[] missing type info: %A : %A" e t)
    | EOp (Update, [e1; e2; e3], t) -> 
      let t = exp_typ e1 in
      match t with
      | Some (TApply (x, _) | TName x) ->
        (r prec (vaApp_t ("update_" + (sid x)) [e1; e2; e3] t), prec)
      | _ ->
        internalErr (sprintf "overloaded Operator[:=] missing type info: %A : %A" e t)
    | EOp (Cond, [e1; e2; e3], t) -> ("if " + (r 90 e1) + " then " + (r 90 e2) + " else " + (r 90 e3), 0)
    | EOp (FieldOp x, [e], _) ->
      let t = exp_typ e in
      match (t, x) with 
      | (Some (TApply (x, _)), Id f) ->
        let (mn, t) = name_of_id x in
        let s = if mn = "" then "" else mn + "." in
        let s = s + "__proj__" + "Mk" + string_of_id t + "__item__" + f in
        (s + " " + (r 95 e),  95)
      | _ ->
        ((r 95 e) + "." + (sid x), 95)
    | EOp (FieldUpdate x, [e1; e2], t) -> 
      let t = exp_typ e1 in
      match (t, x) with 
      | (Some (TName x), Id f) ->
        let (mn, t) = name_of_id x in
        let s = if mn = "" then "" else mn + "." in
        let s = s + "__proj__" + string_of_id t + "__item__" + f in
        (s + " " + (r 90 e1) + " " + (r 90 e2),  0)
      | _ ->
        ("({" + (r 90 e1) + " with " + (sid x) + " = " + (r 90 e2) + "})", 90)
    | EOp ((Subscript | Update | Cond | FieldOp _ | FieldUpdate _ | CodeLemmaOp | RefineOp | StateOp _ | OperandArg _), _, _) -> internalErr (sprintf "EOp: %A" e)
    | EApply (e, ts, es, t) ->  ((r 90 e) + (string_of_type_arguments ts) + " " + (string_of_args es), 90)
    | EBind ((Forall | Exists | Lambda), [], [], _, e, t) -> (r prec e, prec)
    | EBind (Forall, [], xs, ts, e, t) -> qbind "forall" " . " xs ts e
    | EBind (Exists, [], xs, ts, e, t) -> qbind "exists" " . " xs ts e
    | EBind (Lambda, [], xs, ts, e, t) -> qbind "fun" " -> " xs ts e
    | EBind (BindLet, [ex], [x], [], e, t) -> ("let " + (string_of_formal x) + " = " + (r 5 ex) + " in " + (r 5 e), 6)
    | EBind (BindLet, [ex], xs, [], e, t) -> ("let (" + String.concat ", " (List.map string_of_formal xs) + ") = " + (r 5 ex) + " in " + (r 5 e), 6)
    | EBind (BindAlias, _, _, _, e, t) -> (r prec e, prec)
    | EBind (BindSet, [], xs, ts, e, t) -> notImplemented "iset"
    | EBind ((Forall | Exists | Lambda | BindLet | BindSet), _, _, _, _, _) -> internalErr (sprintf "EBind: %A" e)
    | ECast (c, e, t) -> (r prec e, prec) // TODO: add type conversion
    | ELabel (l, e) -> (r prec e, prec)
    | _ -> internalErr  (sprintf "unexpected exp %A " e)
  in if prec <= ePrec then s else "(" + s + ")"
and string_of_ret (x:id, t:typ option) = match t with None -> internalErr (sprintf "string_of_ret: %A" x) | Some t -> "(" + (sid x) + ":" + (string_of_typ t) + ")"
and string_of_formal (x:id, t:typ option) = match t with None -> sid x | Some t -> "(" + (sid x) + ":" + (string_of_typ t) + ")"
and string_of_formals (xs:formal list):string = String.concat " " (List.map string_of_formal xs)
and string_of_formal_bare (x:id, t:typ option) = match t with None -> sid x | Some t -> (sid x) + ":" + (string_of_typ t)
and string_of_pformal (x:id, t:typ, _, _, _) = string_of_formal (x, Some t)
and string_of_pformals (xs:pformal list):string = String.concat " " (List.map string_of_pformal xs)
and typ_of_pformal (_, t:typ, _, _, _) = string_of_typ t
and string_of_trigger (es:exp list):string = String.concat "; " (List.map string_of_exp es)
and string_of_triggers (ts:exp list list):string =
    match ts with
    | [] -> ""
    | [t] -> "{:pattern" + string_of_trigger t + "}"
    | _::_::_ -> "{:pattern " + String.concat "\/ " (List.map string_of_trigger ts) + "}"
and string_of_exp (e:exp):string = string_of_exp_prec 99 e
and string_of_exp90 (e:exp):string = string_of_exp_prec 90 e
and string_of_exps (es:exp list):string = String.concat " " (List.map string_of_exp es)
and string_of_args (es:exp list):string = match es with [] -> "()" | _ -> string_of_exps es

let name_of_formal (x:id, t:typ option) = sid x
let type_of_formal (x:id, t:typ option) = match t with None -> "_" | Some t -> (string_of_typ t)

let string_of_lhs_formal ((x, tOpt):lhs):string = match tOpt with Some (t, _) -> string_of_formal (x, t) | _ -> sid x

let val_string_of_formals (xs:formal list) =
  match xs with
  | [] -> (sid (Reserved "dummy")) + ":unit"
  | _ -> String.concat " -> " (List.map string_of_formal_bare xs)

let let_string_of_formals (useTypes:bool) (xs:formal list) =
  match xs with
  | [] -> "()"
  | _ -> string_of_formals (List.map (fun (x, t) -> (x, if useTypes then t else None)) xs)

let string_of_decrease (es:exp list) =
  match es with
  | [] -> ""
  | _ -> sprintf "(decreases %%[%s])" (String.concat ";" (List.map string_of_exp es))

let string_of_outs_exp (outs:(bool * formal list) option):string =
  match outs with
  | None -> "()"
  | Some (dep, fs) ->
      let sDep = if dep then "|" else "" in
      "(" + sDep + (String.concat ", " (List.map name_of_formal fs)) + sDep + ")"

let string_of_outs_formals (outs:(bool * formal list) option):string =
  match outs with
  | None -> "()"
  | Some (dep, fs) ->
      let sDep = if dep then "|" else "" in
      "(" + sDep + (String.concat ", " (List.map name_of_formal fs)) + sDep + "):(" +
      (String.concat (if dep then " & " else " * ") (List.map string_of_ret fs)) + ")"

let rec emit_stmt (ps:print_state) (outs:(bool * formal list) option) (s:stmt):unit =
  match s with
  | SLoc (loc, s) -> try emit_stmt ps outs s with err -> raise (LocErr (loc, err))
  | SLabel _ -> err "unsupported feature: labels (unstructured code)"
  | SGoto _ -> err "unsupported feature: 'goto' (unstructured code)"
  | SReturn _ -> err "unsupported feature: 'return' (unstructured code)"
  | SAssume e -> ps.PrintLine ("assume " + (string_of_exp e) + ";")
  | SAssert (_, e) -> ps.PrintLine ("assert " + (string_of_exp e) + ";")
  | SCalc (op, contents, e) -> 
      ps.PrintLine ("calc (" + string_of_bop op + ") {");
      ps.Indent();
      List.iter (fun {calc_exp = e; calc_op = op; calc_hints = hints} ->
        ps.PrintLine ((string_of_exp e) + ";");
        ps.PrintLine(string_of_bop op);
        ps.PrintLine("{"); List.iter (emit_block ps "" outs) hints;  ps.PrintLine("}");
      ) contents;
      ps.PrintLine((string_of_exp e) + ";")
      ps.Unindent();
      ps.PrintLine("};")
  | SVar (x, tOpt, _, g, a, None) -> () // used to forward-declare variables for SLetUpdates
  | SVar (x, tOpt, _, g, a, Some e) ->
      let sf = string_of_formal (x, tOpt) in
      let rhs = " = " + (string_of_exp90 e) in
      ps.PrintLine ((string_of_var_storage g) + "let " + sf + rhs + " in")
  | SAlias _ -> internalErr "SAlias"
  | SAssign ([], e) -> ps.PrintLine ((string_of_exp90 e) + ";")
  | SAssign ([lhs], e) ->
      ps.PrintLine ("let " + (string_of_lhs_formal lhs) + " = " + (string_of_exp90 e) + " in")
  | SAssign ((_::_::_) as lhss, e) ->
      ps.PrintLine ("let (" + (String.concat ", " (List.map string_of_lhs_formal lhss)) + ") = " + (string_of_exp90 e) + " in")
  | SLetUpdates (outs, s) ->
      ps.PrintLine ("let (" + (String.concat ", " (List.map string_of_formal outs)) + ") =");
      ps.PrintLine "(";
      ps.Indent ();
      emit_stmt ps (Some (false, outs)) s;
      ps.Unindent ();
      ps.PrintLine ") in"
  | SBlock ss -> notImplemented "block"
  | SIfElse (_, e, ss1, ss2) ->
      ps.PrintLine ("if " + (string_of_exp90 e) + " then");
      emit_block ps "" outs ss1;
      ps.PrintLine ("else");
      emit_block ps (match outs with None -> ";" | Some _ -> "") outs ss2
  | SWhile (e, invs, (_, ed), ss) ->
      let st = match outs with None -> "()" | Some (dep, fs) -> String.concat (if dep then " & " else " * ") (List.map string_of_ret fs) in
      let sWhile = sid (Reserved "while") in
      let sParams = match outs with None -> "()" | Some (_, fs) -> string_of_formals fs in
      ps.PrintLine ("let rec " + sWhile + " " + sParams + " : Ghost (" + st + ")");
      ps.Indent ();
      let inv = and_of_list (List.map snd invs) in
      ps.PrintLine ("(requires " + (string_of_exp inv) + ")");
      ps.PrintLine ("(ensures (fun " + string_of_outs_exp outs + " -> (not (" + (string_of_exp e) + ")) /\ " + (string_of_exp inv) + "))");
      let () =
        match (ed, outs) with
        | ([], Some (_, ((x, _)::_))) -> ps.PrintLine ("(decreases " + (sid x) + ")")
        | (_::_, _) -> ps.PrintLine ("(decreases (" + (String.concat ", " (List.map string_of_exp ed)) + "))")
        | ([], _) -> ()
        in
      ps.PrintLine "=";
      ps.PrintLine ("if " + (string_of_exp90 e) + " then");
      ps.Indent ();
      ps.PrintLine ("let " + (string_of_outs_formals outs) + " =");
      emit_block ps "" outs ss;
      let args = match outs with None -> "()" | Some (_, fs) -> String.concat " " (List.map (fun (x, _) -> sid x) fs) in
      ps.PrintLine ("in " + sWhile + " " + args);
      ps.Unindent ();
      ps.PrintLine ("else " + (string_of_outs_exp outs));
      ps.Unindent ();
      ps.PrintLine ("in " + sWhile + " " + args)
  | SForall (xs, ts, ex, e, ss) ->
    (
      let l = sid (Reserved "forall_lemma") in
      ps.PrintLine ("let " + l + " " + (let_string_of_formals true xs) + " : Lemma");
      ps.Indent ();
      ps.PrintLine ("(requires " + (string_of_exp ex) + ")");
      ps.PrintLine ("(ensures " + (string_of_exp e) + ")");
      match (xs, ts) with
      | ([], []) ->
          ps.PrintLine "=";
          ps.Unindent ();
          let s =
            match skip_loc ex with
            | EBool true | ECast (_, EBool true, _) -> l
            | _ -> "FStar.Classical.move_requires " + l
            in
          emit_block ps (" in " + s + " ();") None ss
      | ([], _::_) -> err "trigger only allowed with one or more variables"
      | (_::_, ts) ->
          let smtpat es = "SMTPat (" + (string_of_exp es) + ")" in
          let smtpats es = "[" + String.concat "; " (List.map smtpat es) + "]" in
          let pats = 
            match ts with
            | [] -> err "in fstar mode, forall statements must have at least one trigger"
            | [es] -> smtpats es
            | _::_ -> "[SMTPatOr [" + String.concat "; " (List.map smtpats ts) + "]]"
            in
          ps.PrintLine pats;
          ps.PrintLine ("=");
          ps.Unindent ();
          emit_block ps " in" None ss
    )
  | SExists (xs, ts, e) -> notImplemented "exists statements"
and emit_stmts (ps:print_state) (outs:(bool * formal list) option) (stmts:stmt list) =
  List.iter (emit_stmt ps None) stmts;
  ps.PrintLine (string_of_outs_exp outs)
and emit_block (ps:print_state) (suffix:string) (outs:(bool * formal list) option) (stmts:stmt list) =
  ps.PrintLine "(";
  ps.Indent ();
  emit_stmts ps outs stmts;
  ps.Unindent ();
  ps.PrintLine (")" + suffix)

let emit_fun (ps:print_state) (loc:loc) (f:fun_decl):unit =
  ps.PrintLine ("");
  let isOpaque = attrs_get_bool (Id "opaque") false f.fattrs in
  let isOpaqueToSmt = isOpaque || attrs_get_bool (Id "opaque_to_smt") false f.fattrs in
  let isPublic = attrs_get_bool (Id "public") false f.fattrs in
  let isPublicDecl = attrs_get_bool (Id "public_decl") false f.fattrs in
  let isQAttr = attrs_get_bool (Id "qattr") false f.fattrs in
  let isPublicDecl = isPublicDecl || isOpaque in
  let isRecursive = attrs_get_bool (Id "recursive") false f.fattrs in
  // write everything to *.fsti if it is public and not opaque or publicDecl. 
  // For opaque and publicDecl, only "val" is written into *.fsti if it is public, 
  // everything else goes into *.fst regardless if it is public or not.
  let writeToPsi = isPublic && not (isOpaque || isPublicDecl) 
  let ps = match (writeToPsi, ps.print_interface) with (true, Some psi) -> psi | _ -> ps in
  let psi = match ps.print_interface with None -> ps | Some psi -> psi in
  let sg = match f.fghost with Ghost -> "GTot" | NotGhost -> "Tot" in
  let sVal x decreases = "val " + x + " : " + (val_string_of_formals f.fargs) + " -> " + sg + " " + (string_of_typ f.fret) + decreases in
  let printBody header hasDecl x e =
    (if isOpaqueToSmt || isQAttr then ps.PrintLine ("[@" + (if isOpaqueToSmt then " \"opaque_to_smt\"" else "") + (if isQAttr then " va_qattr" else "") + "]"));
    let sRet = if hasDecl then "" else " : " + (string_of_typ f.fret) in
    ps.PrintLine (header + x + " " + (let_string_of_formals (not hasDecl) f.fargs) + sRet + " =");
    ps.Indent ();
    ps.PrintLine (string_of_exp e);
    ps.Unindent ()
    in
  let header = if isRecursive then "let rec " else "let " in
  // add custom metrics to convince F* that mutually recursive functions terminate
  let dArgs = List.map (fun (x, _) -> evar x) f.fargs in
  let decreases0 = if isRecursive then string_of_decrease dArgs else "" in
  if isPublicDecl then
    if isPublic then (
      psi.PrintLine ("")
      psi.PrintLine (sVal (sid f.fname) decreases0);
    )
    else
      ps.PrintLine (sVal (sid f.fname) decreases0);
    ( match f.fbody with
      | None -> ()
      | Some e -> printBody header true (sid f.fname) e
    )
  else
  (
    match f.fbody with
    | None -> ()
    | Some e -> printBody header false (sid f.fname) e
  )

let emit_proc (ps:print_state) (loc:loc) (p:proc_decl):unit =
  gen_lemma_sym_count := 0;
  let (reqs, enss) = collect_specs false p.pspecs in
  let (rs, es) = (and_of_list reqs, and_of_list enss) in
  ps.PrintLine ("");
  let psi = match ps.print_interface with None -> ps | Some psi -> psi in
  let tactic = match p.pbody with None -> None | Some _ -> attrs_get_exp_opt (Id "tactic") p.pattrs in
  let isPublic = attrs_get_bool (Id "public") false p.pattrs in
  let isRecursive = attrs_get_bool (Id "recursive") false p.pattrs in
  let decreaseExps = attrs_get_exps_opt (Id "decrease") p.pattrs in
  let isDependent = attrs_get_bool (Id "dependent") false p.pattrs in
  let isReducible = attrs_get_bool (Id "reducible") false p.pattrs in
  let isReducible = isReducible || (p.prets = []) in
  let args = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.pargs in
  let rets = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.prets in
  let printPType (ps:print_state) s decreases =
    ps.Indent ();
    let st = String.concat " & " (List.map typ_of_pformal p.prets) in
    ps.PrintLine (s + (match p.prets with [] -> "Lemma" | _ -> "Ghost (" + st + ")" + decreases));
    ps.PrintLine ("(requires " + (string_of_exp rs) + ")");
    let sprets = String.concat ", " (List.map (fun (x, _, _, _, _) -> sid x) p.prets) in
    let sDep = if isDependent then "|" else "" in
    ps.PrintLine ("(ensures (" + (match p.prets with [] -> "" | _ -> "fun (" + sDep + sprets + sDep + ") -> ") + (string_of_exp_prec 5 es) + "))");
    ps.Unindent ();
    in
  let dArgs = match decreaseExps with Some es -> es | None -> List.map (fun (x, _) -> evar x) args in
  let decreases0 = if isRecursive then string_of_decrease dArgs else "" in
  ( match (tactic, ps.print_interface) with
    | (Some _, None) -> ()
    | (_, _) ->
        let psi = if isPublic then psi else ps
        psi.PrintLine ("");
        psi.PrintLine ("val " + (sid p.pname) + " : " + (val_string_of_formals args));
        printPType psi "-> " decreases0
  );
  ( match p.pbody with
    | None -> ()
    | Some ss ->
        let formals = let_string_of_formals (match tactic with None -> false | Some _ -> true) args in
        (if not isReducible then ps.PrintLine "[@\"opaque_to_smt\"]");
        let header = if isRecursive then "let rec " else "let " in
        ps.PrintLine (header + (sid p.pname) + " " + formals + " =")
        (match tactic with None -> () | Some _ -> ps.PrintLine "(");
        ps.Indent ();
        let mutable_scope = Map.ofList (List.map (fun (x, t, _, _, _) -> (x, Some t)) p.prets) in
        let (_, ss) = let_updates_stmts mutable_scope ss in
        let outs = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.prets in
        emit_stmts ps (Some (isDependent, outs)) ss;
        ps.Unindent ();
        ( match tactic with
          | None -> ()
          | Some e ->
              ps.PrintLine ") <: ("
              printPType ps "" "";
              ps.PrintLine (") by " + (string_of_exp_prec 99 e))
        )
  )

let emit_open (ps:print_state) (s:string):unit =
  ps.PrintLine ("open " + s)
  match ps.print_interface with None -> () | Some psi -> psi.PrintLine ("open " + s)

let emit_decl (ps:print_state) (opens:(string * string option option) list) (loc:loc, d:decl):unit =
  try
    match d with
    | DVerbatim (attrs, lines) ->
      (
        let isInterface = attrs_get_bool (Id "interface") false attrs in
        let isImplementation = attrs_get_bool (Id "implementation") false attrs in
        match (isInterface, isImplementation, ps.print_interface) with
        | (true, false, Some psi) -> List.iter psi.PrintUnbrokenLine lines
        | (true, true, Some psi) ->
            List.iter psi.PrintUnbrokenLine lines;
            List.iter ps.PrintUnbrokenLine lines
        | _ -> List.iter ps.PrintUnbrokenLine lines
      )
    | DPragma (ModuleName s) ->
        ps.PrintLine ("module " + s);
        match ps.print_interface with None -> () | Some psi -> psi.PrintLine ("module " + s);
        // TODO: emit "open M" from "include {:fstar}{:open} M
        // List.iter (emit_open ps) opens
    | DPragma (PushOptions ops) ->
        let rec dump e =
          match skip_locs e with
          | EVar _ | EInt _ | EBool _ -> string_of_exp e
          | EString s -> "'" + s + "'"
          | EOp (FieldOp x, [e], _) -> dump e + "." + sid x 
          | EApply (e, _, es, _) -> dump e + " " + String.concat " " (List.map dump es)
          | _ ->
              err "options in :options attribute must consist of variables, ., integers, strings, booleans, and function applications"
          in
        let s = String.concat " " (List.map (fun e -> "--" + dump e) ops) in
        ps.PrintUnbrokenLine ("#push-options \"" + s + "\"")
    | DVar _ -> ()
    | DFun f -> emit_fun ps loc f
    | DProc p -> emit_proc ps loc p
    | _ -> ()
  with err -> raise (LocErr (loc, err))

let emit_decls (ps:print_state) (ds:decls) (opens:(string * string option option) list):unit =
  List.iter (emit_decl ps opens) ds

