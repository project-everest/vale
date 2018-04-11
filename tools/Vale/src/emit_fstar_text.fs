module Emit_fstar_text

open Ast
open Ast_util
open Transform
open Emit_common_base
open Microsoft.FSharp.Math

let resetOptions = ref ""
let prevResetOptionsPs = ref ""
let prevResetOptionsPsi = ref ""

let sid (x:id):string =
  match x with
  | Id s -> s
  | Reserved s -> qprefix "va_" s
  | Operator s -> internalErr (sprintf "custom operator: %A" x)

let prefix_id (prefix:string) (x:id):id =
  match x with
  | Id s -> Id (prefix + s)
  | Reserved s -> Reserved (prefix + s)
  | Operator s -> internalErr (sprintf "prefix_id: %A %A" prefix s)

let transparent_id (x:id):id = prefix_id "transparent_" x
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
  | BOr | BLor -> (16, 16, 17)
  | BAnd | BLand -> (18, 18, 19)
  | BLe | BGe | BLt | BGt | BEq | BSeq | BNe -> (20, 20, 21)
  | BAdd -> (30, 30, 31)
  | BSub -> (30, 30, 31)
  | BMul | BDiv | BMod -> (40, 40, 41)
  | BOldAt | BIn | BCustom _ -> internalErr (sprintf "binary operator: %A" op)

let string_of_bop (op:bop):string =
  match op with
  | BEquiv -> "<==>"
  | BImply -> "==>"
  | BExply -> internalErr "<=="
  | BOr -> "||"
  | BLor -> "\\/"
  | BAnd -> "&&"
  | BLand -> "/\\"
  | BEq -> "=="
  | BSeq -> "="
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
  | BOldAt | BIn | BCustom _ -> internalErr (sprintf "binary operator: %A" op)

let string_of_ghost (g:ghost) = ""
let string_of_var_storage (g:var_storage) = ""


let rec string_of_typ (t:typ):string =
  match t with
  | TName x -> sid x
  | TApp (TName (Id "tuple"), []) -> "unit"
  | TApp (TName (Id "tuple"), ts) -> "(" + (String.concat " * " (List.map string_of_typ ts)) + ")"
  | TApp (TName (Id "fun"), ts) -> "(" + (String.concat " -> " (List.map string_of_typ ts)) + ")"
  | TApp (t, []) -> "(" + (string_of_typ t) + " ())"
  | TApp (t, ts) -> "(" + (string_of_typ t) + " " + (String.concat " " (List.map string_of_typ ts)) + ")"

let rec string_of_exp_prec prec e =
  let r = string_of_exp_prec in
  let (s, ePrec) =
    let qbind q qsep xs ts e = (q + " " + (string_of_formals xs) + qsep + (string_of_triggers ts) + (r 5 e), 6) in
    match e with
    | ELoc (loc, ee) -> try (r prec ee, prec) with err -> raise (LocErr (loc, err))
    | EVar x -> (sid x, 99)
    | EInt i -> (string i, 99)
    | EReal r -> (r, 99)
    | EBitVector (n, i) -> ("bv" + (string n) + "(" + (string i) + ")", 99)
    | EBool true -> ("true", 99)
    | EBool false -> ("false", 99)
    | EString s -> ("\"" + s.Replace("\\", "\\\\") + "\"", 99)
    | EOp (Uop (UCall CallGhost), [e]) -> (r prec e, prec)
    | EOp (Uop UReveal, [EApply (x, es)]) -> (r prec (vaApp "reveal_opaque" [EApply (transparent_id x, es)]), prec)
    | EOp (Uop UNot, [e]) -> ("~" + (r 99 e), 90)
    | EOp (Uop UNeg, [e]) -> ("-" + (r 99 e), 0)
    | EOp (Uop (UIs x), [e]) -> ((r 90 e) + "." + (sid x) + "?", 0)
    | EOp (Uop (UReveal | UOld | UConst | UGhostOnly | UToOperand | UCustom _), [_]) -> internalErr (sprintf "unary operator: %A" e)
    | EOp (Uop _, ([] | (_::_::_))) -> internalErr (sprintf "unary operator: %A" e)
    | EOp (Bop BExply, [e1; e2]) -> (r prec (EOp (Bop BImply, [e2; e1])), prec)
    | EOp (Bop op, [e1; e2]) ->
      (
        let isChainOp (op:bop):bool =
          match op with
          | BLe | BGe | BLt | BGt -> true
          | _ -> false
          in
        match (op, skip_loc e1) with
        | (op, EOp (Bop op1, [e11; e12])) when isChainOp op && isChainOp op1 ->
            // Convert (a <= b) < c into (a <= b) && (b < c)
            let e2 = EOp (Bop op, [e12; e2]) in
            (r prec (EOp (Bop BAnd, [e1; e2])), 0)
        | _ ->
            let (pe, p1, p2) = prec_of_bop op in
            ((r p1 e1) + " " + (string_of_bop op) + " " + (r p2 e2), pe)
      )
    | EOp (Bop _, ([] | [_] | (_::_::_::_))) -> internalErr (sprintf "binary operator: %A" e)
    | EApply (Id "tuple", es) -> ("(" + (String.concat ", " (List.map (r 5) es)) + ")", 90)
    | EApply (Id "list", es) -> ("[" + (String.concat "; " (List.map (r 5) es)) + "]", 90)
//    | EOp (MultiOp MSet, es) -> notImplemented "MSet"
    | EOp (Subscript, [e1; e2]) -> (r prec (vaApp "subscript" [e1; e2]), prec)
    | EOp (Update, [e1; e2; e3]) -> (r prec (vaApp "update" [e1; e2; e3]), prec)
    | EOp (Cond, [e1; e2; e3]) -> ("if " + (r 90 e1) + " then " + (r 90 e2) + " else " + (r 90 e3), 0)
    | EOp (FieldOp x, [e]) -> ((r 90 e) + "." + (sid x), 90)
    | EOp (FieldUpdate x, [e1; e2]) -> ("{" + (r 90 e1) + " with " + (sid x) + " = " + (r 90 e2) + "}", 90)
    | EOp ((Subscript | Update | Cond | FieldOp _ | FieldUpdate _ | CodeLemmaOp | RefineOp | StateOp _ | OperandArg _), _) -> internalErr (sprintf "EOp: %A" e)
    | EApply (x, es) -> ("(" + (sid x) + " " + (string_of_args es) + ")", 90)
    | EBind ((Forall | Exists | Lambda), [], [], _, e) -> (r prec e, prec)
    | EBind (Forall, [], xs, ts, e) -> qbind "forall" " . " xs ts e
    | EBind (Exists, [], xs, ts, e) -> qbind "exists" " . " xs ts e
    | EBind (Lambda, [], xs, ts, e) -> qbind "fun" " -> " xs ts e
    | EBind (BindLet, [ex], [x], [], e) -> ("let " + (string_of_formal x) + " = " + (r 5 ex) + " in " + (r 5 e), 6)
    | EBind (BindLet, [ex], xs, [], e) -> ("let (" + String.concat ", " (List.map string_of_formal xs) + ") = " + (r 5 ex) + " in " + (r 5 e), 6)
    | EBind (BindAlias, _, _, _, e) -> (r prec e, prec)
    | EBind (BindSet, [], xs, ts, e) -> notImplemented "iset"
    | EBind ((Forall | Exists | Lambda | BindLet | BindSet), _, _, _, _) -> internalErr (sprintf "EBind: %A" e)
  in if prec <= ePrec then s else "(" + s + ")"
and string_of_ret (x:id, t:typ option) = match t with None -> internalErr (sprintf "string_of_ret: %A" x) | Some t -> "(" + (sid x) + ":" + (string_of_typ t) + ")"
and string_of_formal (x:id, t:typ option) = match t with None -> sid x | Some t -> "(" + (sid x) + ":" + (string_of_typ t) + ")"
and string_of_formals (xs:formal list):string = String.concat " " (List.map string_of_formal xs)
and string_of_formal_bare (x:id, t:typ option) = match t with None -> sid x | Some t -> (sid x) + ":" + (string_of_typ t)
and string_of_pformal (x:id, t:typ, _, _, _) = string_of_formal (x, Some t)
and string_of_pformals (xs:pformal list):string = String.concat " " (List.map string_of_pformal xs)
and string_of_trigger (es:exp list):string = String.concat "; " (List.map string_of_exp es)
and string_of_triggers (ts:exp list list):string = 
    match ts with 
    | [] -> ""
    | [t] -> "{:pattern" + string_of_trigger t + "}"
    | _::_::_ -> "{:pattern " + String.concat "\/ " (List.map string_of_trigger ts) + "}"
and string_of_exp (e:exp):string = string_of_exp_prec 90 e
and string_of_exps (es:exp list):string = String.concat " " (List.map string_of_exp es)
and string_of_exps_tail (es:exp list):string = String.concat "" (List.map (fun e -> " " + string_of_exp e) es)
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

let string_of_decrease (es:exp list) n =
  match es with
  | [] -> ""
  | _ -> sprintf "(decreases %%[%s;%i])" (String.concat ";" (List.map string_of_exp es)) n
  
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
  | SCalc _ -> err "unsupported feature: 'calc' for F*"
  | SVar (x, tOpt, _, g, a, None) -> () // used to forward-declare variables for SLetUpdates
  | SVar (x, tOpt, _, g, a, Some e) ->
      let sf = string_of_formal (x, tOpt) in
      let rhs = " = " + (string_of_exp e) in
      ps.PrintLine ((string_of_var_storage g) + "let " + sf + rhs + " in")
  | SAlias _ -> internalErr "SAlias"
  | SAssign ([], e) -> ps.PrintLine ((string_of_exp e) + ";")
  | SAssign ([lhs], e) ->
      ps.PrintLine ("let " + (string_of_lhs_formal lhs) + " = " + (string_of_exp e) + " in")
  | SAssign ((_::_::_) as lhss, e) ->
      ps.PrintLine ("let (" + (String.concat ", " (List.map string_of_lhs_formal lhss)) + ") = " + (string_of_exp e) + " in")
  | SLetUpdates (outs, s) ->
      ps.PrintLine ("let (" + (String.concat ", " (List.map string_of_formal outs)) + ") =");
      ps.PrintLine "(";
      ps.Indent ();
      emit_stmt ps (Some (false, outs)) s;
      ps.Unindent ();
      ps.PrintLine ") in"
  | SBlock ss -> notImplemented "block"
  | SQuickBlock _ -> internalErr "quick_block"
  | SIfElse (_, e, ss1, ss2) ->
      ps.PrintLine ("if " + (string_of_exp e) + " then");
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
      ps.PrintLine ("if " + (string_of_exp e) + " then");
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
      let gen_aux_lemma l f intro n xs rest =
        ps.PrintLine ("let " + l + ":" + (let_string_of_formals true xs) + "-> Lemma");
        ps.Indent ();
        ps.PrintLine ("(forall " + (let_string_of_formals true rest) + ". " + (string_of_triggers ts));
        ps.PrintLine ("(" + (string_of_exp ex) + "==>" + (string_of_exp e) + ")" + ")");
        ps.PrintLine (" = fun " + (let_string_of_formals false xs) + "->" + intro);
        let p = [ for i in 1 .. n -> "t"+(string i)] in
        let string_of_p = String.concat " " p in
        ps.PrintLine (" (fun " + string_of_p + " -> FStar.Classical.move_requires " + "(" + f + " " + (let_string_of_formals false xs) + " " + string_of_p + ")" + ")");       
        ps.Unindent ();
      in
      let forall_intro_name l n = 
        if n >3 then l + "_forall_intro_" + (string n) else "FStar.Classical.forall_intro_3" 
      in
      let rec gen_forall_intro l n = 
        match n with
        | 0 | 1 | 2 | 3 -> ()
        | _ ->
          (
            gen_forall_intro l (n-1);
            ps.PrintLine("let " + (forall_intro_name l n));
            let t = [ for i in 1 .. n -> "(#t"+ (string i) + ":Type)"] in
            let p = [ for i in 1 .. n -> "a"+ (string i)] in
            let pt = [ for i in 1 .. n -> "a"+ (string i) + ":" + "t" + (string i)] in
            let ptp = [ for i in 1 .. n -> "(a"+ (string i) + ":" + "t" + (string i) + ")"] in
            ps.Indent ();
            ps.PrintLine((String.concat "" t) + " (#p:(" + (String.concat " -> " pt) + " -> Type0))");
            ps.PrintLine("($f: (" + (String.concat " -> " pt) + " -> Lemma (p " + (String.concat " " p) +  ")))");
            ps.PrintLine(":Lemma (forall " + (String.concat " " ptp) + ". p " + (String.concat " " p) + ")");
            ps.PrintLine("= let g: " + pt.Head + " -> Lemma (forall " + (String.concat " " ptp.Tail) + ".p " + (String.concat " " p) + ")");
            ps.PrintLine("  = fun " + p.Head + " -> " + (forall_intro_name  l (n-1)) + " (f " + p.Head + ") in");
            ps.PrintLine("FStar.Classical.forall_intro g in");
            ps.Unindent ();
          )
      in
      let rec gen_forall l f (xs: formal list) = 
        match xs.Length with 
        | 0 -> ps.PrintLine(l)
        | 1 -> ps.PrintLine("FStar.Classical.forall_intro " + "(FStar.Classical.move_requires " + f + ")")
        | 2 -> ps.PrintLine("FStar.Classical.forall_intro_2 " + "(fun x -> FStar.Classical.move_requires " + "(" + f + " x)" + ")")
        | 3 -> ps.PrintLine("FStar.Classical.forall_intro_3 " + "(fun x y -> FStar.Classical.move_requires " + "(" + f + " x y)" + ")")
        | _ -> 
         (
            let aux_name = f + "_1" in
            let n = xs.Length - 1 in
            gen_forall_intro l n;
            gen_aux_lemma aux_name f (forall_intro_name l n) (n-1) [xs.Head] xs.Tail;
            ps.PrintLine "in";
            ps.PrintLine("FStar.Classical.forall_intro " + "(FStar.Classical.move_requires " + aux_name + ")");
          )
      in
      let gen_lemma l xs ts ex e ss = 
        let f = l + "_f" in
        ps.PrintLine ("let " + f + " " + (let_string_of_formals true xs) + " : Lemma ");
        ps.Indent ();
        ps.PrintLine ("(requires " + (string_of_exp ex) + ")");
        ps.PrintLine ("(ensures " + (string_of_exp e) + ")");
        ps.PrintLine "=";
        emit_block ps " in " None ss;
        ps.Unindent ();
        gen_forall l f xs; 
      in
      ps.PrintLine ("let " + l + " () : Lemma ");
      match (xs, ts) with
      | ([], []) ->
          ps.PrintLine ("(requires " + (string_of_exp ex) + ")");
          ps.PrintLine ("(ensures " + (string_of_exp e) + ")");
          ps.PrintLine "=";
          emit_block ps (" in " + l + " ();") None ss;
      | ([], _::_) -> err "trigger only allowed with one or more variables"
      | (_, _) ->
        ( 
          ps.Indent();
          ps.PrintLine ("(forall " + (string_of_formals xs) + ". " + (string_of_triggers ts) + "(" + (string_of_exp ex) + "==>" + (string_of_exp e) + ")" + ")");
          ps.Unindent();
          ps.PrintLine "=";
          ps.Indent ();
          gen_lemma l xs ts ex e ss;
          ps.Unindent ()
          ps.PrintLine "in";      
        )
        ps.PrintLine(l + "();");
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

let emit_laxness (ps:print_state) (a:attrs):unit =
  if !disable_verify then
    let isAdmit = attrs_get_bool (Id "admit") false a in
    let isLax = attrs_get_bool (Id "lax") false a in
    let emit (ps:print_state) (prev:string ref) (opts:string):unit =
      let s = if isAdmit || isLax then "\"--lax\"" else opts in
      if !prev <> s then
       (
        prev := s;
        ps.PrintUnbrokenLine ("#reset-options " + s)
       )
      in
    emit ps prevResetOptionsPs !resetOptions;
    match ps.print_interface with None -> () | Some psi -> emit psi prevResetOptionsPsi ""

let emit_fun (ps:print_state) (loc:loc) (f:fun_decl):unit =
  ps.PrintLine ("");
  let isOpaqueToSmt = attrs_get_bool (Id "opaque_to_smt") false f.fattrs in
  let isOpaque = attrs_get_bool (Id "opaque") false f.fattrs in
  let isPublic = attrs_get_bool (Id "public") false f.fattrs in
  let isPublicDecl = attrs_get_bool (Id "public_decl") false f.fattrs in
  let isQAttr = attrs_get_bool (Id "qattr") false f.fattrs in
  let isAdmit = attrs_get_bool (Id "admit") false f.fattrs in
  let isPublicDecl = isPublicDecl || (isOpaque && isAdmit) in
  let isOpaque = isOpaque && not isAdmit in
  let isRecursive = attrs_get_bool (Id "recursive") false f.fattrs in
  (match ps.print_interface with None -> () | Some psi -> psi.PrintLine (""));
  let ps = match (isPublic, ps.print_interface) with (true, Some psi) -> psi | _ -> ps in
  let psi = match ps.print_interface with None -> ps | Some psi -> psi in
  emit_laxness ps f.fattrs;
  let sg = match f.fghost with Ghost -> "GTot" | NotGhost -> "Tot" in
  let sVal x decreases = "val " + x + " : " + (val_string_of_formals f.fargs) + " -> " + sg + " " + (string_of_typ f.fret) + decreases in
  let printBody header hasDecl x e =
    (if isOpaqueToSmt || isQAttr then ps.PrintLine ("[@" + (if isOpaqueToSmt then " \"opaque_to_smt\"" else "") + (if isQAttr then " va_qattr" else "") + "]"));
    let sRet = if hasDecl then "" else " : " + (string_of_typ f.fret) in
    ps.PrintLine (header + x + " " + (let_string_of_formals (not hasDecl) f.fargs) + sRet + " =");
    ps.Indent ();
    ps.PrintLine (if isAdmit then "admit ()" else string_of_exp e);
    ps.Unindent ()
    in
  let header = if isRecursive then "let rec " else "let " in
  // add custom metrics to convince F* that mutually recursive functions terminate
  let dArgs = List.map (fun (x, _) -> EVar x) f.fargs in
  let decreases0 = if isRecursive then string_of_decrease dArgs 0 else "" in
  let decreases1 = if isRecursive then string_of_decrease dArgs 1 else "" in
  if isOpaque then
    ps.PrintLine (sVal (sid (transparent_id f.fname)) decreases0);
    psi.PrintLine (sVal (sid f.fname) decreases1);
    ( match f.fbody with
      | None -> ()
      | Some e -> printBody header true (sid (transparent_id f.fname)) e
    );
    let fArgs = List.map (fun (x, _) -> EVar x) f.fargs in
    let eOpaque = vaApp "make_opaque" [EApply (transparent_id f.fname, fArgs)] in
    let header = if isRecursive then "and " else "let " in
    printBody header true (sid f.fname) eOpaque
  else if isPublicDecl then
    psi.PrintLine (sVal (sid f.fname) decreases1);
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
  (match ps.print_interface with None -> () | Some psi -> psi.PrintLine (""));
  let psi = match ps.print_interface with None -> ps | Some psi -> psi in
  let tactic = match p.pbody with None -> None | Some _ -> attrs_get_exp_opt (Id "tactic") p.pattrs in
  let isRecursive = attrs_get_bool (Id "recursive") false p.pattrs in
  let decreaseExps = attrs_get_exps_opt (Id "decrease") p.pattrs in
  let isAdmit = attrs_get_bool (Id "admit") false p.pattrs in
  let isDependent = attrs_get_bool (Id "dependent") false p.pattrs in
  let isReducible = attrs_get_bool (Id "reducible") false p.pattrs in
  let isReducible = isReducible || isAdmit || (p.prets = []) in
  let tactic = if isAdmit then None else tactic in
  emit_laxness ps p.pattrs;
  let args = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.pargs in
  let rets = List.map (fun (x, t, _, _, _) -> (x, Some t)) p.prets in
  let printPType (ps:print_state) s decreases =
    ps.Indent ();
    let st = String.concat (if isDependent then " & " else " * ") (List.map string_of_pformal p.prets) in
    ps.PrintLine (s + (match p.prets with [] -> "Lemma" | _ -> "Ghost (" + st + ")" + decreases));
    ps.PrintLine ("(requires " + (string_of_exp rs) + ")");
    let sprets = String.concat ", " (List.map (fun (x, _, _, _, _) -> sid x) p.prets) in
    let sDep = if isDependent then "|" else "" in
    ps.PrintLine ("(ensures (" + (match p.prets with [] -> "" | _ -> "fun (" + sDep + sprets + sDep + ") -> ") + (string_of_exp es) + "))");
    ps.Unindent ();
    in
  let dArgs = match decreaseExps with Some es -> es | None -> List.map (fun (x, _) -> EVar x) args in
  let decreases0 = if isRecursive then string_of_decrease dArgs 0 else "" in
  ( match (tactic, ps.print_interface) with
    | (Some _, None) -> ()
    | (_, _) ->
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
        if isAdmit then
          ps.PrintLine "admit ()"
        else
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

let emit_decl (ps:print_state) (loc:loc, d:decl):unit =
  try
    match d with
    | DVerbatim (attrs, lines) ->
      (
        emit_laxness ps attrs;
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
        match ps.print_interface with None -> () | Some psi -> psi.PrintLine ("module " + s)
    | DPragma (ResetOptions s) ->
        resetOptions := s;
        prevResetOptionsPs := s;
        ps.PrintUnbrokenLine ("#reset-options " + s)
    | DVar _ -> ()
    | DFun f -> emit_fun ps loc f
    | DProc p -> emit_proc ps loc p
  with err -> raise (LocErr (loc, err))

let emit_decls (ps:print_state) (ds:decls):unit =
  List.iter (emit_decl ps) ds

