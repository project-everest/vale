module Emit_dafny_direct

open Ast
open Ast_util
open Transform
open Emit_common_base
open Emit_dafny_text
open Microsoft.Dafny
open Microsoft.Basetypes
open Microsoft.FSharp.Math
open DafnyInterface

type IToken = Microsoft.Boogie.IToken

let create_dummy_token (value:string):IToken =
  let tok = new Microsoft.Boogie.Token() in
  tok.``val`` <- value;
  tok :> IToken

// Create Boogie Token
let create_token (loc:loc) (value:string):IToken =
  let tok = create_dummy_token value in
  tok.filename <- loc.loc_file; tok.line <-  loc.loc_line; tok.col <- loc.loc_col; tok.pos <- loc.loc_pos;
  tok

// Create Boogie BigDec
let get_dec (loc:loc) (str:string):BigDec =
  try BigDec.FromString(str)
  with
  | :? System.FormatException -> internalErr "incorrectly formatted number"

let ghost_to_bool (g:ghost):bool = match g with Ghost -> true | NotGhost -> false
let var_storage_to_bool (v:var_storage):bool = match v with XGhost -> true | _ -> false

let bop2opcode (op:bop):BinaryExpr.Opcode =
  match op with
  | BEquiv -> BinaryExpr.Opcode.Iff
  | BImply -> BinaryExpr.Opcode.Imp
  | BExply -> BinaryExpr.Opcode.Exp
  | BAnd _ -> BinaryExpr.Opcode.And
  | BOr _ -> BinaryExpr.Opcode.Or
  | BEq _ -> BinaryExpr.Opcode.Eq
  | BNe _ -> BinaryExpr.Opcode.Neq
  | BLt -> BinaryExpr.Opcode.Lt
  | BGt -> BinaryExpr.Opcode.Gt
  | BLe -> BinaryExpr.Opcode.Le
  | BGe -> BinaryExpr.Opcode.Ge
  | BIn -> BinaryExpr.Opcode.In
  | BAdd -> BinaryExpr.Opcode.Add
  | BSub -> BinaryExpr.Opcode.Sub
  | BMul -> BinaryExpr.Opcode.Mul
  | BDiv -> BinaryExpr.Opcode.Div
  | BMod -> BinaryExpr.Opcode.Mod
  | BOldAt | BCustom _ -> internalErr "binary operator"

let is_rel_op (op:bop):bool =
  match op with
  | BEq _ -> true
  | BNe _ -> true
  | BLt -> true
  | BGt -> true
  | BLe -> true
  | BGe -> true
  | _ -> false

let rec is_rel_expr (exp:exp):bool =
  match exp with
  | EOp (Bop op, _, _) -> is_rel_op op
  | _ -> false

// Create Dafny Type
// TODO: Add line information for better error output
let rec create_type (built_ins:BuiltIns) (t:typ):Type = // ignoring function types for now
  match t with
  | TName id ->
      match (sid id) with
      | "char" -> new CharType() :> Type
      | "nat" ->
          let tok = create_dummy_token "nat" in
          new UserDefinedType(tok, tok.``val``, null) :> Type
      | "int" -> new IntType() :> Type
      | "real" -> new RealType() :> Type
      | "object" -> new ObjectType() :> Type
      | "string" ->
          let tok = create_dummy_token "string" in
          new UserDefinedType(tok, tok.``val``, null) :> Type
      | s ->
          if s.Contains "." then notImplemented "type creation for types with dots"
          else
            let tok = create_dummy_token s in
            let e = new NameSegment(tok, s, null) in
            new UserDefinedType(tok, e) :> Type
  | TTuple l ->
      match l with
      | [] ->
          let tok = create_dummy_token "tuple_token" in
          let tmp = built_ins.TupleType(tok, 0, true) in
          new UserDefinedType(tok, BuiltIns.TupleTypeName(0), null) :> Type
      | t :: [] -> create_type built_ins t
      | _ ->
          let tok = create_dummy_token "tuple_token" in
          let args = List.fold (fun (acc:ResizeArray<Type>) (elem:typ) -> acc.Add(create_type built_ins elem); acc) (new ResizeArray<Type>()) l in
          let dims = args.Count in
          let tmp = built_ins.TupleType(tok, dims, true) in
          new UserDefinedType(tok, BuiltIns.TupleTypeName(dims), args) :> Type
  | TApply (id, tlist) ->
      match (sid id) with
      | "set" ->
          match tlist with
          | [] -> new SetType (true, null) :> Type
          | t::[] -> new SetType(true, create_type built_ins t) :> Type
          | _ -> internalErr "set type expects only one type argument"
      | "iset" ->
          match tlist with
          | [] -> new SetType(false, null) :> Type
          | t::[] -> new SetType(false, create_type built_ins t) :> Type
          | _ -> internalErr "iset type expects only one type argument"
      | "multiset" ->
          match tlist with
          | [] -> new MultiSetType(null):> Type
          | t::[] -> new MultiSetType(create_type built_ins t):> Type
          | _ -> internalErr "multiset type expects only one type argument"
      | "seq" ->
          match tlist with
          | [] -> new SeqType(null):> Type
          | t::[] -> new SeqType(create_type built_ins t):> Type
          | _ -> internalErr "seq type expects only one type argument"
      | "map" ->
          match tlist with
          | [] -> new MapType(true, null, null) :> Type
          | t1::t2::[] -> new MapType(true, create_type built_ins t1, create_type built_ins t2) :> Type
          | _ -> internalErr "map type expects two type arguments"
      | "imap" ->
          match tlist with
          | [] -> new MapType(false, null, null) :> Type
          | t1::t2::[] -> new MapType(false, create_type built_ins t1, create_type built_ins t2) :> Type
          | _ -> internalErr "imap type expects two type arguments"
      | "array" -> // do not currently handle Dafny's higher dimensioned arrays
          let tok = create_dummy_token "array" in
          let args = List.fold (fun (acc:ResizeArray<Type>) (elem:typ) -> acc.Add(create_type built_ins elem); acc) (new ResizeArray<Type>()) tlist in
          let t = built_ins.ArrayType(tok, 1, args, true) in
          t :> Type
      | s ->
          if s.Contains "."
          then notImplemented "type creation for types with dots"
          else
            let tok = create_dummy_token s in
            let args = List.fold (fun (acc:ResizeArray<Type>) (elem:typ) -> acc.Add(create_type built_ins elem); acc) (new ResizeArray<Type>()) tlist in
            let e = new NameSegment(tok, s, args) in
            new UserDefinedType(e.tok, e) :> Type
  | TBool _ -> new BoolType() :> Type
  | TInt _ -> new IntType() :> Type
  | _ -> internalErr (sprintf "not implemented create_type for %A" t)

// Create Dafny formal from Vale formal
let create_formal (built_ins:BuiltIns) (loc:loc) (x:id, t:typ option):Formal =
  let id = create_token loc (sid x) in
  match t with
  | None -> err "formals must have types"
  | Some t -> new Formal(id, id.``val``, create_type built_ins t, true, false) //incoming, is_ghost

let create_formals (built_ins:BuiltIns) (loc:loc) (xs:formal list):ResizeArray<Formal> =
  List.fold (fun (acc:ResizeArray<Formal>) (elem:formal) -> acc.Add(create_formal built_ins loc elem); acc) (new ResizeArray<Formal>()) xs in

// Create Dafny formal from pformal
let create_pformal (built_ins:BuiltIns) (loc:loc) (x:id, t:typ, g:var_storage, _, _) (incoming:bool):Formal =
  let id = create_token loc (sid x) in
  let is_ghost = var_storage_to_bool g in
  new Formal(id, id.``val``, create_type built_ins t, incoming, is_ghost)

let create_pformals (built_ins:BuiltIns) (loc:loc) (xs:pformal list) (incoming):ResizeArray<Formal> =
  List.fold (fun (acc:ResizeArray<Formal>) (elem:pformal) -> acc.Add(create_pformal built_ins loc elem incoming); acc) (new ResizeArray<Formal>()) xs in

let create_bvar (built_ins:BuiltIns) (loc:loc) (x:id, t:typ option):BoundVar =
  let id = create_token loc (sid x) in
  match t with
  | None -> new BoundVar(id, id.``val``, new InferredTypeProxy())
  | Some t -> new BoundVar(id, id.``val``, create_type built_ins t)

let need_rel_chain (exp:exp):bool =
  match exp with
  | EOp (Bop op, [e1; e2], _) -> if is_rel_op op then is_rel_expr (skip_loc e1) else false
  | _ -> false

let rec create_chaining_rel (built_ins:BuiltIns) (loc:loc) (x:exp) (chain:ResizeArray<Expression>) (ops:ResizeArray<BinaryExpr.Opcode>) (opLocs:ResizeArray<IToken>) (prefixLimits:ResizeArray<Expression>) (first_op_tok:IToken ref):Expression =
  match x with
  | EOp (Bop op, [e1; e2], _) ->
      if is_rel_expr (skip_loc e1)
      then
        let e = create_chaining_rel built_ins (one_loc_of_exp loc e1) (skip_loc e1) chain ops opLocs prefixLimits first_op_tok in
        let left = chain.Item(chain.Count-1) in
        let right = create_expression built_ins loc e2 in
        let tok = create_token loc (string_of_bop op) in
        // validate op against current operator chain
        match op with
            | BEq _ -> ()
            | BNe _ -> if ops.Contains BinaryExpr.Opcode.Neq then err "a chain cannot have more than one != operator"
            | BLt -> if (ops.Contains BinaryExpr.Opcode.Ge || ops.Contains BinaryExpr.Opcode.Gt) then err "this operator chain cannot continue with an ascending operator"
            | BLe -> if (ops.Contains BinaryExpr.Opcode.Ge || ops.Contains BinaryExpr.Opcode.Gt) then err "this operator chain cannot continue with an ascending operator"
            | BGt -> if (ops.Contains BinaryExpr.Opcode.Le || ops.Contains BinaryExpr.Opcode.Lt) then err "this operator chain cannot continue with a descending operator"
            | BGe -> if (ops.Contains BinaryExpr.Opcode.Le || ops.Contains BinaryExpr.Opcode.Lt) then err "this operator chain cannot continue with a descending operator"
            | _ -> err "expected relational expression"
        let op = bop2opcode op in
        chain.Add(right)
        ops.Add(op)
        opLocs.Add(tok)
        prefixLimits.Add(null)
        new BinaryExpr(tok, BinaryExpr.Opcode.And, e, new BinaryExpr(tok, op, left, right)) :> Expression
      else
        // base case (left-most)
        let left = create_expression built_ins loc e1 in
        let right = create_expression built_ins loc e2 in
        let tok = create_token loc (string_of_bop op) in
        let op = bop2opcode op in
        first_op_tok := tok;
        chain.Add(left)
        chain.Add(right)
        opLocs.Add(tok)
        ops.Add(op)
        prefixLimits.Add(null)
        new BinaryExpr(tok, op, left, right) :> Expression
  | _ -> err "expected relational expression"

// Create Dafny Expression
and create_expression (built_ins:BuiltIns) (loc:loc) (x:exp):Expression =
  try
    match x with
      | ELoc (loc, e) -> create_expression built_ins loc e
      | EVar (id, _) ->
          let tok = create_token loc (sid id) in
          new NameSegment(tok, tok.``val``, null) :> Expression
      | EInt num ->
           let tok = create_token loc ((num:bigint).ToString ()) in
           new LiteralExpr(tok, num) :> Expression
      | EReal s ->
          let str = Util.RemoveUnderscores(s) in
          let d = get_dec loc str in
          let tok = create_token loc s in
          new LiteralExpr(tok, d) :> Expression
      | EBitVector _ -> notImplemented "bit vector support"
      | EBool b ->
          let tok = create_token loc (string b) in
          new LiteralExpr(tok, b) :> Expression
      | EString s ->
          let tok = create_token loc s in
          new StringLiteralExpr(tok, s, false) :> Expression
      | EOp (Uop UReveal, [EVar (x, _)], _) ->
          let tok = create_token loc ("reveal_" + (sid x)) in
          let exp = new NameSegment(tok, tok.``val``, null) in
          let openParen = create_token loc "(" in
          new ApplySuffix(openParen, exp, new ResizeArray<Expression>()) :> Expression
      | EOp (Uop (UNot _), [e], _) ->
          let tok = create_token loc "!" in
          let exp = create_expression built_ins loc e in
          new UnaryOpExpr(tok, UnaryOpExpr.Opcode.Not, exp) :> Expression
      | EOp (Uop UNeg, [e], _) ->
          let tok = create_token loc "-" in
          let exp = create_expression built_ins loc e in
          new NegationExpression(tok, exp) :> Expression
      | EOp (Uop (UIs x), [e], _) ->
          let exp = create_expression built_ins loc e in
          let id = create_token loc (sid x + "?") in
          new ExprDotName(id, exp, id.``val``, null) :> Expression
      | EOp (Uop (UReveal | UOld | UConst | UGhostOnly | UToOperand | UCustom _), [_], _) -> internalErr "unary operator"
      | EOp (Uop _, ([] | (_::_::_)), _) -> internalErr "unary operator"
      | EOp (Bop op, [e1; e2], _) ->
          if need_rel_chain x
          then
            let chain = new ResizeArray<Expression>() in
            let ops = new ResizeArray<BinaryExpr.Opcode>() in
            let opLocs = new ResizeArray<IToken>() in
            let prefix_limits = new ResizeArray<Expression>() in
            let (first_op_tok:IToken ref) = ref null in
            let e = create_chaining_rel built_ins loc x chain ops opLocs prefix_limits first_op_tok in
            new ChainingExpression(!first_op_tok, chain, ops, opLocs, prefix_limits) :> Expression
          else
              let tok = create_token loc (string_of_bop op) in
              let opcode = bop2opcode op in
              let e1 = create_expression built_ins loc e1 in
              let e2 = create_expression built_ins loc e2 in
              match op with
              | BExply -> new BinaryExpr(tok, opcode, e2, e1) :> Expression
              | _ -> new BinaryExpr(tok, opcode, e1, e2) :> Expression
      | EOp (Bop _, ([] | [_] | (_::_::_::_)), _) -> internalErr "binary operator"
      | EOp (TupleOp _, es, _) ->
          let tok = create_token loc "(" in
          let args = new ResizeArray<Expression>() in
          List.iter (fun x -> args.Add(create_expression built_ins loc x)) es
          if args.Count = 1 then new ParensExpression(tok, args.Item 0) :> Expression
          else
            let tmp = built_ins.TupleType(tok, args.Count, true) in
            new DatatypeValue(tok, BuiltIns.TupleTypeName(args.Count), BuiltIns.TupleTypeCtorNamePrefix + (string args.Count), args) :> Expression
      | EApply (e, _, es, _) when is_id e && id_of_exp e = (Id "seq") ->
          let tok = create_token loc "[" in
          let elements = new ResizeArray<Expression>() in
          List.iter (fun x -> elements.Add(create_expression built_ins loc x)) es
          new SeqDisplayExpr(tok, elements) :> Expression
      | EApply (e, _, es, _) when is_id e && id_of_exp e = (Id "set") ->
          let tok = create_token loc "{" in
          let elements = new ResizeArray<Expression>() in
          List.iter (fun x -> elements.Add(create_expression built_ins loc x)) es
          new SetDisplayExpr(tok, true, elements) :> Expression
      | EOp (Subscript, [e1; e2], _) ->
          let tok = create_token loc "[" in
          let e1 = create_expression built_ins loc e1 in
          let e2 = create_expression built_ins loc e2 in
          new SeqSelectExpr(tok, true, e1, e2, null) :> Expression
      | EOp (Update, [e1; e2; e3], _) ->
          let tok = create_token loc "[" in
          let e1 = create_expression built_ins loc e1 in
          let e2 = create_expression built_ins loc e2 in
          let e3 = create_expression built_ins loc e3 in
          new SeqUpdateExpr(tok, e1, e2, e3) :> Expression
      | EOp (Cond, [e1; e2; e3], _) ->
          let tok = create_token loc "if" in
          let e1 = create_expression built_ins loc e1 in
          let e2 = create_expression built_ins loc e2 in
          let e3 = create_expression built_ins loc e3 in
            new ITEExpr(tok, false, e1, e2, e3) :> Expression
      | EOp (FieldOp x, [e], _) ->
          let e = create_expression built_ins loc e in
          let id = create_token loc (sid x) in
          new ExprDotName(id, e, id.``val``, null) :> Expression
      | EOp (FieldUpdate x, [e1; e2], _) ->
          let tok = create_token loc "(" in
          let e1 = create_expression built_ins loc e1 in
          let e2 = create_expression built_ins loc e2 in
          let id = create_token loc (sid x) in
          let updates = new ResizeArray<IToken * string * Expression>() in
          updates.Add((id, id.``val``, e2))
          new DatatypeUpdateExpr(tok, e1, updates) :> Expression
      | EOp ((Subscript | Update | Cond | FieldOp _ | FieldUpdate _ | CodeLemmaOp | RefineOp | StateOp _ | OperandArg _), _, _) -> internalErr "EOp"
      | EApply (e, _, es, _) ->
          let x = match id_of_exp_opt e with Some x -> x | None -> Id "" in
          let tok = create_token loc (sid x) in
          if (sid x).Equals("int")
          then
            match es with
            | e::[] ->
                let e = create_expression built_ins loc e in
                new ConversionExpr(tok, e, new IntType()) :> Expression
            | _ -> err "casting to int takes one parameter"
          elif (sid x).Equals("real") then
            match es with
            | e::[] ->
                let e = create_expression built_ins loc e in
                new ConversionExpr(tok, e, new RealType()) :> Expression
            | _ -> err "casting to int takes one parameter"
          else
            let exp = new NameSegment(tok, tok.``val``, null) in
            let openParen = create_token loc "(" in
            let args = List.fold (fun (acc:ResizeArray<Expression>) (elem:exp) -> acc.Add(create_expression built_ins loc elem); acc) (new ResizeArray<Expression>()) es
            new ApplySuffix(openParen, exp, args) :> Expression
      | EBind (Forall, [], xs, ts, e, _) ->
          let tok = create_token loc "forall" in
          let bvars = new ResizeArray<BoundVar>() in
          List.iter (fun (x:formal) -> bvars.Add(create_bvar built_ins loc x)) xs
          let attrs = List.fold (fun (acc:Attributes) (es:exp list) -> create_attr built_ins loc ("trigger", es) acc) null ts in
          let body = create_expression built_ins loc e in
          new ForallExpr(tok, bvars, null, body, attrs) :> Expression
      | EBind (Exists, [], xs, ts, e, _) ->
          let tok = create_token loc "exists" in
          let bvars = new ResizeArray<BoundVar>() in
          List.iter (fun (x:formal) -> bvars.Add(create_bvar built_ins loc x)) xs
          let attrs = List.fold (fun (acc:Attributes) (es:exp list) -> create_attr built_ins loc ("trigger", es) acc) null ts in
          let body = create_expression built_ins loc e in
          new ExistsExpr(tok, bvars, null, body, attrs) :> Expression
      | EBind (Lambda, [], xs, ts, e, _) ->
          let tok = create_token loc "(" in
          let bvars = new ResizeArray<BoundVar>() in
          List.iter (fun (x:formal) -> bvars.Add(create_bvar built_ins loc x)) xs
          built_ins.CreateArrowTypeDecl(bvars.Count)
          let reads = new ResizeArray<FrameExpression>() in // no reads clauses for now
          let req = null in // no ensures clause for now
          let body = create_expression built_ins loc e in
          new LambdaExpr(tok, true, bvars, req, reads, body) :> Expression
      | EBind (BindLet, [ex], [x], [], e, _) ->
          let tok = create_token loc "var" in
          let bvar = create_bvar built_ins loc x in
          let left = new ResizeArray<CasePattern>() in
          let right = new ResizeArray<Expression>() in
          let e = create_expression built_ins loc e in
          left.Add(new CasePattern(bvar.tok, bvar))
          right.Add(create_expression built_ins loc ex)
          new LetExpr(tok, left, right, e, true, null) :> Expression
      | EBind (BindAlias, _, _, _, e, _) -> create_expression built_ins loc e
      | EBind (BindSet, [], xs, ts, e, _) ->
          notImplemented "BindSet"
      | EBind ((Forall | Exists | Lambda | BindLet | BindSet), _, _, _, _, _) -> internalErr "EBind"
      | _ -> internalErr (sprintf "unexpected create_expression %A" x)
  with err -> raise (LocErr (loc, err))

// TODO: Mismatch between Vale and Dafny definitions of attributes
and create_attr (built_ins:BuiltIns) (loc:loc) (x:string, es:exp list) (prev_attr:Attributes):Attributes =
  let x = create_token loc x in
  let openBrace = create_token loc "{" in
  let colon = create_token loc ":" in
  let closeBrace = create_token loc "}" in
  let args = new ResizeArray<Expression>() in
  List.iter (fun (exp:exp) -> args.Add(create_expression built_ins loc exp)) es
  new UserSuppliedAttributes(x, openBrace, colon, closeBrace, args, prev_attr) :> Attributes

let create_fattr (built_ins:BuiltIns) (loc:loc) (attr:attr) (prev_attr:Attributes):Attributes =
  match attr with
  | (Id "opaque", ([] | [EBool true])) ->
      create_attr built_ins loc ("opaque", []) prev_attr
  | (x,e) -> err ("unknown function attribute " + (sid x))

let rec create_pattrs (built_ins:BuiltIns) (loc:loc) (attrs:attrs):Attributes =
  match attrs with
  | [] -> null
  | (Id x, es)::t ->
      let prev = create_pattrs built_ins loc t in
      create_attr built_ins loc (x, es) prev
  | (x,e)::_ -> err ("unknown procedure attribute " + (sid x))

let create_local_var (built_ins:BuiltIns) (loc:loc) (x:id) (tOpt:typ option) (is_ghost:bool) =
  let id = create_token loc (sid x) in
  let t =
      match tOpt with
      | None -> new InferredTypeProxy() :> Type
      | Some s -> create_type built_ins s
  in
  new LocalVariable(id, id, id.``val``, t, is_ghost)

// Create Dafny Statement
let rec create_stmt (built_ins:BuiltIns) (loc:loc) (s:stmt):ResizeArray<Statement> =
  let stmts = new ResizeArray<Statement>() in
  try
    match s with
    | SLoc (loc, s) -> create_stmt built_ins loc s
    | SLabel _ -> err "unsupported feature: labels (unstructured code)"
    | SGoto _ -> err "unsupported feature: 'goto' (unstructured code)"
    | SReturn _ -> err "unsupported feature: 'return' (unstructured code)"
    | SAssume e -> // Assume no attributes
        let start_tok = create_token loc "assume" in
        let end_tok = create_token loc ";" in
        let exp = create_expression built_ins loc e in
        let s = new AssumeStmt(start_tok, end_tok, exp, null) :> Statement in
        stmts.Add(s)
        stmts
    | SAssert (attrs, e) -> // Assume no attributes
        let start_tok = create_token loc "assert" in
        let end_tok = create_token loc ";" in
        let exp = create_expression built_ins loc e in
        let attrs = if attrs.is_split then create_attr built_ins loc ("split_here",[]) null else null in
        let s = new AssertStmt(start_tok, end_tok, exp, null, attrs) :> Statement in
        stmts.Add(s)
        stmts
    | SCalc (op, contents, e) ->
        let start_tok = create_token loc "calc" in
        let end_tok = create_token loc "}" in
        let makeCalcOp op = CalcStmt.BinaryCalcOp(bop2opcode op) :> CalcStmt.CalcOp in
        let calcOp = makeCalcOp op in
        let resOp = ref calcOp in
        let checkOp nextOp =
          let maybeOp = (!resOp).ResultOp(nextOp) in
          if maybeOp = null then err "bad calc op" else
          resOp := maybeOp
          in
        let lines = new ResizeArray<Expression>() in
        let hints = new ResizeArray<BlockStmt>() in
        let stepOps = new ResizeArray<CalcStmt.CalcOp>() in
        let attrs = null in
        let len = List.length contents in
        let addContents {calc_exp = e; calc_op = op; calc_hints = chs} =
          let exp = create_expression built_ins loc e in
          lines.Add(exp)
          if lines.Count = len then lines.Add(exp) // Dafny expects redundant last expression
          let subhints = new ResizeArray<Statement>() in
          let start_tok = create_token loc "{" in
          let end_tok = create_token loc "}" in
          List.iter (fun ss -> subhints.Add(create_block_stmt built_ins loc ss)) chs
          hints.Add(new BlockStmt(start_tok, end_tok, subhints))
          let stepOp = makeCalcOp op in
          checkOp stepOp
          stepOps.Add(stepOp)
          in
        List.iter addContents contents
        lines.Add(create_expression built_ins loc e)
        let s = new CalcStmt(start_tok, end_tok, calcOp, lines, hints, stepOps, attrs) in
        stmts.Add(s)
        stmts
    | SVar (x, tOpt, _, g, a, eOpt) ->
        let is_ghost:bool = var_storage_to_bool g in
        let start_tok =
            if is_ghost then create_token loc "ghost"
            else create_token loc "var" in
        let var = create_local_var built_ins loc x tOpt is_ghost in
        let lhss:ResizeArray<LocalVariable> = new ResizeArray<LocalVariable>() in
        let end_tok = create_token loc ";" in
        var.Attributes <- null;
        lhss.Add(var)
        match eOpt with
        | None ->
            let s = new VarDeclStmt(start_tok, end_tok, lhss, null) :> Statement in
            stmts.Add(s)
            stmts
        | Some e ->
            let assign_tok = create_token loc ":=" in
            let rhss:ResizeArray<AssignmentRhs> = new ResizeArray<AssignmentRhs>() in
            let ies = new ResizeArray<Expression>() in
            let update = new UpdateStmt(assign_tok, end_tok, ies, rhss) in
            rhss.Add(new ExprRhs(create_expression built_ins loc e))
            ies.Add(new AutoGhostIdentifierExpr(var.Tok, var.Name))
            let s = new VarDeclStmt(start_tok, end_tok, lhss, update) :> Statement in
            stmts.Add(s)
            stmts
    | SAlias _ -> internalErr "SAlias"
    | SAssign ([], e) ->
        let exp = create_expression built_ins loc e in
        let end_tok = create_token loc ";" in
        let lhss = new ResizeArray<Expression>() in
        let rhss = new ResizeArray<AssignmentRhs>() in
        rhss.Add(new ExprRhs(exp, null))
        let s = new UpdateStmt(exp.tok, end_tok, lhss, rhss) :> Statement in
        stmts.Add(s)
        stmts
    | SAssign (lhss, e) when List.forall (fun (x, d) -> d = None) lhss ->
        let exp = create_expression built_ins loc e in
        let assign_tok = create_token loc ":=" in
        let end_tok = create_token loc ";" in
        let get_expr (lhs:lhs):Expression =
          match lhs with
          | (x, None) -> create_expression built_ins loc (evar x)
          | _ -> internalErr "SAssign"
        let left = new  ResizeArray<Expression>() in
        let right = new ResizeArray<AssignmentRhs>() in
        List.iter (fun x -> left.Add(get_expr x)) lhss
        right.Add(new ExprRhs(exp, null))
        let s = new UpdateStmt(assign_tok, end_tok, left, right) :> Statement in
        stmts.Add(s)
        stmts
    | SAssign (lhss, e) when List.forall (fun (x, d) -> d <> None) lhss ->
        let is_ghost = true in
        let start_tok = create_token loc "ghost" in
        let assign_tok = create_token loc ":=" in
        let end_tok = create_token loc ";" in
        let get_var (lhs:lhs):LocalVariable =
          match lhs with
          | (x, Some (tOpt, _)) -> create_local_var built_ins loc x tOpt true
          | _ -> internalErr "SAssign"
        let left = new ResizeArray<LocalVariable>() in
        let ies = new ResizeArray<Expression>() in
        let right = new ResizeArray<AssignmentRhs>() in
        List.iter (fun x -> let v = get_var x in left.Add(v); ies.Add(new AutoGhostIdentifierExpr(v.Tok, v.Name))) lhss
        right.Add(new ExprRhs(create_expression built_ins loc e))
        let update = new UpdateStmt(assign_tok, end_tok, ies, right) in
        let s = new VarDeclStmt(start_tok, end_tok, left, update) :> Statement in
        stmts.Add(s)
        stmts
    | SAssign _ ->
        List.iter (fun x -> stmts.AddRange(create_stmt built_ins loc x)) (eliminate_assign_lhss s)
        stmts
    | SLetUpdates _ -> internalErr "SLetUpdates"
    | SBlock ss -> notImplemented "block"
    | SQuickBlock _ -> internalErr "quick_block"
    | SIfElse (_, e, ss1, ss2) ->
        let tok = create_token loc "if" in
        let guard = create_expression built_ins loc e in
        let thn = create_block_stmt built_ins loc ss1 in
        let els = (create_block_stmt built_ins loc ss2) :> Statement in
        let s = new IfStmt(tok, els.EndTok, false, guard, thn, els) :> Statement in
        stmts.Add(s)
        stmts
    | SWhile (e, invs, (l, ed), ss) ->
        let tok = create_token loc "while" in
        let guard = create_expression built_ins loc e in
        let invariants = new ResizeArray<MaybeFreeExpression>() in
        let decreases = new ResizeArray<Expression>() in
        List.iter (fun (loc, exp) -> invariants.Add(new MaybeFreeExpression(create_expression built_ins loc exp, false, null))) invs
        match ed with
        | [] -> decreases.Add(new WildcardExpr(create_token loc "*"))
        | es -> List.iter (fun x -> decreases.Add(create_expression built_ins l x)) es
        let body = create_block_stmt built_ins loc ss in
        let s = new WhileStmt(tok, body.EndTok, guard, invariants, new Specification<Expression>(decreases, null), new Specification<FrameExpression>(null, null), body) :> Statement in
        stmts.Add(s)
        stmts
    | SForall (xs, ts, ex, e, ss) ->
        let tok = create_token loc "forall" in
        let bvars = new ResizeArray<BoundVar>() in
        List.iter (fun (x:formal) -> bvars.Add(create_bvar built_ins loc x)) xs
        let attrs = List.fold (fun (acc:Attributes) (es:exp list) -> create_attr built_ins loc ("trigger", es) acc) null ts in
        let range =
          match skip_loc ex with
          | EBool true -> new LiteralExpr(tok, true) :> Expression
          | _ -> create_expression built_ins loc ex
        let ens = new ResizeArray<MaybeFreeExpression>() in
        ens.Add(new MaybeFreeExpression(create_expression built_ins loc e, false))
        let block = create_block_stmt built_ins loc ss in
        let s = new ForallStmt(tok, block.EndTok, bvars, attrs, range, ens, block) :> Statement in
        stmts.Add(s)
        stmts
    | SExists (xs, ts, e) ->
        let is_ghost = true in
        let start_tok = create_token loc "ghost" in
        let assign_tok = create_token loc ":|" in
        let end_tok = create_token loc ";" in
        let e = create_expression built_ins loc e in
        let get_var (x:id, tOpt:typ option):LocalVariable = create_local_var built_ins loc x tOpt is_ghost in
        let left = new ResizeArray<LocalVariable>() in
        let attrs = List.fold (fun (acc:Attributes) (es:exp list) -> create_attr built_ins loc ("trigger", es) acc) null ts in
        let ies = new ResizeArray<Expression>() in
        List.iter (fun x -> let v = get_var x in left.Add(v); ies.Add(new IdentifierExpr(v.Tok, v.Name))) xs
        let update =  new AssignSuchThatStmt(assign_tok, end_tok, ies, e, null, attrs) in
        let s = new VarDeclStmt(start_tok, end_tok, left, update) :> Statement in
        stmts.Add(s)
        stmts
  with err -> raise (LocErr (loc, err))
and create_block_stmt (built_ins:BuiltIns) (loc:loc) (xs:stmt list):BlockStmt =
  let body_start = create_token loc "{" in
  let body_end = create_token loc "}" in
  let body = List.fold (fun (acc:ResizeArray<Statement>) (elem:stmt) -> acc.AddRange(create_stmt built_ins loc elem); acc) (new ResizeArray<Statement>()) xs
  new BlockStmt(body_start, body_end, body)

let build_fun (built_ins:BuiltIns) (loc:loc) (f:fun_decl):Function =
  let is_function_method = not (ghost_to_bool f.fghost) in
  let typeArgs = new ResizeArray<TypeParameter>() in // no type arguments / generic parameters
  let attrs = List.fold (fun (acc:Attributes) (elem:attr) -> create_fattr built_ins loc elem acc) null f.fattrs in
  let tok = create_token loc (sid f.fname) in
  let formals = create_formals built_ins loc f.fargs in
  let resultType = create_type built_ins f.fret in
  let reqs = new ResizeArray<Expression>() in // Functions do not have requires clauses
  let ens = new ResizeArray<Expression>() in // Functions do not have ensures clauses
  let reads = new ResizeArray<FrameExpression>() in // Functions do not have reads clauses
  let decreases = new ResizeArray<Expression>() in // Function do not have decreases clauses
  let body =
    match f.fbody with
    | None -> internalErr "function body missing"
    | Some e -> create_expression built_ins loc e
    in

  // Assuming is not static or protected
  let f =
    Function(
      tok, sid f.fname, false, false, not is_function_method, typeArgs, formals, null, resultType,
      reqs, reads, ens, new Specification<Expression>(decreases, null), body, attrs, null) in
  f.BodyStartTok <- create_token loc "{";
  f.BodyEndTok <- create_token loc "}";
  built_ins.CreateArrowTypeDecl(formals.Count);
  f

let build_lemma (built_ins:BuiltIns) (loc:loc) (p:proc_decl):Lemma =
  let tok = create_token loc (sid p.pname) in
  let typeArgs = new ResizeArray<TypeParameter>() in // no type arguments / generic parameters
  let ins = create_pformals built_ins loc p.pargs true in
  let outs = create_pformals built_ins loc p.prets false in
  let reqs = new ResizeArray<MaybeFreeExpression>() in
  let mods = new ResizeArray<FrameExpression>() in // Empty, no modifies
  let ens = new ResizeArray<MaybeFreeExpression>() in
  let decs = new ResizeArray<Expression>() in // Empty, no decreases
  let decAttrs:Attributes = null in
  let modAttrs:Attributes = null in
  let gen_spec (x:(loc * spec)):unit =
    match x with
    | (loc, Requires (_, e)) -> reqs.Add(new MaybeFreeExpression(create_expression built_ins loc e, false))
    | (loc, Ensures (_, e)) -> ens.Add(new MaybeFreeExpression(create_expression built_ins loc e, false, null))
    | (loc, Modifies _) -> () //no-op
    | (_, SpecRaw _) -> internalErr "SpecRaw"
  List.iter (gen_spec) p.pspecs
  let attrs = create_pattrs built_ins loc p.pattrs in
  let body_start = create_token loc "{" in
  let body_end = create_token loc "}" in
  let body =
    match p.pbody with
    | None -> internalErr "procedure body missing"
    | Some e -> create_block_stmt built_ins loc e
    in

  // Assuming not static
  let l = Lemma(tok, sid p.pname, false, typeArgs, ins, outs, reqs, new Specification<FrameExpression>(mods, modAttrs), ens, new Specification<Expression>(decs, decAttrs), body, attrs, null) in
  l.BodyStartTok <- body_start;
  l.BodyEndTok <- body_end;
  l

let create_dafny_decl (mdl:LiteralModuleDecl) (built_ins:BuiltIns) (loc:loc, d:decl):unit =
  let dmod:DefaultModuleDecl = mdl.ModuleDef :?> DefaultModuleDecl in
  let default_class:DefaultClassDecl = (dmod.TopLevelDecls.Item 0) :?> DefaultClassDecl in
  try
    match d with
    | DVerbatim (_, lines) ->
        let s = String.concat "" (List.map (fun s -> s + System.Environment.NewLine) lines) in
        let errCount = DafnyDriver.Parse_Verbatim_Block(s, loc.loc_file, loc.loc_line, mdl, built_ins) in
        if errCount > 0 then internalErr (sprintf "%i parse errors detected within verbatim block in %s at (%i,%i)/n" errCount loc.loc_file loc.loc_line loc.loc_col)
    | DPragma _ -> ()
    | DVar _ -> ()
    | DConst _ -> ()
    | DType _ -> ()
    | DOperandType _ -> ()
    | DUnsupported _ -> ()
    | DFun f -> default_class.Members.Add(build_fun built_ins loc f)
    | DProc p ->
        gen_lemma_sym_count := 0;
        match p.pghost with
        | Ghost -> default_class.Members.Add(build_lemma built_ins loc p)
        | NotGhost -> notImplemented "NotGhost procedure block handling"
  with err -> raise (LocErr (loc, err))

let add_includes (dmod:DefaultModuleDecl) (included_file:string):unit =
  let full_path = System.IO.Path.GetFullPath(included_file) in
  dmod.Includes.Add(new Include(create_dummy_token included_file, "", included_file, full_path))

// Top level decl building see Parser.Dafny()
let build_dafny_program (mdl:LiteralModuleDecl) (built_ins:BuiltIns) (ins:string list) (ds:decls):unit =
  let dmod:DefaultModuleDecl = mdl.ModuleDef :?> DefaultModuleDecl in
  let default_class = new DefaultClassDecl(dmod, new ResizeArray<MemberDecl>()) in
  dmod.TopLevelDecls.Add(default_class)
  // Add included files
  List.iter (add_includes dmod) ins
  // Build dafny decls
  List.iter (create_dafny_decl mdl built_ins) ds
