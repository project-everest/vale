module Ast

open Microsoft.FSharp.Math

type loc = {loc_file:string; loc_line:int; loc_col:int; loc_pos:int}

type id = Id of string | Reserved of string | Operator of string

type kind =
| KType of bigint
| KDependent of id

type bool_or_prop = BpBool | BpProp
type bnd = Int of bigint | NegInf | Inf
type typ =
| TName of id
| TApply of id * typ list
| TBool of bool_or_prop
| TInt of bnd * bnd
| TTuple of typ list
| TFun of fun_typ
| TDependent of id // the id is an expression-level variable, not a type-level variable
| TVar of id * kind option
and fun_typ = typ list * typ

type ghost = Ghost | NotGhost
type stmt_modifier = SmPlain | SmGhost | SmInline
type formal = id * typ option

type exp_call = CallGhost | CallLemma | CallInline | CallOutline

type uop =
| UNot of bool_or_prop | UNeg | UOld | UIs of id
| UConst
| UReveal | UFStarNameString | UGhostOnly | UToOperand
| UCall of exp_call
| UCustom of string

type bop =
| BEquiv | BImply | BExply | BAnd of bool_or_prop | BOr of bool_or_prop
| BEq of bool_or_prop | BNe of bool_or_prop | BLt | BGt | BLe | BGe | BIn
| BAdd | BSub | BMul | BDiv | BMod
| BOldAt
| BCustom of string

type op =
| Uop of uop
| Bop of bop
| TupleOp of typ list option
| Subscript
| Update
| Cond
| FieldOp of id
| FieldUpdate of id
| CodeLemmaOp // one expression for code, a different expression for lemmas
| RefineOp // one expression for abstract, one expression for abstract with optional oldness, one expression for refined
| StateOp of id * string * typ // example: (eax, "reg", int) for va_get_reg(EAX, ...exps..., state):int
| OperandArg of id * string * typ

type bindOp =
| Forall
| Exists
| Lambda
| BindLet // x := e
| BindAlias // x @= eax (different from x := eax in treatment of old(x))
| BindSet

type tqual = TqExplicit | TqImplicit
type cast = Upcast | Downcast
type exp =
| ELoc of loc * exp
| EVar of id * typ option
| EInt of bigint
| EReal of string
| EBitVector of int * bigint
| EBool of bool
| EString of string
| EOp of op * exp list * typ option
| EApply of exp * (tqual * typ) list option * exp list * typ option
| EBind of bindOp * exp list * formal list * triggers * exp * typ option
| ECast of cast * exp * typ
| ELabel of loc * exp // marker for exp that needs to be wrapped in a loc label

and triggers = exp list list

type attr = id * exp list
type attrs = attr list

type var_alias =
| AliasThread // thread-local variable, such as register
| AliasLocal // procedure-local variable
type mutability = Mutable | Immutable
type var_storage =
| XGhost // ghost, no storage space
| XPhysical // ordinary non-ghost variable (supplies its own storage space)
| XOperand // procedure operand argument (procedure caller determines storage)
| XInline // inline procedure argument (procedure caller supplies constant that gets inlined)
| XAlias of var_alias * exp // variable is a name for some other storage
| XState of exp // top-level declaration of member of the state (e.g. a register)

type assert_attrs = {is_inv:bool; is_split:bool; is_refined:bool; is_quicktype:bool option}
type quick_info = {qsym:string; qmods:id list}
type lhs = id * (typ option * ghost) option // TODO: we only allow Ghost here, so no need to mention possibility of NotGhost; can just be id * formal option
type stmt =
| SLoc of loc * stmt
| SLabel of id
| SGoto of id
| SReturn
| SAssume of exp
| SAssert of assert_attrs * exp
| SCalc of bop * calcContents list * exp
| SVar of id * typ option * mutability * var_storage * attrs * exp option
| SAlias of id * id
| SAssign of lhs list * exp
| SLetUpdates of formal list * stmt // used to turn imperative updates into functional 'let' assignments
| SBlock of stmt list
| SIfElse of stmt_modifier * exp * stmt list * stmt list
| SWhile of exp * (loc * exp) list * (loc * exp list) * stmt list
| SForall of formal list * triggers * exp * exp * stmt list
| SExists of formal list * triggers * exp
and calcContents = {calc_exp:exp; calc_op:bop; calc_hints:stmt list list}

type is_refined = Refined | Unrefined
type mod_kind = Read | Modify | Preserve
type raw_spec_kind =
| RRequires of is_refined
| REnsures of is_refined
| RRequiresEnsures
| RModifies of mod_kind

type lets =
| LetsVar of id * typ option * exp
| LetsAlias of id * id

type spec_exp =
| SpecExp of exp
| SpecLet of id * typ option * exp

type spec_raw = // spec before desugaring
| RawSpec of raw_spec_kind * (loc * spec_exp) list
| Lets of (loc * lets) list

type spec =
| Requires of is_refined * exp
| Ensures of is_refined * exp
| Modifies of mod_kind * exp
| SpecRaw of spec_raw

type type_infer = InferExplicit | InferImplicit
type tformal = id * kind * type_infer

type inline_kind = Outline | Inline
type inout = In | Out | InOut
type pformal = id * typ * var_storage * inout * attrs

type fun_decl =
  {
    fname:id;
    fghost:ghost;
    ftargs:tformal list;
    fargs:formal list;
    fret_name:id option;
    fret:typ;
    fspecs:(loc * spec) list;
    fbody:exp option;
    fattrs:attrs;
  }

type proc_decl =
  {
    pname:id;
    pghost:ghost;
    pinline:inline_kind;
    ptargs:tformal list;
    pargs:pformal list;
    prets:pformal list;
    pspecs:(loc * spec) list;
    pbody:stmt list option;
    pattrs:attrs;
  }

type prag =
| ModuleName of string
| ResetOptions of string

type operand_typ =
| OT_Const
| OT_Name of id
| OT_State of inout * id

type decl =
| DType of id * tformal list option * kind * typ option * attrs
| DOperandType of id * pformal list option * typ * typ option * operand_typ list
| DVar of id * typ * var_storage * attrs
| DConst of id * typ
| DFun of fun_decl
| DProc of proc_decl
| DUnsupported of id * string option
| DVerbatim of attrs * string list
| DPragma of prag

type decls = (loc * decl) list

type include_decl = {inc_loc:loc; inc_attrs:attrs; inc_path:string}

let expAt (l:loc) (e:exp):exp = ELoc (l, e)
let stmtAt (l:loc) (s:stmt):stmt list = [SLoc (l, s)]

type id_local = {local_in_param:bool; local_exp:exp; local_typ:typ option} // In parameters are read-only and refer to old(state)
type id_info =
| GhostLocal of mutability * typ option
| ProcLocal of id_local
| ThreadLocal of id_local
| InlineLocal of typ option
| OperandLocal of inout * typ
| StateInfo of string * exp list * typ
| OperandAlias of id * id_info
