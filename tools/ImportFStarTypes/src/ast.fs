module Ast

open Microsoft.FSharp.Math

type loc = {loc_file:string; loc_line:int; loc_col:int; loc_pos:int}

type raw_exp =
| RLet of loc
| RFun of loc
| RArrow of loc
| RTildeArrow of loc
| RDollarDollar of loc
| RPlus of loc
| RRefine of loc
| RLtGt of loc
| RMeta of loc
| RComma of loc
| RAttribute of loc
| RAttributes of loc
| RDecreases of loc
| RDollar of loc
| RHash of loc
| RColon of loc
| RSColon of loc
| RSemi of loc
| RMatch of loc
| RWith of loc
| RBar of loc
| RHashDot of loc
| RType of loc
| RAscribed of loc
| RPattern of loc
| RDecl of loc * string
| RQualifier of loc * string
| RUnitValue of loc
| RInt of loc * bigint
| RString of loc * string
| RId of loc * string
| RList of raw_exp list

type id = { name:string option; index:int option }

type univ =
| UId of id
| UInt of bigint
| UPlus of univ * univ
| UMax of univ list

type aqual = Explicit | Implicit | Equality

// F* expressions
type f_exp =
| EId of id
| EInt of bigint
| EUnitValue
| EBool
| EProp
| EType of univ
| EComp of f_exp * f_exp * f_exp list
| EApp of f_exp * (aqual * f_exp) list
| EAppUnivs of f_exp * univ list
| EArrow of aqual * id * f_exp * f_exp
| ERefine of id * f_exp * f_exp
| ETyped of f_exp * f_exp
| EAscribed of f_exp * f_exp
| EPattern of f_exp list list * f_exp
| ELet of f_binder * f_exp * f_exp
| EFun of f_binder list * f_exp
| EUnsupported of string
and f_binder = aqual * id * f_exp option

type f_decl = {
  f_name:string;
  f_qualifiers:string list;
  f_category:string;
  f_udecls:id list;
  f_binders:f_binder list;
  f_typ:f_exp;
  f_body:f_exp option;
}

// Vale kinds, types, and expressions
type v_kind =
| KType of bigint
| KDependent of string

type bool_or_prop = BpBool | BpProp
type v_type =
| TName of string
| TInt of bigint // used by int_range
| TApply of string * v_type list
| TFun of v_type list * v_type

type v_exp =
| VId of string
| VInt of bigint
| VApp of string * v_type list option * v_exp list
| VLet of string * v_type * v_exp * v_exp
//| VFun of v_binder list * v_exp
//| VUnsupported of string
//and v_binder = aqual * id * v_exp option

type effect = EffectLemma | EffectGhost | EffectOther

(*
type v_decl = {
  v_name:string;
  v_qualifiers:string list;
  v_category:string;
  v_udecls:id list;
  v_binders:v_binder list;
  v_type:v_type;
  v_body:v_exp option;
}
*)
