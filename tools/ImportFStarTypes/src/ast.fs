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

type exp =
| EId of id
| EInt of bigint
| EUnitValue
| EBool
| EProp
| EType of univ
| EComp of exp * exp * exp list
| EApp of exp * (aqual * exp) list
| EAppUnivs of exp * univ list
| EArrow of aqual * id * exp * exp
| ERefine of id * exp * exp
| ETyped of exp * exp
| EAscribed of exp * exp
| EPattern of exp list list * exp
| ELet of binder * exp * exp
| EFun of binder list * exp
| EUnsupported of string
and binder = aqual * id * exp option

type decl =
  {
    d_name:string;
    d_qualifiers:string list;
    d_category:string;
    d_udecls:id list;
    d_binders:binder list;
    d_typ:exp;
    d_body:exp option;
  }
