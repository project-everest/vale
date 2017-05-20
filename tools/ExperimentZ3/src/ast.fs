module Ast

exception ParseErr of string
let parse_err (s:string):'a = raise (ParseErr s)

type quant = Forall | Exists
type exp =
| Token of string
| Exps of exps
| Assert of exp * string option
| True
| False
| And of exp list
| Or of exp list
| Not of exp
| Implies of exp * exp
| Quant of quant * (string * exp) list * exp * exp list list * string option * string option
and exps = exp list

type query =
| Unparsed of exps
| Parsed of exps
