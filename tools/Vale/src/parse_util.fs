module Parse_util

open Ast
open Ast_util
open Microsoft.FSharp.Text.Lexing

exception ParseErr of string
let parse_err (s:string):'a = raise (ParseErr s)
let assrt b = if b then () else err "assert failure"
let file (lexbuf:LexBuffer<_>) = lexbuf.StartPos.FileName
let line (lexbuf:LexBuffer<_>) = lexbuf.StartPos.Line
let col (lexbuf:LexBuffer<_>) = lexbuf.StartPos.Column + 1
let curLoc (lexbuf:LexBuffer<_>):loc = { loc_file = file lexbuf; loc_line = line lexbuf; loc_col = col lexbuf; loc_pos = lexbuf.StartPos.AbsoluteOffset }
let parse_require b = if b then () else parse_err "parse requirement violated"

let setInitialPos (lexbuf:LexBuffer<_>) filename = lexbuf.EndPos <- { pos_bol = 0; pos_fname = filename; pos_cnum = 0; pos_lnum = 1 }

let rec exp2id (e:exp) (i:id):id =
  match i with
  | Id s ->
    (
      match e with
      | ELoc(_, EVar (Id r, _)) ->
        Id (r + "." + s)
      | ELoc(_, EOp (FieldOp (Id r), [ee], _)) ->
        exp2id ee (Id (r + "." + s))
      | _ -> parse_err "malformed qualified function/method name"
    )
  | _ -> parse_err "malformed qualified function/method name"
