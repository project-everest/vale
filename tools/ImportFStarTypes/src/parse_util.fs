module Parse_util

open Ast
open Microsoft.FSharp.Text.Lexing

exception ParseErr of string
let parse_err (s:string):'a = raise (ParseErr s)
let file (lexbuf:LexBuffer<_>) = lexbuf.StartPos.FileName
let line (lexbuf:LexBuffer<_>) = lexbuf.StartPos.Line
let col (lexbuf:LexBuffer<_>) = lexbuf.StartPos.Column + 1
let curLoc (lexbuf:LexBuffer<_>):loc = { loc_file = file lexbuf; loc_line = line lexbuf; loc_col = col lexbuf; loc_pos = lexbuf.StartPos.AbsoluteOffset }
let parse_require b = if b then () else parse_err "parse requirement violated"

let setInitialPos (lexbuf:LexBuffer<_>) filename = lexbuf.EndPos <- { pos_bol = 0; pos_fname = filename; pos_cnum = 0; pos_lnum = 1 }

