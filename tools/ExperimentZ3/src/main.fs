open Ast
open Parse
open Microsoft.FSharp.Text.Lexing

exception InternalErr of string
let setInitialPos (lexbuf:LexBuffer<_>) filename = lexbuf.EndPos <- { pos_bol = 0; pos_fname = filename; pos_cnum = 0; pos_lnum = 1 }

let rec string_of_exp (e:exp):string =
  match e with
  | Token s -> s
  | Exps es -> "(" + (string_of_exps es) + ")"
  | _ -> raise (InternalErr (sprintf "string_of_exp %A" e))
and string_of_exps (es:exp list):string =
  String.concat " " (List.map string_of_exp es)

let line_len = 100 in
let rec print_exp (indent:string) (pos:int) (e:exp):int =
  match e with
  | Token s ->
      let pos2 = pos + (String.length s) in
      if pos > 0 && pos2 > line_len then
        printfn "";
        printf "%s%s" indent s;
        0
      else
        printf "%s" s;
        pos2
  | Exps es ->
      printf "(";
      let pos = pos + 1 in
      let indent = indent + " " in
      let print_exp_space (space:bool, pos:int) (e:exp):(bool * int) =
        let pos = if space then (printf " "; pos + 1) else pos in
        (true, print_exp indent pos e)
        in
      let (_, pos) = List.fold print_exp_space (false, pos) es in
      printf ")";
      (pos + 1)
  | _ -> raise (InternalErr (sprintf "print_exp %A" e))
let printn_exp (e:exp):unit =
//  printfn "%s" (string_of_exp e)
  let _ = print_exp "" 0 e in
  printfn ""

let rec parse_exp (e:exp):exp =
  match e with
  | Token "true" -> True
  | Token "false" -> False
  | Token _ -> e
  | Exps es->
    (
      let es = List.map parse_exp es in
      let quant q fs e attrs =
        let formal e = match e with Exps [Token s; e] -> (s, e) | _ -> parse_err (sprintf "forall formal %A" e) in
        let rec parse_attrs attrs =
          match attrs with
          | (Token ":pattern")::(Exps ps)::attrs ->
              let (pats, qid, w) = parse_attrs attrs in (ps::pats, qid, w)
          | (Token ":qid")::(Token s)::attrs ->
              let (pats, qid, w) = parse_attrs attrs in (pats, Some s, w)
          | (Token ":weight")::(Token s)::attrs ->
              let (pats, qid, w) = parse_attrs attrs in (pats, qid, Some s)
          | [] -> ([], None, None)
          | _ -> parse_err (sprintf "forall.parse_attrs %A" attrs)
          in
        let (pats, qid, weight) = parse_attrs attrs in
        Quant (q, List.map formal fs, e, pats, qid, weight)
        in
      match es with
      | [Token "assert"; Exps [Token "!"; e; Token ":named"; Token s]] -> Assert (e, Some s)
      | [Token "assert"; e] -> Assert (e, None)
      | ((Token "and")::es) -> And es
      | ((Token "or")::es) -> Or es
      | [Token "not"; e] -> Not e
      | [Token "implies"; e1; e2] -> Implies (e1, e2)
      | [Token "forall"; Exps fs; Exps ((Token "!")::e::attrs)] -> quant Forall fs e attrs
      | [Token "forall"; Exps fs; e] -> quant Forall fs e []
      | [Token "exists"; Exps fs; Exps ((Token "!")::e::attrs)] -> quant Forall fs e attrs
      | [Token "exists"; Exps fs; e] -> quant Forall fs e []
      | _ -> Exps es
    )
  | _ -> raise (InternalErr (sprintf "parse_exp %A" e))

let rec unparse_exp (e:exp):exp =
  let r = unparse_exp in
  let rs = List.map unparse_exp in
  match e with
  | Token _ -> e
  | Exps es -> Exps (rs es)
  | Assert (e, None) -> Exps [Token "assert"; r e]
  | Assert (e, Some s) -> Exps [Token "assert"; Exps [Token "!"; r e; Token ":named"; Token s]]
  | True -> Token "true"
  | False -> Token "false"
  | And es -> Exps ((Token "and")::(rs es))
  | Or es -> Exps ((Token "or")::(rs es))
  | Not e -> Exps [Token "not"; r e]
  | Implies (e1, e2) -> Exps [Token "implies"; r e1; r e2]
  | Quant (q, fs, e, pats, qid, weight) ->
    (
      let fs = List.map (fun (x, e) -> Exps [Token x; r e]) fs in
      let weight = match weight with None -> [] | Some s -> [Token ":weight"; Token s] in
      let pats = List.collect (fun ps -> [Token ":pattern"; Exps ps]) pats in
      let qid = match qid with None -> [] | Some s -> [Token ":qid"; Token s] in
      let q = Token (match q with Forall -> "forall" | Exists -> "exists") in
      let attrs = weight @ pats @ qid in
      match attrs with
      | [] -> Exps [q; Exps (rs fs); r e]
      | _ -> Exps [q; Exps (rs fs); Exps ((Token "!")::(r e)::(rs attrs))]
    )

let query_to_parsed (q:query):exp list =
  match q with
  | Parsed es -> es
  | Unparsed es -> List.map parse_exp es

let query_to_unparsed (q:query):exp list =
  match q with
  | Parsed es -> List.map unparse_exp es
  | Unparsed es -> es

let query_from_parsed (es:exp list):query = Parsed es
let query_from_unparsed (es:exp list):query = Unparsed es

let sort_exps (q:query):unit =
  let es = query_to_parsed q in
  let (ds, es) =
    List.partition (fun e ->
        match e with
        | Exps ((Token ("set-option" | "declare-sort" | "declare-fun" | "define-fun" | "declare-datatypes"))::_) -> true
        | _ -> false
      )
      es in
  let (asserts, es) = List.partition (fun e -> match e with | Assert _ -> true | _ -> false) es in
  let ds = List.map unparse_exp ds in
  let es = List.map unparse_exp es in
  let get_option_string e = match e with Some s -> s | _ -> "_" in
  let get_assert_string e = match e with Assert (_, Some s) -> s | _ -> "_" in
  let compare_e e1 e2 = Operators.compare (get_assert_string e1) (get_assert_string e2) in
  let asserts = List.sortWith compare_e asserts in
  List.iter printn_exp ds;
  List.iter (fun e ->
      match e with
      | Assert (_, sOpt) ->
          printfn ";;assert %s" (get_option_string sOpt);
          printfn "                                                                     %s" (string_of_exp (unparse_exp e))
      | _ -> ()
    )
    asserts;
  List.iter printn_exp es;
  //let es = List.map unparse_exp es in
  //List.iter printn_exp es;
  ()

let remove_exps (q:query):query =
  let es = query_to_parsed q in
  let f e =
    match e with
    | Exps [Token "set-option"; Token ":produce-unsat-cores"; Token "true"] -> false
    | Assert (_, Some s)
        when  s.StartsWith("token_correspondence_")
           || s.StartsWith("subterm_ordering_")
           || s.StartsWith("refinement_kinding_")
           || s.StartsWith("kinding_Tm_arrow_")
           || s.StartsWith("haseq")
           || s.StartsWith("function_token")
           || s.StartsWith("fresh_token")
           || s.StartsWith("Prims_pretyping")
           || s.Contains("_pre_typing_Tm_arrow")
           || s.Contains("_interpretation_Tm_arrow")
           -> false
    | _ -> true
    in
  let es = List.filter f es in
  query_from_parsed es

let phase (n:string) (q:query):query =
  let es = query_to_parsed q in
  let s_phase = "phase_" in
  let phase_mismatch (s:string):bool =
    if not (s.Contains(s_phase)) then false else
    let i = s.IndexOf(s_phase) in
    let j = i + s_phase.Length in
    let k = s.IndexOf("_", j) in
    let m = s.Substring(j, k - j) in
    n <> m
  // split assertions among phases:
  let rec f polarity e = // polarity: false=assume, true=assert
    match e with
    | And es when polarity -> And (List.map (f polarity) es)
    | Or es when polarity -> Or (List.map (f polarity) es)
    | Not e -> Not (f (not polarity) e)
    | Implies (e1, e2) when polarity -> Implies (e1, f polarity e2)
    | Quant (q, fs, body, pats, qid, weight) when polarity -> Quant (q, fs, f polarity body, pats, qid, weight)
    | Exps [Token "Valid"; Exps ((Token s)::es)] when phase_mismatch s && polarity -> True
    | _ -> e
    in
  let g e =
    match e with
    | Assert (e, Some s) when phase_mismatch s -> []
    | Assert (e, sOpt) -> [Assert (f false e, sOpt)]
    | _ -> [e]
    in
  let es = List.collect g es in
  query_from_parsed es

// select nth check-sat, where n=0 is first, n=1 is second, etc.
let select_exps (n:string) (q:query):query =
  let es = query_to_unparsed q in
  let n = System.Int32.Parse n in
  let rec f ((n:int), (es:exp list), (stack:exp list list)) (e:exp):(int * exp list * exp list list) =
    if n < 0 then (n, es, stack) else
    match e with
    | Exps [Token "push"] -> (n, [], es::stack)
    | Exps [Token "pop"] -> (n, List.head stack, List.tail stack)
    | Exps [Token "check-sat"] when n > 0 -> (n - 1, es, stack)
    | Exps [Token "check-sat"] when n = 0 -> (n - 1, (e::es) @ (List.concat stack), [])
    | _ -> (n, e::es, stack)
    in
  let (_, es, _) = List.fold f (n, [], []) es in
  let es = List.rev es in
  query_from_unparsed es

let stats (q:query):query =
  let es = query_to_unparsed q in
  let f e =
    match e with
    | Exps [Token "check-sat"] -> [e; Exps [Token "get-info"; Token ":all-statistics"]]
    | _ -> [e]
    in
  let es = List.collect f es in
  query_from_unparsed es

let main (args:string list) =
  try
    let read_file name =
      printfn ";;parsing %s" name
      let stream_in = System.IO.File.OpenRead(name) in
      let parse_in = new System.IO.BinaryReader(stream_in) in
      let lexbuf = LexBuffer<byte>.FromBinaryReader parse_in in
      setInitialPos lexbuf name
      let p = Parse.start Lex.token lexbuf in
      parse_in.Close ()
      stream_in.Close ()
      p
      in
    let rec do_cmds (q:query) (cmds:string list):unit =
      match cmds with
      | [] -> ()
      | "-in"::filename::cmds -> do_cmds (Unparsed (read_file filename)) cmds
      | "-print"::cmds -> List.iter printn_exp (query_to_unparsed q); do_cmds q cmds
      | "-sort"::cmds -> sort_exps q; do_cmds q cmds
      | "-select"::n::cmds -> do_cmds (select_exps n q) cmds
      | "-remove"::cmds -> do_cmds (remove_exps q) cmds
      | "-phase"::n::cmds -> do_cmds (phase n q) cmds
      | "-stats"::cmds -> do_cmds (stats q) cmds
      | _ -> parse_err (sprintf "unknown commands: %A" cmds)
    do_cmds (Unparsed []) args
  with
  | ParseErr s -> printfn "parse error: %s" s
  | InternalErr s -> printfn "internal error: %s" s

let () = main (List.tail (List.ofArray (System.Environment.GetCommandLineArgs ())))
