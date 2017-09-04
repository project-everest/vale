open Ast
open Ast_util
open Parse
open Parse_util
open Transform
open Emit_common
open Microsoft.Dafny
open Microsoft.FSharp.Math
open Microsoft.FSharp.Text.Lexing
open DafnyInterface
open System.IO

let cur_file = ref ""
let lexbufOpt = ref (None:LexBuffer<byte> option)
let dafny_opts_rev = ref []

let main (argv) =
  let in_files_rev = ref ([]:(string * bool) list) in
  let includes_rev = ref ([]:string list) in
  let suffixMap_rev = ref ([]:(string * string) list) in
  let sourceDir = ref "." in
  let destDir = ref "." in
  let outfile = ref (None:string option) in
  let dafnyDirect = ref false in
  let emitFStarText = ref false in
  let arg_list = argv |> Array.toList in
  let debug_flags = ref (Set.empty:Set<string>) in
  let print_error_loc locOpt =
    match locOpt with
    | None -> printfn "\nerror:"
    | Some loc -> printfn "\nerror at %s:" (string_of_loc loc)
    in
  let print_error_prefix locOpt =
    match !lexbufOpt with 
    | None -> printfn "\nerror processing file %s" !cur_file; print_error_loc locOpt
    | Some lexbuf -> printfn "\nerror at line %i column %i of file %s" (line lexbuf) (col lexbuf) (file lexbuf)
    in
  let rec print_error locOpt e =
    match e with
    | (LocErr (loc, e)) as x ->
        if Set.contains "stack" !debug_flags then printfn ""; printfn "internal details:"; print_error_loc locOpt; printfn "%s" (x.ToString ())
        print_error (Some loc) e
    | (Err s) as x ->
        print_error_loc locOpt
        printfn "%s" s
        if Set.contains "stack" !debug_flags then printfn ""; printfn "internal details:"; printfn "%s" (x.ToString ());
        exit 1
    | (InternalErr s) as x ->
        print_error_loc locOpt
        printfn "internal error:"
        printfn "%s" s
        printfn "\ninternal details:"
        printfn "%s" (x.ToString ())
        exit 1
    | ParseErr x -> (print_error_prefix locOpt; printfn "%s" x; exit 1)
    | :? System.ArgumentException as x -> (print_error_prefix locOpt; printfn "%s" (x.ToString ()); exit 1)
    | Failure x -> (print_error_prefix locOpt; printfn "%s" x; exit 1)
    | x -> (print_error_loc locOpt; printfn "%s" (x.ToString ()); exit 1)
    in
  try
  (
    let parse_argv (args:string list) =
      let rec match_args (arg_list:string list) =
        match arg_list with
        | "-dafnyDirect" ::l ->
            if !emitFStarText
            then failwith "Cannot include include both -dafnyDirect and -fstarText"
            else dafnyDirect := true; match_args l
        | "-h" :: [] -> failwith "TODO: Implement command line help"
        | "-fstarText" :: l ->
            if !dafnyDirect
            then failwith "Cannot include include both -dafnyDirect and -fstarText"
            else emitFStarText := true; match_args l
        | "-i" :: l ->
          match l with
          | [] -> failwith "Specify include file"
          | f :: l -> includes_rev := f::(!includes_rev); match_args l
        | "-include" :: l ->
          match l with
          | [] -> failwith "Specify include file"
          | f :: l -> in_files_rev := (f, false)::(!in_files_rev); match_args l
        | "-sourceDir" :: l ->
          match l with
          | x :: l -> sourceDir := x; match_args l
          | _ -> failwith "Specify source directory (to be prepended to -in files)"
        | "-destDir" :: l ->
          match l with
          | x :: l -> destDir := x; match_args l
          | _ -> failwith "Specify destination directory (to be prepended to -out file)"
        | "-includeSuffix" :: l ->
          match l with
          | src :: dst :: l -> suffixMap_rev := (src, dst)::(!suffixMap_rev); match_args l
          | _ -> failwith "Specify include suffix mapping"
        | "-in" :: l ->
          match l with
          | [] -> failwith "Specify input file"
          | f :: l -> in_files_rev := (f, true)::!in_files_rev; match_args l
        | "-out" :: l ->
          match l with
          | [] -> failwith "Specify output file"
          | f :: l -> outfile := Some f; match_args l
        | "-debug" :: l ->
          match l with
          | [] -> failwith "Specify debug feature name"
          | x :: l -> debug_flags := Set.add x !debug_flags; match_args l
        | "-assumeUpdates" :: s :: l -> assumeUpdates := System.Int32.Parse(s); match_args l
        | "-break" :: l -> ignore (System.Diagnostics.Debugger.Launch()); match_args l
        | "-reprint" :: file :: l -> reprint_file := Some file; match_args l
        | "-reprintVerbatims=false" :: l -> reprint_verbatims := false; match_args l
        | "-reprintGhostDecls=false" :: l -> reprint_ghost_decls := false; match_args l
        | "-reprintSpecs=false" :: l -> reprint_specs := false; match_args l
        | "-reprintGhostStmts=false" :: l -> reprint_ghost_stmts := false; match_args l
        | "-reprintLoopInvs=false" :: l -> reprint_loop_invs := false; match_args l
        | "-reprintBlankLines=false" :: l -> reprint_blank_lines := false; match_args l
        | "-conciseLemmas=false" :: l -> concise_lemmas := false; match_args l
        | f :: l ->
          if f.[0] = '-' then
            failwith ("Unrecognized argument: " + f + "\n")
          elif f.StartsWith "/" then
            dafny_opts_rev := f::(!dafny_opts_rev); match_args l
          else
            failwith ("Unrecognized argument: " + f + "\n")
        | [] -> if List.length !in_files_rev = 0 then failwith "Use -in to specify input file"
        in
        match_args args
      in
    parse_argv (List.tail arg_list);
    let in_files = List.rev (!in_files_rev) in
    let flagsSuffixMap = List.rev !suffixMap_rev in
    let debugIncludes = Set.contains "includes" !debug_flags in
    let parse_file comment name =
      printfn "%sparsing %s" comment name
      cur_file := name
      let stream_in = System.IO.File.OpenRead(name) in
      let parse_in = new System.IO.BinaryReader(stream_in) in
      let lexbuf = LexBuffer<byte>.FromBinaryReader parse_in in
      setInitialPos lexbuf name
      lexbufOpt := Some lexbuf;
      let p = Parse.start Lex.token lexbuf in
      lexbufOpt := None;
      parse_in.Close ()
      stream_in.Close ()
      p
    let includesSet = Set.ofList (List.map Path.GetFullPath !includes_rev) in
    let processedFiles = ref includesSet in
    let rebaseFile (o:string) (xabs:string):string =
      // Attempt to build a relative path to xabs from o; if that fails, use an absolute path
      let oabs = Path.GetFullPath o in
      let rec commonPrefix (s1:string) (s2:string) (i:int) (k:int) =
        if i >= s1.Length || i >= s2.Length then k else
        if s1.[i] <> s2.[i] then k else
        commonPrefix s1 s2 (i + 1) (if s1.[i] = Path.DirectorySeparatorChar then (i + 1) else k)
        in
      let prefixLen = commonPrefix oabs xabs 0 0 in
      let suffix1 = oabs.Substring(prefixLen) in
      let suffix2 = xabs.Substring(prefixLen) in
      let flipSeparator c = if c = Path.DirectorySeparatorChar then [".."] else [] in
      let flips = List.collect flipSeparator (List.ofArray (suffix1.ToCharArray ())) in
      let relPath = Path.Combine (List.toArray (flips @ [suffix2])) in
      // If the relative path is equivalent to the absolute path, use the relative path:
      let resultPath () = Path.GetFullPath (Path.Combine (Path.GetDirectoryName o, relPath)) in
      (if debugIncludes then
        printfn "rebase file:";
        printfn "   from: %A" o;
        printfn "     to: %A" xabs;
        printfn "  guess: %A" relPath;
        (try (let p = resultPath () in printfn "%s: %A" (if p = xabs then "     ok" else " failed") p) with err -> printfn "  error: %A" err)
      );
      let relPathOk = try (resultPath () = xabs) with _ -> false in
      if relPathOk then relPath else xabs
      in
    let processSuffixInclude (includerRaw:string) (x:string):unit =
      let x = if !dafnyDirect then Path.GetFullPath (Path.Combine (!destDir, Path.GetDirectoryName includerRaw, x)) else x in
      (if debugIncludes then printfn "adding generated include to %A" x);
      includes_rev := x::!includes_rev
      in
    let processVerbatimInclude (source:string) (x:string):unit =
      let xabs = Path.GetFullPath (Path.Combine (Path.GetDirectoryName source, x)) in
      if not (Set.contains xabs !processedFiles) then
        processedFiles := Set.add xabs !processedFiles;
        let path =
          match !outfile with
          | None -> xabs
          | Some o -> rebaseFile o xabs
          in
        (if debugIncludes then printfn "adding include from %A: %A --> %A --> %A" source x xabs path);
        includes_rev := path::!includes_rev
      in
    let rec processFile (xRaw:string, isInputFile:bool):((loc * decl) * bool) list =
      let x = if isInputFile then Path.Combine (!sourceDir, xRaw) else xRaw in
      (if debugIncludes then printfn "processing file %A" x);
      let xabs = Path.GetFullPath x in
      if Set.contains xabs !processedFiles then [] else
      processedFiles := Set.add xabs !processedFiles;
      let (incs, ds) = parse_file "// " x in
      let ds = List.map (fun d -> (d, isInputFile)) ds in
      let processInclude {inc_loc = loc; inc_attrs = attrs; inc_path = incPath} =
        try
          let attrs = skip_locs_attrs attrs in
          if attrs_get_bool (Id "verbatim") false attrs then
            (if isInputFile then processVerbatimInclude x incPath);
            []
          else
            let suffixMap = List.collect (fun a ->
              match a with (Id "suffix", [EString s1; EString s2]) -> [(s1, s2)] | _ -> []) attrs in
            let suffixMap = flagsSuffixMap @ suffixMap in
            let suffixFalse = List.exists (fun a ->
              match a with (Id "suffix", [EBool false]) -> true | _ -> false) attrs in
            let useSuffix = match suffixMap with [] -> false | _::_ -> isInputFile && not suffixFalse in
            let rec resuffix map s =
              match map with
              | [] -> err ("could not find matching suffix for path \"" + s + "; use 'include{:suffix false} to suppress this feature")
              | (s1, s2)::t when s.EndsWith(s1) -> s.Substring(0, s.Length - s1.Length) + s2
              | _::t -> resuffix t s
              in
            (if useSuffix then processSuffixInclude xRaw (resuffix suffixMap incPath));
            processFile (Path.Combine (Path.GetDirectoryName x, incPath), false)
        with err -> raise (LocErr (loc, err))
        in
      (List.collect processInclude incs) @ ds
      in
    let ins = List.map processFile in_files in
    let decls = List.concat ins in
    let stream =
      match !outfile with
      | None -> System.Console.Out
      | Some s ->
          let s = Path.Combine (!destDir, s) in
          let _ = System.IO.Directory.CreateDirectory (System.IO.Path.GetDirectoryName s) in
          (new System.IO.StreamWriter(new System.IO.FileStream(s, System.IO.FileMode.Create))):>System.IO.TextWriter
      in
    let ps =
      {
        print_out = stream;
        cur_loc = ref { loc_file = ""; loc_line = 1; loc_col = 1; loc_pos = 0 };
        cur_indent = ref "";
      } in
    if (not !dafnyDirect) then List.iter (fun (s:string) -> ps.PrintLine ("include \"" + s.Replace("\\", "\\\\") + "\"")) (List.rev !includes_rev);
    let decls = build_decls empty_env decls in
    (match !reprint_file with
      | None -> ()
      | Some filename ->
          let rstream = (new System.IO.StreamWriter(new System.IO.FileStream(filename, System.IO.FileMode.Create))):>System.IO.TextWriter in
          let rps =
            {
              print_out = rstream;
              cur_loc = ref { loc_file = ""; loc_line = 1; loc_col = 1; loc_pos = 0 };
              cur_indent = ref "";
            } in
          Emit_vale_text.emit_decls rps (List.rev (!reprint_decls_rev));
          rstream.Close ()
      );
    if !emitFStarText then Emit_fstar_text.emit_decls ps decls
    else
      if !dafnyDirect then
        // Initialize Dafny objects
        let mdl = new LiteralModuleDecl(new DefaultModuleDecl(), null) in
        let built_ins = new BuiltIns() in
        let arg_list = List.rev (!cur_file::!dafny_opts_rev) in
        DafnyOptions.Install(new DafnyOptions(new ConsoleErrorReporter()));
        Emit_dafny_direct.build_dafny_program mdl built_ins (List.rev !includes_rev) decls;
        DafnyDriver.Start_Dafny(List.toArray arg_list, mdl, built_ins) |> ignore
      else Emit_dafny_text.emit_decls ps decls;
    stream.Close ()
  )
  with err -> print_error None err
;;

let () = main (System.Environment.GetCommandLineArgs ())

