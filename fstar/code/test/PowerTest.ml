let parse_cmdline :
  (string * (unit -> (PPC64LE_Vale_Decls.ins,PPC64LE_Vale_Decls.ocmp) PPC64LE_Machine_s.precode) * int * bool) list -> unit
  =
  fun l  ->
  let printer = PPC64LE_Vale_Decls.gcc in
  (* Extract and print assembly code *)
  PPC64LE_Vale_Decls.print_header printer;
  let _ = List.fold_left (fun label_count (name, code, _, _) ->
                          PPC64LE_Vale_Decls.print_proc name
                                                      (code ())
                                                      label_count printer)
                          (Prims.parse_int "0") l in
  PPC64LE_Vale_Decls.print_footer printer

let _ =
  parse_cmdline [
    ("Copy16", PPC64LE_Test_Memcpy.va_code_Copy16, 0, true);
    ("MulIf", PPC64LE_Test_Basics.va_code_MulIf, 0, true);
    ("AddLoop", PPC64LE_Test_Basics.va_code_AddLoop, 0, true);
    ("VecXor", PPC64LE_Test_Basics.va_code_VecXor, 0, true);
  ]
