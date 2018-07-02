open Interop_Printer

(* let poly = ("poly", [("ctx", TBuffer TUInt64); ("inp", TBuffer TUInt64); ("len", TBase TUInt64)]) *)

let aes = ("aes", [("input_key", TBuffer TUInt128); ("output_key", TBuffer TUInt128)])
	    
let _ = print_string (translate_vale Linux X86 aes)
let _ = print_newline()
let _ = print_string (translate_lowstar Linux X86 aes)
