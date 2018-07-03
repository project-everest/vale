open Interop_Printer

(* let poly = ("poly", [("ctx", TBuffer TUInt64); ("inp", TBuffer TUInt64); ("len", TBase TUInt64)]) *)

(* let aes = ("aes", [("input_key", TBuffer TUInt128); ("output_key", TBuffer TUInt128)]) *)
	    
let gcmencrypt = ("gcmencrypt", [
  ("plain_b", TBuffer TUInt128); ("plain_num_bytes", TBase TUInt64);
  ("auth_b", TBuffer TUInt128); ("auth_num_bytes", TBase TUInt64);
  ("iv_b", TBuffer TUInt128); ("keys_b", TBuffer TUInt128);
  ("cipher_b", TBuffer TUInt128); ("tag_b", TBuffer TUInt128)
  ])

let _ = print_string (translate_vale Linux X86 gcmencrypt)
let _ = print_newline()
let _ = print_string (translate_lowstar Linux X86 gcmencrypt)
