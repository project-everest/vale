open Interop_Printer

(* let poly = ("poly", [("ctx", TBuffer TUInt64); ("inp", TBuffer TUInt64); ("len", TBase TUInt64)]) *)

(* let aes = ("aes", [("input_key", TBuffer TUInt128); ("output_key", TBuffer TUInt128)]) *)
	    
(* let gcmencrypt = ("gcmencrypt", [
  ("plain_b", TBuffer TUInt128); ("plain_num_bytes", TBase TUInt64);
  ("auth_b", TBuffer TUInt128); ("auth_num_bytes", TBase TUInt64);
  ("iv_b", TBuffer TUInt128); 
  ("key", TGhost "aes_key_LE AES_128"); ("keys_b", TBuffer TUInt128);
  ("cipher_b", TBuffer TUInt128); ("tag_b", TBuffer TUInt128)
  ],
    Stk (Prims.parse_int "18"))
*)
(*
let aes_encrypt_block = ("aes128_encrypt_block", [
  ("output_b", TBuffer TUInt128); ("input_b", TBuffer TUInt128);
  ("key", TGhost "aes_key_LE AES_128"); ("keys_b", TBuffer TUInt128)
  ], Stk (Prims.parse_int "0"))
*)

let ghash = ("ghash_incremental_bytes_stdcall", [
  ("h_b", TBuffer TUInt128); ("hash_b", TBuffer TUInt128);
  ("input_b", TBuffer TUInt128); ("num_bytes", TBase TUInt64)
  ], Stk (Prims.parse_int "0"))

let os = Linux

let _ = print_string (translate_vale os X86 ghash)
let _ = print_newline()
let _ = print_string (translate_lowstar os X86 ghash)
