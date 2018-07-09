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

(*
let ghash = ("ghash_incremental_bytes_stdcall", [
  ("h_b", TBuffer TUInt128); ("hash_b", TBuffer TUInt128);
  ("input_b", TBuffer TUInt128); ("num_bytes", TBase TUInt64)
  ], Stk (Prims.parse_int "0"))
*)
(*
let gctr_bytes_extra_buffer = ("gctr_bytes_extra_buffer", [
  ("plain_b", TBuffer TUInt128); ("num_bytes", TBase TUInt64);
  ("iv_old", TGhost "quad32"); ("iv_b", TBuffer TUInt128);
  ("key", TGhost "aes_key_LE AES_128"); ("keys_b", TBuffer TUInt128);
  ("cipher_b", TBuffer TUInt128)], Stk (Prims.parse_int "0"))
*)
(*
let ghash_extra = ("ghash_incremental_extra_stdcall", [
  ("in_b", TBuffer TUInt128); ("hash_b", TBuffer TUInt128);
  ("h_b", TBuffer TUInt128); ("num_bytes", TBase TUInt64);
  ("orig_hash", TGhost "quad32")], Stk (Prims.parse_int "0"))
*)

(*
let ghash_one_block = ("ghash_incremental_one_block_buffer", [
  ("h_b", TBuffer TUInt128); ("hash_b", TBuffer TUInt128);
  ("input_b", TBuffer TUInt128); ("offset", TBase TUInt64)
  ], Stk (Prims.parse_int "0"))
*)

(* let inc32 = ("inc32_buffer", [("iv_b", TBuffer TUInt128)], Stk (Prims.parse_int "0")) *)

 
(* let quad32_xor = ("quad32_xor_buffer", [("src1", TBuffer TUInt128);
  ("src2", TBuffer TUInt128); ("dst", TBuffer TUInt128)], Stk (Prims.parse_int "0")) *)

(*
let gcm_make_length = ("gcm_make_length_quad_buffer", [
  ("plain_num_bytes", TBase TUInt64); ("auth_num_bytes", TBase TUInt64);
  ("b", TBuffer TUInt128)], Stk (Prims.parse_int "0"))
*)

(*
let gcm_load_xor = ("gcm_load_xor_store_buffer", [
  ("plain_b", TBuffer TUInt128); ("mask_b", TBuffer TUInt128);
  ("cipher_b", TBuffer TUInt128); ("offset", TBase TUInt64);
  ("num_blocks", TGhost "nat64");
  ("key", TGhost "aes_key_LE AES_128"); ("iv", TGhost "quad32")], Stk (Prims.parse_int "0"))
*)

(*
let aes_encrypt_block_be = ("aes128_encrypt_block_be", [
  ("output_b", TBuffer TUInt128); ("input_b", TBuffer TUInt128);
  ("key", TGhost "aes_key_LE AES_128"); ("keys_b", TBuffer TUInt128)
  ], Stk (Prims.parse_int "0"))
*)

let mk_quad1 = ("mk_quad32_lo0_be_1_buffer_win", [("b", TBuffer TUInt128)], Stk (Prims.parse_int "0"))
(*
let zero_quad32_buffer = ("zero_quad32_buffer_win", [("b", TBuffer TUInt128)], Stk (Prims.parse_int "0"))
*)
let os = Windows 

let name = mk_quad1 

let _ = print_string (translate_vale os X86 name)
let _ = print_newline()
let _ = print_string (translate_lowstar os X86 name)
