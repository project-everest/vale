module GCTR_s

// IMPORTANT: Following NIST's specification, this spec is written assuming a big-endian mapping from bytes to quad32s
//            Since the AES spec (AES_s) is in little-endian, we need to byteswap each time we call AES

open Words_s
open Types_s
open FStar.Mul
open AES_s
open FStar.Seq

// length plain < pow2_32 / 256 <= spec max of 2**39 - 256;
type gctr_plain = p:seq quad32 { 256 * length p < pow2_32 }

let inc32 (cb:quad32) (i:int) : quad32 =
  Mkfour ((cb.lo0 + i) % pow2_32) cb.lo1 cb.hi2 cb.hi3

let rec gctr_encrypt_recursive (icb:quad32) (plain:gctr_plain) 
			       (alg:algorithm) (key:aes_key alg) (i:int) : Tot (seq quad32) (decreases %[length plain]) =
  if length plain = 0 then createEmpty
  else 
    let r_key = reverse_bytes_nat32_seq key in
    let r_icb = reverse_bytes_quad32 (inc32 icb i) in
    cons (quad32_xor (head plain) (aes_encrypt alg r_key r_icb)) (gctr_encrypt_recursive icb (tail plain) alg key (i + 1))
  
let gctr_encrypt (icb:quad32) (plain:gctr_plain) (alg:algorithm) (key:aes_key alg) =
  gctr_encrypt_recursive icb plain alg key 0
  
