module GCTR_s

// IMPORTANT: Following NIST's specification, this spec is written assuming a big-endian mapping from bytes to quad32s
//            Since the AES spec (AES_s) is in little-endian, we need to byteswap each time we call AES

open Words_s
open Types_s
open FStar.Mul
open AES_s
open FStar.Seq

// length plain < pow2_32 / 256 <= spec max of 2**39 - 256;
type gctr_plain_LE = p:seq quad32 { 256 * length p < pow2_32 }

let inc32 (cb:quad32) (i:int) : quad32 =
  Mkfour ((cb.lo0 + i) % pow2_32) cb.lo1 cb.hi2 cb.hi3

let rec gctr_encrypt_recursive (icb_BE:quad32) (plain:gctr_plain_LE) 
			       (alg:algorithm) (key:aes_key_LE alg) (i:int) : Tot (seq quad32) (decreases %[length plain]) =
  if length plain = 0 then createEmpty
  else
    let icb_LE = reverse_bytes_quad32 (inc32 icb_BE i) in
    cons (quad32_xor (head plain) (aes_encrypt_LE alg key icb_LE)) (gctr_encrypt_recursive icb_BE (tail plain) alg key (i + 1))
  
// little-endian, except for icb_BE
let gctr_encrypt_LE (icb_BE:quad32) (plain:gctr_plain_LE) (alg:algorithm) (key:aes_key_LE alg) : seq quad32 =
  gctr_encrypt_recursive icb_BE plain alg key 0
  
