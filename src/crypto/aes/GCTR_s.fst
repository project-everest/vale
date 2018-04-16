module GCTR_s

// IMPORTANT: Following NIST's specification, this spec is written assuming a big-endian mapping from bytes to quad32s
//            Since the AES spec (AES_s) is in little-endian, we need to byteswap each time we call AES

open Words_s
open Types_s
open FStar.Mul
open AES_s
open FStar.Seq

// length plain < pow2_32 / 4096 <= spec max of 2**39 - 256;
type gctr_plain_LE = p:seq nat8 { 4096 * length p < pow2_32 }
type gctr_plain_internal_LE = p:seq quad32

let inc32 (cb:quad32) (i:int) : quad32 =
  Mkfour ((cb.lo0 + i) % pow2_32) cb.lo1 cb.hi2 cb.hi3

let gctr_encrypt_block (icb_BE:quad32) (plain_LE:quad32) (alg:algorithm) (key:aes_key_LE alg) (i:int) : quad32 =
  let icb_LE = reverse_bytes_quad32 (inc32 icb_BE i) in
  quad32_xor plain_LE (aes_encrypt_LE alg key icb_LE)


let rec gctr_encrypt_recursive (icb_BE:quad32) (plain:gctr_plain_internal_LE) 
			       (alg:algorithm) (key:aes_key_LE alg) (i:int) : Tot (seq quad32) (decreases %[length plain]) =
  if length plain = 0 then createEmpty
  else  
    cons (gctr_encrypt_block icb_BE (head plain) alg key i) (gctr_encrypt_recursive icb_BE (tail plain) alg key (i + 1))

let pad_to_128_bits (p:seq nat8) : (q:seq nat8 { length q % 16 == 0 /\ length q <= length p + 15 })
  =
  let num_extra_bytes = length p % 16 in
  if num_extra_bytes = 0 then p
  else p @| (create (16 - num_extra_bytes) 0)
  
// little-endian, except for icb_BE
let gctr_encrypt_LE (icb_BE:quad32) (plain:gctr_plain_LE) (alg:algorithm) (key:aes_key_LE alg) : seq nat8 =
  let nExtra = (length plain) % 16 in

  if nExtra = 0 then
    let plain_quads_LE = le_bytes_to_seq_quad32 plain in
    let cipher_quads_LE = gctr_encrypt_recursive icb_BE plain_quads_LE alg key 0 in
    le_seq_quad32_to_bytes cipher_quads_LE
  else
    let padded_plain = pad_to_128_bits plain in
    let plain_quads_LE = le_bytes_to_seq_quad32 padded_plain in
    let cipher_quads_LE = gctr_encrypt_recursive icb_BE plain_quads_LE alg key 0 in
    let cipher_bytes_LE = le_seq_quad32_to_bytes cipher_quads_LE in
    if length plain < length cipher_bytes_LE then
      slice cipher_bytes_LE 0 (length plain)   // Remove portions of ciphertext (if any) resulting from padding the plaintext
    else 
      cipher_bytes_LE
