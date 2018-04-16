module GCM_s

open Words_s
open Words.Seq_s
open Types_s
open AES_s
open GCTR_s
open GHash_s
open FStar.Seq
open FStar.Mul

unfold type gcm_plain_LE = gctr_plain_LE
unfold type gcm_auth_LE = gctr_plain_LE

let pad_to_128_bits (p:seq nat8) : (q:seq nat8 { length q % 16 == 0 /\ length q <= length p + 15 })
  =
  let num_extra_bytes = length p % 16 in
  if num_extra_bytes = 0 then p
  else p @| (create (16 - num_extra_bytes) 0)

// little-endian, except for iv_BE
let gcm_encrypt_LE (alg:algorithm) (key:aes_key_LE alg) (iv_BE:quad32) (plain:seq nat8) (auth:seq nat8):
  Pure (tuple2 (seq nat8) (seq quad32))
  (requires 4096 * length plain < pow2_32 /\
            4096 * length auth < pow2_32
  )
  (ensures fun (c, t) -> True)
  =
  let h_LE = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
  let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
  let padded_p = le_bytes_to_seq_quad32 (pad_to_128_bits plain) in
  let raw_c = gctr_encrypt_LE (inc32 j0_BE 1) padded_p alg key in
  let raw_c_bytes = le_seq_quad32_to_bytes raw_c in
  // Remove portions of ciphertext (if any) resulting from padding the plaintext
  let c_bytes = if length plain < length raw_c_bytes then slice raw_c_bytes 0 (length plain) else raw_c_bytes in  
  // lengths = [0; (length a); 0; (length c % pow2_32)]
  let lengths_BE = Mkfour (8 * length plain) 0 (8 * length auth) 0 in
  let lengths_LE = reverse_bytes_quad32 lengths_BE in
  let zero_padded_c = pad_to_128_bits c_bytes in
  let zero_padded_a = pad_to_128_bits auth in
  let c_LE = le_bytes_to_seq_quad32 zero_padded_c in
  let a_LE = le_bytes_to_seq_quad32 zero_padded_a in
  let hash_input_LE = append a_LE (append c_LE (create 1 lengths_LE)) in
  let s_LE = ghash_LE h_LE hash_input_LE in
  let t = gctr_encrypt_LE j0_BE (create 1 s_LE) alg key in
  c_bytes, t


let gcm_encrypt (alg:algorithm) (key:aes_key alg) (iv:seqn 16 nat8) (plain:seq nat8) (auth:seq nat8) :
  Pure (tuple2 (seq nat8) (seq nat8))
    (requires
      4096 * length plain < pow2_32 /\
      4096 * length auth < pow2_32
    )
    (ensures fun (c, t) -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let iv_BE = be_bytes_to_quad32 iv in
  let (c, t) = gcm_encrypt_LE alg key_LE iv_BE plain  auth in
  (c, le_seq_quad32_to_bytes t)
