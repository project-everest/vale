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

// little-endian, except for iv_BE
let gcm_encrypt_LE (alg:algorithm) (key:aes_key_LE alg) (iv_BE:quad32) (p:gcm_plain_LE) (a:gcm_auth_LE) :
  tuple2 (seq quad32) (seq quad32)
  =
  let h_LE = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
  let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
  let c = gctr_encrypt_LE (inc32 j0_BE 1) p alg key in
  // lengths = [0; (length a); 0; (length c % pow2_32)]
  let lengths_BE = Mkfour ((128 * length c) % pow2_32) 0 (128 * length a) 0 in // Mod is needed, since F* can't see length c fits without a lemma
  let lengths_LE = reverse_bytes_quad32 lengths_BE in
  let hash_input_LE = append a (append c (create 1 lengths_LE)) in
  let s_LE = ghash_LE h_LE hash_input_LE in
  let t = gctr_encrypt_LE j0_BE (create 1 s_LE) alg key in
  c, t

let gcm_encrypt (alg:algorithm) (key:aes_key alg) (iv:seqn 16 nat8) (plain:seq nat8) (auth:seq nat8) :
  Pure (tuple2 (seq nat8) (seq nat8))
    (requires
      // TODO: handle lengths other than multiples of 16
      4096 * length plain < pow2_32 /\ length plain % 16 == 0 /\
      4096 * length auth < pow2_32 /\ length auth % 16 == 0
    )
    (ensures fun (c, t) -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let iv_BE = be_bytes_to_quad32 iv in
  let p_LE = le_bytes_to_seq_quad32 plain in
  let a_LE = le_bytes_to_seq_quad32 auth in
  let (c, t) = gcm_encrypt_LE alg key_LE iv_BE p_LE a_LE in
  (le_seq_quad32_to_bytes c, le_seq_quad32_to_bytes t)
