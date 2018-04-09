module GCM_s

// IMPORTANT: Following NIST's specification, this spec is written assuming a big-endian mapping from bytes to quad32s
//            Since the AES spec (AES_s) is in little-endian, we need to byteswap each time we call AES

open Words_s
open Types_s
open AES_s
open GCTR_s
open GHash_s
open FStar.Seq

unfold type gcm_plain = gctr_plain
unfold type gcm_auth = gctr_plain

let gcm_encrypt (alg:algorithm) (key:aes_key alg) (iv:quad32) (p:gcm_plain) (a:gcm_auth)  =
  let h = aes_encrypt alg (reverse_bytes_nat32_seq key) (Mkfour 0 0 0 0) in
  let j0 = Mkfour 1 iv.lo1 iv.hi2 iv.hi3 in
  let c = gctr_encrypt (inc32 j0 1) p alg key in
  let hash_input = append a (append c (create 1 (Mkfour 0 (length c % pow2_32) 0 (length a)))) in // Mod is needed, since F* can't see length c fits without a lemma
  let s = ghash h hash_input in
  let t = gctr_encrypt j0 (create 1 s) alg key in
  c, t
