module GCM_s

open Types_s
open AES_s
open GCTR_s
open GHash_s
open FStar.Seq

unfold type gcm_plain = gctr_plain
unfold type gcm_auth = gctr_plain

let gcm_encrypt (alg:algorithm) (key:aes_key alg) (iv:quad32) (p:gcm_plain) (a:gcm_auth)  =
  let h = aes_encrypt alg key (Quad32 0 0 0 0) in
  let j0 = Quad32 1 iv.mid_lo iv.mid_hi iv.hi in
  let c = gctr_encrypt (inc32 j0 1) p alg key in
  let hash_input = append a (append c (create 1 (Quad32 0 (length a) 0 (length c % nat32_max)))) in // Mod is needed, since F* can't see length c fits without a lemma
  let s = ghash h hash_input in
  let t = gctr_encrypt j0 (create 1 s) in
  c, t
