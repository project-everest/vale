module GCM_i

open Types_s
open Types_i
open GCM_s
open AES_s
open GCM_helpers_i
open GCTR_s
open GCTR_i
open FStar.Mul
open FStar.Seq
open Words_s
open Words.Seq_s

let gcm_encrypt_LE_fst_helper (iv_enc iv_BE:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:aes_key_LE(alg)) : Lemma
  (requires cipher == gctr_encrypt_LE iv_enc (make_gctr_plain_LE plain) alg key /\
                      4096 * (length plain) < pow2_32 /\
                      4096 * (length auth) < pow2_32 /\
                      iv_enc == inc32 (Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3) 1
  )
  (ensures cipher == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth))
  =
  let s_key_LE = seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE key) in
  let s_iv_BE = be_bytes_to_quad32 (be_quad32_to_bytes iv_BE) in
  let s_j0_BE = Mkfour 1 s_iv_BE.lo1 s_iv_BE.hi2 s_iv_BE.hi3 in
  let s_cipher = fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) in
  assert (s_cipher == gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg s_key_LE);
  be_bytes_to_quad32_to_bytes iv_BE;
  assert (s_iv_BE == iv_BE);
  assert (s_key_LE == key);

  assert (gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg s_key_LE ==
          gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg key);
   assert (gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg key ==
           gctr_encrypt_LE (inc32 s_j0_BE 1) (make_gctr_plain_LE plain) alg key);
  assert (gctr_encrypt_LE (inc32 s_j0_BE 1) (make_gctr_plain_LE plain) alg key ==
          gctr_encrypt_LE iv_enc (make_gctr_plain_LE plain) alg key);
  ()
  
            
