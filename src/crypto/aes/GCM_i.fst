module GCM_i

open Opaque_s
open Types_s
open Types_i
open GCM_s
open AES_s
open GCM_helpers_i
open GCTR_s
open GCTR_i
open GHash_s
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
  reveal_opaque (gcm_encrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth)
(*
  let s_key_LE = seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE key) in
  let s_iv_BE = be_bytes_to_quad32 (be_quad32_to_bytes iv_BE) in
  let s_j0_BE = Mkfour 1 s_iv_BE.lo1 s_iv_BE.hi2 s_iv_BE.hi3 in
  let s_cipher = fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) in
  be_bytes_to_quad32_to_bytes iv_BE;
  assert (s_cipher == gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg s_key_LE);
  assert (s_iv_BE == iv_BE);
  assert (s_key_LE == key);

  assert (gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg s_key_LE ==
          gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg key);
   assert (gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg key ==
           gctr_encrypt_LE (inc32 s_j0_BE 1) (make_gctr_plain_LE plain) alg key);
  assert (gctr_encrypt_LE (inc32 s_j0_BE 1) (make_gctr_plain_LE plain) alg key ==
          gctr_encrypt_LE iv_enc (make_gctr_plain_LE plain) alg key);
  ()
*)

let gcm_encrypt_LE_snd_helper (iv_BE length_quad32 hash mac:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:aes_key_LE(alg)) : Lemma
  (requires (4096 * (length plain) < pow2_32 /\
             4096 * (length auth) < pow2_32 /\
             cipher == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) /\
             length_quad32 == reverse_bytes_quad32 (Mkfour (8 * length plain) 0 (8 * length auth) 0) /\
             (let h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
                      let auth_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in
                      let cipher_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
                      hash == ghash_LE h (append auth_padded_quads (append cipher_padded_quads (create 1 length_quad32))) /\
                      le_quad32_to_bytes mac == gctr_encrypt_LE (Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3) (le_quad32_to_bytes hash) alg key)
  ))
  (ensures le_quad32_to_bytes mac == snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth))
  =
  reveal_opaque (gcm_encrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth)
  //be_bytes_to_quad32_to_bytes iv_BE;
  //let t = snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) in
  //()


let decrypt_helper (alg:algorithm) (key:aes_key alg) (iv:seqn 16 nat8) (plain:seq nat8) (auth:seq nat8)
                   (rax:nat64) (alleged_tag_quad computed_tag:quad32) : Lemma
  (requires 4096 * length plain < pow2_32 /\
            4096 * length auth < pow2_32 /\
            (if alleged_tag_quad = computed_tag then rax = 0 else rax > 0) /\
            le_quad32_to_bytes computed_tag == snd (gcm_encrypt_LE alg key iv plain auth)
  )
  (ensures  (rax = 0) == snd (gcm_decrypt_LE alg key iv plain auth (le_quad32_to_bytes alleged_tag_quad)))
  = 
  let b = snd (gcm_decrypt_LE alg key iv plain auth (le_quad32_to_bytes alleged_tag_quad)) in
  let (_, ct) = gcm_encrypt_LE alg key iv plain auth in
  assert (b = (ct = (le_quad32_to_bytes alleged_tag_quad)));
  assert (ct == le_quad32_to_bytes computed_tag);
  assert (b == (le_quad32_to_bytes computed_tag = le_quad32_to_bytes alleged_tag_quad));
  le_quad32_to_bytes_injective_specific alleged_tag_quad computed_tag;
  assert (b == (computed_tag = alleged_tag_quad));
  assert ((rax = 0) == (computed_tag = alleged_tag_quad));
  ()
