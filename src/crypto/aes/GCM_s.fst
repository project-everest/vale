module GCM_s

open Types_s
open AES_s
open GCTR_s
open GHash_s

assume type gcm_plain
assume type gcm_auth

let gcm (alg:algorithm) (key:aes_key alg) (iv:quad32) (p:gcm_plain) (a:gcm_auth)  =
  let h = aes_encrypt alg key (Quad32 0 0 0 0) in
  let j0 = Quad32 1 iv.mid_lo iv.mid_hi iv.hi in
//  let c = gctr_encrypt (inc32 j0 1) p alg key in
  
  ()
