module GCTR_s

open Types_s
//open FStar.Seq
open FStar.Mul
open AES_s
open FStar.List.Tot.Base

type gctr_plain = p:list quad32 { 256 * length p < nat32_max }

let inc32 (cb:quad32) (i:int) = 
  Quad32 ((cb.lo + i) % nat32_max) cb.mid_lo cb.mid_hi cb.hi

let rec gctr_encrypt_recursive (icb:quad32) (plain:gctr_plain) 
			       (alg:algorithm) (key:aes_key alg) (i:int) =
  match plain with
  | [] -> []
  | hd :: tl -> (quad32_xor hd (aes_encrypt alg key (inc32 icb i))) :: (gctr_encrypt_recursive icb tl alg key (i + 1))
  
(*
  if length plain = 0 then
    createEmpty
  else
    cons (quad32_xor (index plain 0) (aes_encrypt alg key (inc32 icb i))) (gctr_encrypt_recursive icb (slice plain 1 (length plain)) alg key (i + 1))
*)

(*
let rec gctr_encrypt_recursive (icb:quad32) (plain:seq quad32 { 256 * length plain < nat32_max }) (alg:algorithm) (key:aes_key alg) =
  if length plain == 0 then
    []
  else 
    let rest = gctr_encrypt_recursive icb (all_but_last plain) alg key in
    rest + [quad32_xor (last plain) (aes_encrypt alg key (inc32 icb ((length plain) - 1)))] 
*)

// length plain < nat32_max / 256 <= spec max of 2**39 - 256;
let gctr_encrypt (icb:quad32) (plain:gctr_plain) (alg:algorithm) (key:aes_key alg) =
  gctr_encrypt_recursive icb plain alg key 0
  
