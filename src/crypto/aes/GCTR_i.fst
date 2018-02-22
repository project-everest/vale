module GCTR_i

open Types_s
open FStar.Mul
open FStar.List.Tot.Base
open AES_s
open GCTR_s 

let rec gctr_encrypt_recursive_length (icb:quad32) (plain:gctr_plain) 
				      (alg:algorithm) (key:aes_key alg) (i:int) : 
  Lemma(length (gctr_encrypt_recursive icb plain alg key i) == length plain) =
  match plain with 
  | [] -> ()
  | hd :: tl -> gctr_encrypt_recursive_length icb tl alg key (i + 1); 
  ()
  			
let rec gctr_encrypt_length (icb:quad32) (plain:list quad32 { 256 * length plain < nat32_max }) 
			     (alg:algorithm) (key:aes_key alg) : 
  Lemma(length (gctr_encrypt icb plain alg key) == length plain) 
  [SMTPat (length (gctr_encrypt icb plain alg key))]
  =
  gctr_encrypt_recursive_length icb plain alg key 0

let rec nth_in_bounds_is_some (l:list 'a) (i:int) : Lemma
  (requires 0 <= i /\ i < length l)
  (ensures Some? (nth l i))
  [SMTPat (nth l i)]
=
  if i = 0 then ()
  else nth_in_bounds_is_some (Cons?.tl l) (i - 1)

let nth_in_bounds (l:list 'a) (i:int {0 <= i /\ i < length l}) =
  nth_in_bounds_is_some l i;
  Some?.v (nth l i)

let rec gctr_indexed (icb:quad32) (plain:gctr_plain) 
		     (alg:algorithm) (key:aes_key alg) (i:int { 0 <= i /\ i < length plain }) : Lemma
  (requires True)
  (ensures (let cipher = gctr_encrypt icb plain alg key in
	    length cipher == length plain /\
	   (nth_in_bounds cipher i == quad32_xor (nth_in_bounds plain i) (aes_encrypt alg key (inc32 icb i) ))))
=
  if i = 0 then ()
  else (assume False)//; gctr_indexed icb (Cons?.tl plain) alg key (i - 1)
 
  
(*
let rec gctr_equivalence (icb:quad32) (plain:gctr_plain) 
		     (alg:algorithm) (key:aes_key alg) (cipher:list quad32) : Lemma
  (requires length cipher == length plain /\
             (forall i . {:pattern nth cipher i} 0 <= i /\ i < length cipher ==> 
	     nth_in_bounds cipher i == quad32_xor (nth_in_bounds plain i) (aes_encrypt alg key (inc32 icb i) )))
  (ensures  cipher == gctr_encrypt icb plain alg key)
=
  match plain with
  | [] -> ()
  | hd :: tl -> gctr_equivalence icb tl alg key (Cons?.tl cipher)
*)
