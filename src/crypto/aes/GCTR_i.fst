module GCTR_i

open Types_s
open FStar.Mul
open FStar.List.Tot.Base
open FStar.List.Tot.Properties
open AES_s
open GCTR_s 
open FStar.Math.Lemmas

let gctr_partial (bound:nat) (plain cipher:Seq.seq quad32) (key:aes_key(AES_128)) (icb:quad32) =
  let bound = min bound (min (Seq.length plain) (Seq.length cipher)) in
  forall j . {:pattern (Seq.index cipher j)} 0 <= j /\ j < bound ==> Seq.index cipher j == quad32_xor (Seq.index plain j) (aes_encrypt AES_128 key (inc32 icb j))
  

let rec gctr_encrypt_recursive_length (icb:quad32) (plain:gctr_plain) 
				      (alg:algorithm) (key:aes_key alg) (i:int) : 
  Lemma(length (gctr_encrypt_recursive icb plain alg key i) == length plain)
  [SMTPat (length (gctr_encrypt_recursive icb plain alg key i))]
  =
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

#reset-options "--use_two_phase_tc true" // Needed so that indexing cipher and plain knows that their lengths are equal
let rec gctr_indexed_helper (icb:quad32) (plain:gctr_plain) 
			    (alg:algorithm) (key:aes_key alg) (i:int) : Lemma
  (requires True)
  (ensures (let cipher = gctr_encrypt_recursive icb plain alg key i in
	    length cipher == length plain /\
	   (forall j . {:pattern index cipher j} 0 <= j /\ j < length plain ==>
	   index cipher j == quad32_xor (index plain j) (aes_encrypt alg key (inc32 icb (i + j)) ))))
=
  match plain with 
  | [] -> ()
  | hd :: tl ->
      let cipher = gctr_encrypt_recursive icb plain alg key i in  
      let r_cipher = gctr_encrypt_recursive icb tl alg key (i+1) in     
      let helper (j:int) : 
	Lemma ((0 <= j /\ j < length plain) ==> (index cipher j == quad32_xor (index plain j) (aes_encrypt alg key (inc32 icb (i + j)) )))
	= 
	if 0 < j && j < length plain then (
	  gctr_indexed_helper icb tl alg key (i+1);
	  assert(index r_cipher (j-1) == quad32_xor (index tl (j-1)) (aes_encrypt alg key (inc32 icb (i + 1 + j - 1)) )) // OBSERVE
	) else ()
      in
      FStar.Classical.forall_intro helper

let rec gctr_indexed (icb:quad32) (plain:gctr_plain) 
		     (alg:algorithm) (key:aes_key alg) (cipher:list quad32) : Lemma
  (requires  length cipher == length plain /\
             (forall i . {:pattern index cipher i} 0 <= i /\ i < length cipher ==> 
	     index cipher i == quad32_xor (index plain i) (aes_encrypt alg key (inc32 icb i) )))
  (ensures  cipher == gctr_encrypt icb plain alg key)
=
  gctr_indexed_helper icb plain alg key 0;
  let c = gctr_encrypt_recursive icb plain alg key 0 in
  index_extensionality c cipher;
  ()

