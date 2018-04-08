module GCTR_i

open Types_s
open FStar.Mul
open FStar.Seq
open AES_s
open GCTR_s 
open FStar.Math.Lemmas

let aes_encrypt_le (alg:algorithm) (key:aes_key(alg)) (p:quad32) =
  let r_key = reverse_bytes_nat32_seq key in
  let r_p = reverse_bytes_quad32 p in
  aes_encrypt alg r_key r_p

logic let gctr_partial (bound:nat) (plain cipher:seq quad32) (key:aes_key(AES_128)) (icb:quad32) =
  let bound = min bound (min (length plain) (length cipher)) in
  forall j . {:pattern (index cipher j)} 0 <= j /\ j < bound ==> 
    index cipher j == quad32_xor (index plain j) (aes_encrypt_le AES_128 key (inc32 icb j))
  
let rec gctr_encrypt_recursive_length (icb:quad32) (plain:gctr_plain) 
				      (alg:algorithm) (key:aes_key alg) (i:int) : Lemma
  (requires True)				      
  (ensures length (gctr_encrypt_recursive icb plain alg key i) == length plain)
  (decreases %[length plain])
  [SMTPat (length (gctr_encrypt_recursive icb plain alg key i))]
  =
  if length plain = 0 then ()
  else gctr_encrypt_recursive_length icb (tail plain) alg key (i + 1)
  			
let rec gctr_encrypt_length (icb:quad32) (plain:seq quad32 { 256 * length plain < nat32_max }) 
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
	   index cipher j == quad32_xor (index plain j) (aes_encrypt_le alg key (inc32 icb (i + j)) ))))
  (decreases %[length plain])	   
=
  if length plain = 0 then ()
  else
      let tl = tail plain in
      let cipher = gctr_encrypt_recursive icb plain alg key i in  
      let r_cipher = gctr_encrypt_recursive icb tl alg key (i+1) in     
      let helper (j:int) : 
	Lemma ((0 <= j /\ j < length plain) ==> (index cipher j == quad32_xor (index plain j) (aes_encrypt_le alg key (inc32 icb (i + j)) )))
	= 
	if 0 < j && j < length plain then (
	  gctr_indexed_helper icb tl alg key (i+1);
	  assert(index r_cipher (j-1) == quad32_xor (index tl (j-1)) (aes_encrypt_le alg key (inc32 icb (i + 1 + j - 1)) )) // OBSERVE
	) else ()
      in
      FStar.Classical.forall_intro helper

let rec gctr_indexed (icb:quad32) (plain:gctr_plain) 
		     (alg:algorithm) (key:aes_key alg) (cipher:seq quad32) : Lemma
  (requires  length cipher == length plain /\
             (forall i . {:pattern index cipher i} 0 <= i /\ i < length cipher ==> 
	     index cipher i == quad32_xor (index plain i) (aes_encrypt_le alg key (inc32 icb i) )))
  (ensures  cipher == gctr_encrypt icb plain alg key)
=
  gctr_indexed_helper icb plain alg key 0;
  let c = gctr_encrypt_recursive icb plain alg key 0 in
  assert(eq cipher c)  // OBSERVE: Invoke extensionality lemmas


let gctr_partial_completed (plain cipher:seq quad32) (key:aes_key(AES_128)) (icb:quad32) : Lemma
  (requires length plain == length cipher /\
	    256 * (length plain) < nat32_max /\
	    gctr_partial (length cipher) plain cipher key icb)
  (ensures cipher == gctr_encrypt icb plain AES_128 key)
  =
  gctr_indexed icb plain AES_128 key cipher;
  ()

let gctr_encrypt_one_block (icb plain:quad32) (alg:algorithm) (key:aes_key alg) : 
  Lemma(gctr_encrypt icb (create 1 plain) alg key =
        (create 1 (quad32_xor plain (aes_encrypt_le alg key icb)))) =
  //assert(inc32 icb 0 == icb);
  let encrypted_icb = aes_encrypt_le alg key icb in
  let p = create 1 plain in
  //assert(length p == 1);
  //assert(tail p == createEmpty);
  //assert(length (tail p) == 0);
  //assert(head p == plain);
  assert(gctr_encrypt_recursive icb (tail p) alg key 1 == createEmpty);   // OBSERVE
  //assert(gctr_encrypt icb p alg key == cons (quad32_xor plain encrypted_icb) createEmpty);
  let x = quad32_xor plain encrypted_icb in
  append_empty_r (create 1 x);                 // This is the missing piece
  //assert(cons x createEmpty == create 1 x);
  ()
  
