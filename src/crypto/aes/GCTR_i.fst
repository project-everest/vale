module GCTR_i

open Types_s
open FStar.Mul
open FStar.List.Tot.Base
open AES_s
open GCTR_s 

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

let nth_in_bounds_extension (l:list 'a) (i:int {0 < i /\ i < length l}) : Lemma
  (requires length l > 0)
  (ensures (nth_in_bounds l i) == (nth_in_bounds (Cons?.tl l) (i - 1)))
  =
  ()

(*
let rec gctr_indexed (icb:quad32) (plain:gctr_plain) 
		     (alg:algorithm) (key:aes_key alg) (i:int) : Lemma
  (requires True)
  (ensures (let cipher = gctr_encrypt_recursive icb plain alg key i in
	    length cipher == length plain /\
	   (forall j . {:pattern nth_in_bounds cipher j} 0 <= j /\ j < length plain ==>
	   nth_in_bounds cipher j == quad32_xor (nth_in_bounds plain j) (aes_encrypt alg key (inc32 icb (i + j)) ))))
=
  match plain with 
  | [] -> ()
  | hd :: tl ->
      let cipher = gctr_encrypt_recursive icb plain alg key i in  
      assert (length cipher == length plain);
      let r_cipher = gctr_encrypt_recursive icb tl alg key (i+1) in     
      assert( Cons?.tl cipher == r_cipher);
      gctr_indexed icb tl alg key (i+1);
      let foo (j:int{0 <= j /\ j < length plain}) : 
	Lemma (nth_in_bounds cipher j == quad32_xor (nth_in_bounds plain j) (aes_encrypt alg key (inc32 icb (i + j)) ))
	= 
	if j = 0 then ()
	else 
	assert(j > 0);
	assert(j < length plain);
	assert(j < length cipher);
	nth_in_bounds_extension cipher j;
	assert(nth_in_bounds cipher j == nth_in_bounds r_cipher (j - 1));
		assume(False);
	assert(nth_in_bounds cipher (j-1) == quad32_xor (nth_in_bounds tl (j-1)) (aes_encrypt alg key (inc32 icb (i + j - 1)) ));
	assume(False)
      in
      assume(False)
(*      
      assert (nth_in_bounds r_cipher (i-1) == quad32_xor (nth_in_bounds tl (i-1)) (aes_encrypt alg key (inc32 icb (i+1) )));
      assert( Cons?.tl cipher == r_cipher);
      //assert (nth_in_bounds r_cipher (i-1) == nth_in_bounds cipher i);
      
      assume(False)
*)      


let rec gctr_indexed (icb:quad32) (plain:gctr_plain) 
		     (alg:algorithm) (key:aes_key alg) (i:int { 0 <= i /\ i < length plain }) : Lemma
  (requires True)
  (ensures (let cipher = gctr_encrypt icb plain alg key in
	    length cipher == length plain /\
	   (nth_in_bounds cipher i == quad32_xor (nth_in_bounds plain i) (aes_encrypt alg key (inc32 icb i) ))))
=
  if i = 0 then ()
  else 
    match plain with 
    | [] -> ()
    | hd :: tl -> 
      let cipher = gctr_encrypt_recursive icb plain alg key 0 in  
      let tl_cipher = gctr_encrypt_recursive icb tl alg key 1 in  
      assert( Cons?.tl cipher == tl_cipher);
      gctr_indexed icb plain alg key (i - 1);
      assert (nth_in_bounds cipher (i-1) == quad32_xor (nth_in_bounds plain (i-1)) (aes_encrypt alg key (inc32 icb (i-1) )));
      assume(False)


      let r_cipher = gctr_encrypt_recursive icb tl alg key (i-1) in     
      gctr_indexed icb tl alg key (i - 1);
      assert (nth_in_bounds r_cipher (i-1) == quad32_xor (nth_in_bounds tl (i-1)) (aes_encrypt alg key (inc32 icb (i+1) )));
      assert( Cons?.tl cipher == r_cipher);
      //assert (nth_in_bounds r_cipher (i-1) == nth_in_bounds cipher i);
      
      assume(False)




let rec gctr_indexed (icb:quad32) (plain:gctr_plain) 
		     (alg:algorithm) (key:aes_key alg) (i:int { 0 <= i /\ i < length plain }) : Lemma
  (requires True)
  (ensures (let cipher = gctr_encrypt_recursive icb plain alg key i in
	    length cipher == length plain /\
	   (nth_in_bounds cipher i == quad32_xor (nth_in_bounds plain i) (aes_encrypt alg key (inc32 icb i) ))))
=
  if i = 0 then ()
  else 
    match plain with 
    | [] -> ()
    | hd :: tl -> 
      let cipher = gctr_encrypt_recursive icb plain alg key i in  
      let r_cipher = gctr_encrypt_recursive icb tl alg key (i+1) in     
      gctr_indexed icb tl alg key (i + 1);
      assert (nth_in_bounds r_cipher (i-1) == quad32_xor (nth_in_bounds tl (i-1)) (aes_encrypt alg key (inc32 icb (i+1) )));
      assert( Cons?.tl cipher == r_cipher);
      //assert (nth_in_bounds r_cipher (i-1) == nth_in_bounds cipher i);
      
      assume(False)
   
  
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
*)
