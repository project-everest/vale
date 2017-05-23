module Poly1305_lemmas

open FStar.Mul
open FStar.UInt
open Semantics
(*
lemma_BitwiseAdd64()
lemma_BitwiseMul64()
*)

let lemma_poly_multiply (n:int) (p:int{ p > 0 }) (r:int) (h:int) (r0:int) (r1:nat) (h0:int) (h1:int) (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int)
  : Lemma (requires 4 * (n * n) == p + 5
		  /\ r == r1 * n + r0
		  /\ h == h2 * (n * n) + h1 * n + h0
		  /\ s1 == r1 + (r1 / 4)
		  /\ r1 % 4 == 0
		  /\ d0 == h0 * r0 + h1 * s1
		  /\ d1 == h0 * r1 + h1 * r0 + h2 * s1
		  /\ d2 == h2 * r0
		  /\ hh == d2 * (n * n) + d1 * n + d0)
	  (ensures (h * r) % p == hh % p)
  = admit()

let lemma_poly_reduce (n:int) (p:int{ p > 0 }) (h:nat) (h2:int) (h10:int) (c:int) (hh:int)
   : Lemma (requires 4 * (n * n) == p + 5
		     /\ h2 == h / (n * n)
		     /\ h10 == h % (n * n)
		     /\ c == (h2 / 4) + (h2 / 4) * 4
		     /\ hh == h10 + c + (h2 % 4) * (n * n))
	   (ensures h % p == hh % p)
   = admit()

let lemma_poly_bits64 ()
  : Lemma (requires true)
	  (ensures (forall (x:nat64) . shift_right #64 x 2 == x / 4)
		/\  (forall (x:nat64) . shift_right #64 x 4 == x / 16)
		/\  (forall (x:nat64) . logand #64 x 3 == x % 4)
		/\  (forall (x:nat64) . logand #64 x 15 == x % 16)
		/\  (forall (x:nat64) . logand #64 x 0 == 0)
		/\  (forall (x:nat64) . logand #64 x 0xffffffffffffffff == x)
		/\  (forall (x:nat64) . logand #64 x 0xfffffffffffffffc == (x / 4) * 4)
		/\  (forall (x:nat64) . logand #64 x 0x0ffffffc0fffffff < nat64_max / 16)
		/\  (forall (x:nat64) . logand #64 x 0x0ffffffc0ffffffc < nat64_max / 16)
		/\  (forall (x:nat64) . (logand #64 x 0x0ffffffc0ffffffc) % 4 == 0)	  
	  )
 = admit()	  
