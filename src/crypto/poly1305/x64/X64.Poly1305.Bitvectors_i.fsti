module X64.Poly1305.Bitvectors_i

(*

open FStar.BV
open FStar.Mul
module U = FStar.UInt

val lemma_shr2: x:uint_t' 64 -> Lemma (U.shift_right #64 x 2 == U.udiv #64 x 4)
val lemma_shr4: x:uint_t' 64 -> Lemma (U.shift_right #64 x 4 == U.udiv #64 x 16)

val lemma_and_mod_n: x:uint_t' 64 -> Lemma (U.logand #64 x 3 == U.mod #64 x 4 /\ 
				      U.logand #64 x 15 == U.mod #64 x 16)
val lemma_clear_lower_2: x:uint_t' 8 -> Lemma (U.logand #8 x 0xfc == 
					U.mul_mod #8 (U.udiv #8 x 4) 4)
val lemma_and_constants: x:uint_t' 64 ->
  Lemma (U.logand #64 x 0 == 0 /\ U.logand #64 x 0xffffffffffffffff == x)
val lemma_poly_constants: x:uint_t' 64 -> 
  Lemma (U.logand #64 x 0x0ffffffc0fffffff < 0x1000000000000000 /\
	 U.logand #64 x 0x0ffffffc0ffffffc < 0x1000000000000000 /\
	 U.mod #64 (U.logand #64 x 0x0ffffffc0ffffffc) 4 == 0)
	 
val lemma_and_commutes: x:uint_t' 64 -> y:uint_t' 64 ->
  Lemma (U.logand #64 x y == U.logand #64 y x)
val lemma_bv128_64_64_and_helper: x:bv_t 128 -> x0:bv_t 64 -> x1:bv_t 64 ->
  y:bv_t 128 -> y0:bv_t 64 -> y1:bv_t 64 ->
  z:bv_t 128 -> z0:bv_t 64 -> z1:bv_t 64 ->
  Lemma (requires (z0 == bvand #64 x0 y0 /\
		   z1 == bvand #64 x1 y1 /\
		   x == bvor #128 (bvshl #128 (bv_uext #64 #64 x1) 64) (bv_uext #64 #64 x0) /\
		   y == bvor #128 (bvshl #128 (bv_uext #64 #64 y1) 64) (bv_uext #64 #64 y0) /\
		   z == bvor #128 (bvshl #128 (bv_uext #64 #64 z1) 64) (bv_uext #64 #64 z0)))
	(ensures (z == bvand #128 x y))
val bv128_64_64: x1:bv_t 64 -> x0:bv_t 64 -> Tot (bv_t 128)

val lemma_bv128_64_64_and: x:bv_t 128 -> x0:bv_t 64 -> x1:bv_t 64 ->
  y:bv_t 128 -> y0:bv_t 64 -> y1:bv_t 64 ->
  z:bv_t 128 -> z0:bv_t 64 -> z1:bv_t 64 ->
  Lemma (requires (z0 == bvand #64 x0 y0 /\
		   z1 == bvand #64 x1 y1 /\
		   x == bv128_64_64 x1 x0 /\
		   y == bv128_64_64 y1 y0 /\
		   z == bv128_64_64 z1 z0))
	(ensures (z == bvand #128 x y))

val lemma_bytes_shift_constants: unit -> Lemma
    (ensures (U.shift_left #64 0 3 == 0 /\
	     U.shift_left #64 1 3 == 8 /\
	     U.shift_left #64 2 3 == 16 /\
	     U.shift_left #64 3 3 == 24 /\
	     U.shift_left #64 4 3 == 32 /\
	     U.shift_left #64 5 3 == 40 /\
	     U.shift_left #64 6 3 == 48 /\
	     U.shift_left #64 7 3 == 56 /\
	     U.shift_left #64 1 (U.shift_left #64 0 3) == 0x1 /\
	     U.shift_left #64 1 (U.shift_left #64 1 3) == 0x100 /\
	     U.shift_left #64 1 (U.shift_left #64 2 3) == 0x10000 /\
	     U.shift_left #64 1 (U.shift_left #64 3 3) == 0x1000000 /\
	     U.shift_left #64 1 (U.shift_left #64 4 3) == 0x100000000 /\
	     U.shift_left #64 1 (U.shift_left #64 5 3) == 0x10000000000 /\
	     U.shift_left #64 1 (U.shift_left #64 6 3) == 0x1000000000000 /\
	     U.shift_left #64 1 (U.shift_left #64 7 3) == 0x100000000000000))

val lemma_bytes_and_mod0: x: bv_t 64 ->
  Lemma (bvand x (int2bv #64 (0x1 - 1)) == bvmod x 0x1)
val lemma_bytes_and_mod1: x: bv_t 64 ->
  Lemma (bvand x (int2bv #64 (0x100 - 1)) == bvmod x 0x100)
val lemma_bytes_and_mod2: x: bv_t 64 ->
  Lemma (bvand x (int2bv #64 (0x10000 - 1)) == bvmod x 0x10000)
val lemma_bytes_and_mod3: x: bv_t 64 ->
  Lemma (bvand x (int2bv #64 (0x1000000 - 1)) == bvmod x 0x1000000)
val lemma_bytes_and_mod4: x: bv_t 64 ->
  Lemma (bvand x (int2bv #64 (0x100000000 - 1)) == bvmod x 0x100000000)
val lemma_bytes_and_mod5: x: bv_t 64 ->
  Lemma (bvand x (int2bv #64 (0x10000000000 - 1)) == bvmod x 0x10000000000)
val lemma_bytes_and_mod6: x: bv_t 64 ->
  Lemma (bvand x (int2bv #64 (0x1000000000000 - 1)) == bvmod x 0x1000000000000)
val lemma_bytes_and_mod7: x: bv_t 64 ->
  Lemma (bvand x (int2bv #64 (0x100000000000000 - 1)) == bvmod x 0x100000000000000)
val lemma_bytes_and_mod_bv: x: bv_t 64 -> y:bv_t 64 -> z:bv_t 64 ->
  Lemma (requires (bvult #64 y (int2bv #64 8) /\
	z == bvshl #64 (int2bv #64 1) (bv2int (bvshl y 3))))
	(ensures (z <> bv_zero #64 /\ bvult #64 (bvshl y 3) (int2bv #64 64)))

val lemma_bytes_power2: unit ->
Lemma (ensures (pow2 0 == 0x1 /\
	       pow2 8 == 0x100 /\
		 pow2 16 == 0x10000 /\
		 pow2 24 == 0x1000000 /\
		 pow2 32 == 0x100000000 /\
		 pow2 40 == 0x10000000000 /\
		 pow2 48 == 0x1000000000000 /\
		 pow2 56 == 0x100000000000000))

val lemma_bytes_shift_power2: y:uint_t' 64 ->
  Lemma (requires (y < 8))
	(ensures  (U.shift_left #64 y 3 < 64 /\
		   y * 8 == U.shift_left #64 y 3 /\
		   pow2 (U.shift_left #64 y 3) == U.shift_left #64 1 (U.shift_left #64 y 3)))
*)
