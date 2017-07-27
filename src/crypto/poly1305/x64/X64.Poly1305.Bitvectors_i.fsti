module X64.Poly1305.Bitvectors_i

open FStar.Mul
open FStar.BV
open FStar.UInt.Vectors
open FStar.UInt.Types
open FStar.UInt.Base
				    
val lemma_clear_lower_2: x:uint_t 64 -> 
  Lemma (logand #64 x 0xfffffffffffffffc == mul_mod #64 (udiv #64 x 4) 4)

val lemma_bv128_64_64_and_helper: x:bv_t 128 -> x0:bv_t 64 -> x1:bv_t 64 ->
  y:bv_t 128 -> y0:bv_t 64 -> y1:bv_t 64 ->
  z:bv_t 128 -> z0:bv_t 64 -> z1:bv_t 64 ->
  Lemma (requires (z0 == bvand #64 x0 y0 /\
		   z1 == bvand #64 x1 y1 /\
		   x == bvor #128 (bvshl #128 (bv_uext #64 #64 x1) 64) 
							   (bv_uext #64 #64 x0) /\
		   y == bvor #128 (bvshl #128 (bv_uext #64 #64 y1) 64) 
							   (bv_uext #64 #64 y0) /\
		   z == bvor #128 (bvshl #128 (bv_uext #64 #64 z1) 64) 
							   (bv_uext #64 #64 z0)))
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

val lemma_bytes_shift_constants0: unit -> Lemma
    (shift_left #64 0 3 == 0 /\
	     shift_left #64 1 (shift_left #64 0 3) == 0x1)

val lemma_bytes_shift_constants1: unit -> Lemma
    (shift_left #64 1 3 == 8 /\
	     shift_left #64 1 (shift_left #64 1 3) == 0x100)

val lemma_bytes_shift_constants2: unit -> Lemma
    (shift_left #64 2 3 == 16 /\
	     shift_left #64 1 (shift_left #64 2 3) == 0x10000)

val lemma_bytes_shift_constants3: unit -> Lemma
    (shift_left #64 3 3 == 24 /\
	     shift_left #64 1 (shift_left #64 3 3) == 0x1000000)

val lemma_bytes_shift_constants4: unit -> Lemma
    (shift_left #64 4 3 == 32 /\
	     shift_left #64 1 (shift_left #64 4 3) == 0x100000000)

val lemma_bytes_shift_constants5: unit -> Lemma
    (shift_left #64 5 3 == 40 /\
	     shift_left #64 1 (shift_left #64 5 3) == 0x10000000000)

val lemma_bytes_shift_constants6: unit -> Lemma
    (shift_left #64 6 3 == 48 /\
	     shift_left #64 1 (shift_left #64 6 3) == 0x1000000000000)

val lemma_bytes_shift_constants7: unit -> Lemma
    (shift_left #64 7 3 == 56 /\
	     shift_left #64 1 (shift_left #64 7 3) == 0x100000000000000)

val lemma_bytes_and_mod0: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1 - 1) == mod #64 x 0x1)
val lemma_bytes_and_mod1: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100 - 1) == mod #64 x 0x100)
val lemma_bytes_and_mod2: x: uint_t 64 ->
  Lemma (logand #64 x  (0x10000 - 1) == mod #64 x 0x10000)
val lemma_bytes_and_mod3: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1000000 - 1) == mod #64 x 0x1000000)
val lemma_bytes_and_mod4: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100000000 - 1) == mod #64 x 0x100000000)
val lemma_bytes_and_mod5: x: uint_t 64 ->
  Lemma (logand #64 x  (0x10000000000 - 1) == mod #64 x 0x10000000000)
val lemma_bytes_and_mod6: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1000000000000 - 1) == mod #64 x 0x1000000000000)
val lemma_bytes_and_mod7: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100000000000000 - 1) == mod #64 x 0x100000000000000)

val lemma_bytes_and_mod: x: uint_t 64 -> y:uint_t 64 ->
  Lemma (requires (y < 8))
	(ensures (shift_left #64 y 3 < 64 /\ 
		   (shift_left #64 1 (shift_left #64 y 3)) <> 0 /\ 
		   logand #64 x (((shift_left #64 1 (shift_left #64 y 3))) - 1) == 
		     mod #64 x (shift_left #64 1 (shift_left #64 y 3))))

val lemma_bytes_power2: unit ->
Lemma (ensures (pow2 0 == 0x1 /\
	        pow2 8 == 0x100 /\
		pow2 16 == 0x10000 /\
		pow2 24 == 0x1000000 /\
		pow2 32 == 0x100000000 /\
		pow2 40 == 0x10000000000 /\
		pow2 48 == 0x1000000000000 /\
		pow2 56 == 0x100000000000000))

val lemma_bytes_shift_power2: y:uint_t 64 ->
  Lemma (requires (y < 8))
	(ensures  (shift_left #64 y 3 < 64 /\
		   y * 8 == shift_left #64 y 3 /\
		   pow2 (shift_left #64 y 3) == shift_left #64 1 (shift_left #64 y 3)))

val lowerUpper128: l:uint_t 64 -> u:uint_t 64 -> Tot (uint_t 128)

// val lemma_lowerUpper128_and: x:uint_t 128 -> x0:uint_t 64 -> x1:uint_t 64 ->
//   y:uint_t 128 -> y0:uint_t 64 -> y1:uint_t 64 ->
//   z:uint_t 128 -> z0:uint_t 64 -> z1:uint_t 64 ->
//   Lemma (requires (z0 == logand #64 x0 y0 /\
// 		   z1 == logand #64 x1 y1 /\
// 		   x == lowerUpper128 x1 x0 /\
// 		   y == lowerUpper128 y1 y0 /\
// 		   z == lowerUpper128 z1 z0))
// 	(ensures (z == logand #128 x y))

open X64.Vale.Decls  // needed for shift_right64, logand64
open X64.Machine_s   // needed for mem
val lemma_poly_bits64 : u:unit -> Lemma
  (requires True)
  (ensures
    (forall (x:nat64) . {:pattern (shift_right64 x 2)} shift_right64 x 2 == x / 4) /\
    (forall (x:nat64) . {:pattern (shift_right64 x 4)} shift_right64 x 4 == x / 16) /\
    (forall (x:nat64) . {:pattern (logand64 x 3)} logand64 x 3 == x % 4) /\
    (forall (x:nat64) . {:pattern (logand64 x 15)} logand64 x 15 == x % 16) /\
    (forall (x:nat64) . {:pattern (logand64 x 0)} logand64 x 0 == 0) /\
    (forall (x:nat64) . {:pattern (logand64 x 0xffffffffffffffff)} logand64 x 0xffffffffffffffff == x) /\
    (forall (x:nat64) . {:pattern (logand64 x 0xfffffffffffffffc)} logand64 x 0xfffffffffffffffc == (x / 4) * 4) /\
    (forall (x:nat64) . {:pattern (logand64 x 0x0ffffffc0fffffff)} logand64 x 0x0ffffffc0fffffff < nat64_max / 16) /\
    (forall (x:nat64) . {:pattern (logand64 x 0x0ffffffc0ffffffc)} logand64 x 0x0ffffffc0ffffffc < nat64_max / 16) /\
    (forall (x:nat64) . {:pattern (logand64 x 0x0ffffffc0ffffffc)} 
		   mod #64 (logand64 x 0x0ffffffc0ffffffc) 4 == 0) /\
    (forall (x:nat64)  (y:nat64) . (logand64 x y) == (logand64 y x)))
