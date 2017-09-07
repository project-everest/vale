module Bitvectors128

open FStar.UInt
open FStar.BV
open FStar.Mul

let lowerUpper128 (l u : FStar.UInt.uint_t 64) : FStar.UInt.uint_t 128 = 
  l + (0x10000000000000000 * u)
let bv128_64_64 x1 x0 = bvor (bvshl (bv_uext #64 #64 x1) 64) (bv_uext #64 #64 x0)

val lemma_bv128_lowerUpper : x0:uint_t 64 -> x1:uint_t 64 ->
  Lemma(lowerUpper128 x0 x1 == bv2int (bv128_64_64 (int2bv x1) (int2bv x0)))

val lemma_bv128_lowerUpper_B128 : x0:uint_t 64 -> x1:uint_t 64 ->
  Lemma (int2bv #128 (lowerUpper128 x0 x1) == bv128_64_64 (int2bv x1) (int2bv x0))

val lemma_bv128_64_64_and: x:bv_t 128 -> x0:bv_t 64 -> x1:bv_t 64 ->
  y:bv_t 128 -> y0:bv_t 64 -> y1:bv_t 64 ->
  z:bv_t 128 -> z0:bv_t 64 -> z1:bv_t 64 ->
  Lemma (requires (z0 == bvand #64 x0 y0 /\
		   z1 == bvand #64 x1 y1 /\
		   x == bv128_64_64 x1 x0 /\
		   y == bv128_64_64 y1 y0 /\
		   z == bv128_64_64 z1 z0))
	(ensures (z == bvand #128 x y))


