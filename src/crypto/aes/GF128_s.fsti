module GF128_s
open Math.Poly2_s
open FStar.Seq
open Types_s

// x^7 + x^2 + x + 1
let gf128_modulus_low_terms : poly =
  of_seq (of_list [true; true; true; false; false; false; false; true])

// x^128 + x^7 + x^2 + x + 1
let gf128_modulus : poly = add (monomial 128) gf128_modulus_low_terms

let gf128_add (a b:poly) : poly = add a b
let gf128_mul (a b:poly) : poly = mod (mul a b) gf128_modulus

// forward representation: low bit of low word is x^0, high bit of high word is x^127
val to_quad32 (a:poly) : quad32
val of_quad32 (q:quad32) : poly

// reverse representation: low bit of low word is x^127, high bit of high word is x^0
val to_quad32_rev (a:poly) : quad32
val of_quad32_rev (q:quad32) : poly

