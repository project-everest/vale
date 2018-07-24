module GF128_s
open Math.Poly2_s
open Math.Poly2.Bits_s
open FStar.Seq
open Types_s

// x^7 + x^2 + x + 1
let gf128_modulus_low_terms : poly =
  of_seq (seq_of_list [true; true; true; false; false; false; false; true])

// x^128 + x^7 + x^2 + x + 1
let gf128_modulus : poly = add (monomial 128) gf128_modulus_low_terms

let gf128_add (a b:poly) : poly = add a b
let gf128_mul (a b:poly) : poly = mod (mul a b) gf128_modulus

let gf128_to_quad32 (a:poly) : quad32 = to_quad32 (reverse a 127)
let gf128_of_quad32 (q:quad32) : poly = reverse (of_quad32 q) 127
