module GHash_s

open Types_s
open GF128_s
open Collections.Seqs_s
open FStar.Mul
open FStar.Seq

type ghash_plain = s:seq quad32 { length s > 0 }

let rec ghash (h:quad32) (x:ghash_plain) : Tot quad32 (decreases %[length x]) = 
  let h_poly = gf128_of_quad32 h in
  let y_i_minus_1 =
    (if length x = 1 then
       Quad32 0 0 0 0
     else
       ghash h (all_but_last x)) in
  let x_i = last x in
  let xor_poly = gf128_of_quad32 (quad32_xor y_i_minus_1 x_i) in
  gf128_to_quad32 (gf128_mul xor_poly h_poly)

