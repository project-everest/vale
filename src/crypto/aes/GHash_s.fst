module GHash_s

open Types_s
open GF128_s
open FStar.Mul
open FStar.Seq

type ghash_plain = s:seq quad32 { length s > 0 }

let all_but_last (s:seq 'a {length s > 0}) = 
  slice s 0 (length s - 1)

let rec ghash (h:quad32) (x:ghash_plain) : Tot quad32 (decreases %[length x]) = 
  let h_poly = of_quad32 h in
  let y_i_minus_1 =
    (if length x = 1 then
       Quad32 0 0 0 0
     else
       ghash h (all_but_last x)) in
  let x_i = last x in
  let xor_poly = of_quad32 (quad32_xor y_i_minus_1 x_i) in
  to_quad32 (gf128_mul xor_poly h_poly)

