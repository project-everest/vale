module Math.Poly2_i
module D = Math.Poly2.Defs_s
module I = Math.Poly2.Defs_i
open FStar.Seq
unfold let max = FStar.Math.Lib.max

let all_defs =
  poly == D.poly /\
  (forall (p:poly).{:pattern (degree p)} degree p == D.degree (to_poly p)) /\
  zero == of_poly D.zero /\
  one == of_poly D.one /\
  (forall (n:nat).{:pattern (monomial n)} monomial n == of_poly (D.monomial n)) /\
  (forall (p:poly) (n:nat).{:pattern (shift p n)} shift p n == of_poly (D.shift (to_poly p) n)) /\
  (forall (p:poly) (n:nat).{:pattern (poly_index p n)} poly_index p n == D.poly_index (to_poly p) n) /\
  (forall (a b:poly).{:pattern (add a b)} add a b == of_poly (D.add (to_poly a) (to_poly b))) /\
  (forall (a b:poly).{:pattern (mul a b)} mul a b == of_poly (D.mul (to_poly a) (to_poly b))) /\
  (forall (a b:poly).{:pattern (div a b)} degree b >= 0 ==> div a b == of_poly (D.div (to_poly a) (to_poly b))) /\
  (forall (a b:poly).{:pattern (mod a b)} degree b >= 0 ==> mod a b == of_poly (D.mod (to_poly a) (to_poly b)))

let reveal_all_defs : squash all_defs = reveal_defs ()

let lemma_add_zero a = I.lemma_add_zero (to_poly a)
let lemma_add_cancel a = I.lemma_add_cancel (to_poly a)
let lemma_add_cancel_eq a b = I.lemma_add_cancel_eq (to_poly a) (to_poly b)
let lemma_add_commute a b = I.lemma_add_commute (to_poly a) (to_poly b)
let lemma_add_associate a b c = I.lemma_add_associate (to_poly a) (to_poly b) (to_poly c)
let lemma_mul_zero a = I.lemma_mul_zero (to_poly a)
let lemma_mul_one a = I.lemma_mul_one (to_poly a)
let lemma_mul_commute a b = I.lemma_mul_commute (to_poly a) (to_poly b)
let lemma_mul_associate a b c = I.lemma_mul_associate (to_poly a) (to_poly b) (to_poly c)
let lemma_mul_distribute a b c = I.lemma_mul_distribute (to_poly a) (to_poly b) (to_poly c)
let lemma_shift_is_mul a n = I.lemma_shift_is_mul (to_poly a) n
let lemma_mod_is_small a b = I.lemma_mod_is_small (to_poly a) (to_poly b)
let lemma_div_mod a b = I.lemma_div_mod (to_poly a) (to_poly b)
