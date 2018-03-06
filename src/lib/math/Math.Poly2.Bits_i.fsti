module Math.Poly2.Bits_i
open Types_s
open Types_i
open Math.Poly2_s
open Math.Poly2.Bits_s
open Math.Poly2_i
open Math.Poly2.Lemmas_i
open FStar.Seq
open FStar.UInt

val lemma_add128 (a b:poly) : Lemma
  (requires degree a <= 127 /\ degree b <= 127)
  (ensures to_quad32 (a +. b) == quad32_xor (to_quad32 a) (to_quad32 b))

val lemma_quad32_double (a:poly) : Lemma
  (requires degree a <= 127)
  (ensures
    of_double32 (quad32_double_lo (to_quad32 a)) == a %. monomial 64 /\
    of_double32 (quad32_double_hi (to_quad32 a)) == a /. monomial 64 /\
    a == (a /. monomial 64) *. monomial 64 +. a %. monomial 64 /\
    (a /. monomial 64) *. monomial 64 == shift (a /. monomial 64) 64
  )

val lemma_quad32_double_shift (a:poly) : Lemma
  (requires degree a <= 127)
  (ensures (
    let Quad32 q0 q1 q2 q3 = to_quad32 a in
    Quad32 0 0 q0 q1 == to_quad32 ((a %. monomial 64) *. monomial 64) /\
    Quad32 q2 q3 0 0 == to_quad32 (a /. monomial 64)
  ))

