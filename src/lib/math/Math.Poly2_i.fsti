module Math.Poly2_i
open FStar.Seq
open Math.Poly2_s

unfold let ( +. ) = add
unfold let ( *. ) = mul

val lemma_add_zero (a:poly) : Lemma ((a +. zero) == a)
val lemma_add_cancel (a:poly) : Lemma ((a +. a) == zero)
val lemma_add_cancel_eq (a b:poly) : Lemma (requires (a +. b) == zero) (ensures a == b)
val lemma_add_commute (a b:poly) : Lemma ((a +. b) == (b +. a))
val lemma_add_associate (a b c:poly) : Lemma ((a +. (b +. c)) == ((a +. b) +. c))
val lemma_mul_zero (a:poly) : Lemma ((a *. zero) == zero)
val lemma_mul_one (a:poly) : Lemma ((a *. one) == a)
val lemma_mul_commute (a b:poly) : Lemma ((a *. b) == (b *. a))
val lemma_mul_associate (a b c:poly) : Lemma (a *. (b *. c) == (a *. b) *. c)
val lemma_mul_distribute (a b c:poly) : Lemma (a *. (b +. c) == (a *. b) +. (a *. c))
