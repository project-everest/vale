module Math.Poly2_i
open FStar.Seq
open Math.Poly2_s

// Fundamental lemmas
// (derived lemmas should go in Math.Poly2.Lemmas_i)

unfold let ( +. ) = add
unfold let ( *. ) = mul
unfold let ( /. ) = div
unfold let ( %. ) = mod

val lemma_equal (a b:poly) : Lemma (requires (forall (i:int). a.[i] == b.[i])) (ensures a == b)
val lemma_index_i (a:poly) (i:int) : Lemma (a.[i] ==> 0 <= i /\ i <= degree a)
val lemma_degree (a:poly) : Lemma (degree a == (-1) \/ a.[degree a])

val lemma_zero_define_i (i:int) : Lemma (not zero.[i])
val lemma_one_define_i (i:int) : Lemma (one.[i] == (i = 0))
val lemma_monomial_define_i (n:nat) (i:int) : Lemma ((monomial n).[i] == (i = n))
val lemma_shift_define_i (p:poly) (n:nat) (i:int) : Lemma ((shift p n).[i] == p.[i - n])
val lemma_reverse_define_i (p:poly) (n:nat) (i:int) : Lemma ((reverse p n).[i] == (p.[n - i] && i >= 0))

val lemma_add_zero (a:poly) : Lemma ((a +. zero) == a)
val lemma_add_cancel (a:poly) : Lemma ((a +. a) == zero)
val lemma_add_cancel_eq (a b:poly) : Lemma (requires (a +. b) == zero) (ensures a == b)
val lemma_add_commute (a b:poly) : Lemma ((a +. b) == (b +. a))
val lemma_add_associate (a b c:poly) : Lemma ((a +. (b +. c)) == ((a +. b) +. c))
val lemma_add_define_i (a b:poly) (i:int) : Lemma ((a +. b).[i] == (a.[i] <> b.[i]))
val lemma_add_degree (a b:poly) : Lemma
  (degree (a +. b) <= degree a \/ degree (a +. b) <= degree b)
  [SMTPat (degree (a +. b))]

val lemma_mul_zero (a:poly) : Lemma ((a *. zero) == zero)
val lemma_mul_one (a:poly) : Lemma ((a *. one) == a)
val lemma_mul_commute (a b:poly) : Lemma ((a *. b) == (b *. a))
val lemma_mul_associate (a b c:poly) : Lemma (a *. (b *. c) == (a *. b) *. c)
val lemma_mul_distribute (a b c:poly) : Lemma (a *. (b +. c) == (a *. b) +. (a *. c))
val lemma_mul_degree (a b:poly) : Lemma
  (degree (a *. b) == (if degree a >= 0 && degree b >= 0 then degree a + degree b else -1))
  [SMTPat (degree (a *. b))]
val lemma_mul_reverse (a b:poly) (n:nat) : Lemma
  (requires degree a <= n /\ degree b <= n)
  (ensures reverse (a *. b) (n + n) == reverse a n *. reverse b n)

val lemma_shift_is_mul (a:poly) (n:nat) : Lemma (shift a n == a *. (monomial n))

val lemma_div_mod (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures a == (a /. b) *. b +. (a %. b))

val lemma_div_degree (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures degree (a /. b) == (if degree a < degree b then -1 else degree a - degree b))
  [SMTPat (degree (a /. b))]

val lemma_mod_degree (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures degree (a %. b) < degree b)
  [SMTPat (degree (a %. b))]
