module Math.Poly2.Lemmas_i
open Math.Poly2_s
open Math.Poly2_i

// Derived lemmas (see Math.Poly2_i for fundamental lemmas)

val lemma_zero_define (_:unit) : Lemma (forall (i:int).{:pattern zero.[i]} not zero.[i])
val lemma_zero_degree (_:unit) : Lemma (degree zero == -1)
val lemma_degree_negative (a:poly) : Lemma (requires degree a < 0) (ensures a == zero)

val lemma_add_define (a b:poly) : Lemma
  (forall (i:int).{:pattern (a +. b).[i] \/ a.[i] \/ b.[i]} (a +. b).[i] == (a.[i] <> b.[i]))

val lemma_add_define_all (_:unit) : Lemma
  (forall (a b:poly).{:pattern (a +. b)}
    (forall (i:int).{:pattern (a +. b).[i] \/ a.[i] \/ b.[i]} (a +. b).[i] == (a.[i] <> b.[i])))

val lemma_mul_distribute_left (a b c:poly) : Lemma ((a +. b) *. c == (a *. c) +. (b *. c))
val lemma_mul_distribute_right (a b c:poly) : Lemma (a *. (b +. c) == (a *. b) +. (a *. c))

val lemma_mul_smaller_is_zero (a b:poly) : Lemma
  (requires degree b > degree (a *. b))
  (ensures a == zero /\ a *. b == zero)

val lemma_mod_distribute (a b c:poly) : Lemma
  (requires degree c >= 0)
  (ensures (a +. b) %. c == (a %. c) +. (b %. c))

val lemma_div_mod_unique (a b x y:poly) : Lemma
  (requires
    degree b >= 0 /\
    degree y < degree b /\
    a == x *. b +. y
  )
  (ensures
    x == a /. b /\
    y == a %. b
  )

val lemma_div_mod_exact (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures (a *. b) /. b == a /\ (a *. b) %. b == zero)

val lemma_mod_small (a b:poly) : Lemma
  (requires degree b >= 0 /\ degree a < degree b)
  (ensures a %. b == a)

val lemma_mod_mod (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures (a %. b) %. b == a %. b)

val lemma_mod_cancel (a:poly) : Lemma
  (requires degree a >= 0)
  (ensures a %. a == zero)

val lemma_mod_mul_mod (a b c:poly) : Lemma
  (requires degree b >= 0)
  (ensures ((a %. b) *. c) %. b == (a *. c) %. b)
