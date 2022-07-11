module PPC64LE.Vale.Vecs
// This interface should not refer to Semantics_s

open Prop_s
open PPC64LE.Machine_s

type t = vecs_t

val equal (vecs1:t) (vecs2:t) : prop0

val lemma_equal_intro (vecs1:t) (vecs2:t) : Lemma
  (requires forall (x:vec). vecs1 x == vecs2 x)
  (ensures equal vecs1 vecs2)
  [SMTPat (equal vecs1 vecs2)]

val lemma_equal_elim (vecs1:t) (vecs2:t) : Lemma
  (requires equal vecs1 vecs2)
  (ensures vecs1 == vecs2)
  [SMTPat (equal vecs1 vecs2)]

