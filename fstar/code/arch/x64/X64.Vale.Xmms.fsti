module X64.Vale.Xmms
// This interface should not refer to Semantics_s

open Defs_s
open Prop_s
open X64.Machine_s

type t = xmms_t

val equal (xmms1:t) (xmms2:t) : prop0

val lemma_equal_intro (xmms1:t) (xmms2:t) : Lemma
  (requires forall (x:xmm). xmms1 x == xmms2 x)
  (ensures equal xmms1 xmms2)
  [SMTPat (equal xmms1 xmms2)]

val lemma_equal_elim (xmms1:t) (xmms2:t) : Lemma
  (requires equal xmms1 xmms2)
  (ensures xmms1 == xmms2)
  [SMTPat (equal xmms1 xmms2)]

