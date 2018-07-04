module X64.Vale.Xmms_i
// This interface should not refer to Semantics_s

open X64.Machine_s
unfold let quad32 = Types_s.quad32

type t = Map16_i.map quad32

val equal : xmms1:t -> xmms2:t -> Type0

val lemma_equal_intro : xmms1:t -> xmms2:t -> Lemma
  (requires forall (x:xmm). Map16_i.sel xmms1 x == Map16_i.sel xmms2 x)
  (ensures equal xmms1 xmms2)
  [SMTPat (equal xmms1 xmms2)]

val lemma_equal_elim : xmms1:t -> xmms2:t -> Lemma
  (requires equal xmms1 xmms2)
  (ensures xmms1 == xmms2)
  [SMTPat (equal xmms1 xmms2)]

