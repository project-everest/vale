module Types_i

open Types_s

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Quad32 v0 v1 v2 v3 = q in
  Quad32 0 v0 v1 v2

assume val lemma_BitwiseXorCommutative (x y:nat32) : Lemma (x *^ y == y *^ x)
assume val lemma_BitwiseXorWithZero (n:nat32) : Lemma (n *^ 0 == n)
assume val lemma_BitwiseXorCancel (n:nat32) : Lemma (n *^ n == 0)
assume val lemma_BitwiseXorAssociative (x y z:nat32) : Lemma (x *^ (y *^ z) == (x *^ y) *^ z)

assume val xor_lemmas (_:unit) : Lemma
  (ensures
    (forall (x y:nat32).{:pattern (x *^ y)} x *^ y == y *^ x) /\
    (forall (n:nat32).{:pattern (n *^ 0)} n *^ 0 == n) /\
    (forall (n:nat32).{:pattern (n *^ n)} n *^ n == 0) /\
    (forall (x y z:nat32).{:pattern (x *^ (y *^ z))} x *^ (y *^ z) == (x *^ y) *^ z)
  )

let lemma_quad32_xor () : Lemma (forall q . {:pattern quad32_xor q q} quad32_xor q q == Quad32 0 0 0 0) =
  xor_lemmas()
