module Types_i

open Types_s
open Collections.Seqs_s
open Collections.Seqs_i
open Words_s
open Words.Four_s
open Words.Seq_s
open FStar.Seq

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Mkfour v0 v1 v2 v3 = q in
  Mkfour 0 v0 v1 v2

val lemma_BitwiseXorCommutative (x y:nat32) : Lemma (x *^ y == y *^ x)
val lemma_BitwiseXorWithZero (n:nat32) : Lemma (n *^ 0 == n)
val lemma_BitwiseXorCancel (n:nat32) : Lemma (n *^ n == 0)
val lemma_BitwiseXorCancel64 (n:nat64) : Lemma (ixor n n == 0)
val lemma_BitwiseXorAssociative (x y z:nat32) : Lemma (x *^ (y *^ z) == (x *^ y) *^ z)

val xor_lemmas (_:unit) : Lemma
  (ensures
    (forall (x y:nat32).{:pattern (x *^ y)} x *^ y == y *^ x) /\
    (forall (n:nat32).{:pattern (n *^ 0)} n *^ 0 == n) /\
    (forall (n:nat32).{:pattern (n *^ n)} n *^ n == 0) /\
    (forall (n:nat64).{:pattern (ixor n n)} ixor n n == 0) /\
    (forall (x y z:nat32).{:pattern (x *^ (y *^ z))} x *^ (y *^ z) == (x *^ y) *^ z)
  )

val lemma_quad32_xor (_:unit) : Lemma (forall q . {:pattern quad32_xor q q} quad32_xor q q == Mkfour 0 0 0 0)

let quad32_double_lo (q:quad32) : double32 = (four_to_two_two q).lo
let quad32_double_hi (q:quad32) : double32 = (four_to_two_two q).hi

val lemma_reverse_reverse_bytes_nat32 (n:nat32) :
  Lemma (reverse_bytes_nat32 (reverse_bytes_nat32 n) == n)
  [SMTPat (reverse_bytes_nat32 (reverse_bytes_nat32 n))]

let lemma_reverse_bytes_quad32 (q:quad32) : 
  Lemma (reverse_bytes_quad32 (reverse_bytes_quad32 q) == q)
  [SMTPat (reverse_bytes_quad32 (reverse_bytes_quad32 q))]
  = ()

val lemma_reverse_reverse_bytes_nat32_seq (s:seq nat32) :
  Lemma (ensures reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s) == s)
  [SMTPat (reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s))]

unfold let quad32_to_seq (q:quad32) = four_to_seq_LE q
