module Types_i

open Types_s
open Collections.Seqs_s
open Collections.Seqs_i
open FStar.Seq

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Quad32 v0 v1 v2 v3 = q in
  Quad32 0 v0 v1 v2

val lemma_BitwiseXorCommutative (x y:nat32) : Lemma (x *^ y == y *^ x)
val lemma_BitwiseXorWithZero (n:nat32) : Lemma (n *^ 0 == n)
val lemma_BitwiseXorCancel (n:nat32) : Lemma (n *^ n == 0)
val lemma_BitwiseXorAssociative (x y z:nat32) : Lemma (x *^ (y *^ z) == (x *^ y) *^ z)

val xor_lemmas (_:unit) : Lemma
  (ensures
    (forall (x y:nat32).{:pattern (x *^ y)} x *^ y == y *^ x) /\
    (forall (n:nat32).{:pattern (n *^ 0)} n *^ 0 == n) /\
    (forall (n:nat32).{:pattern (n *^ n)} n *^ n == 0) /\
    (forall (x y z:nat32).{:pattern (x *^ (y *^ z))} x *^ (y *^ z) == (x *^ y) *^ z)
  )

val lemma_quad32_xor (_:unit) : Lemma (forall q . {:pattern quad32_xor q q} quad32_xor q q == Quad32 0 0 0 0)

let quad32_double_lo (q:quad32) : double32 =
  let Quad32 q0 q1 q2 q3 = q in
  Double32 q0 q1

let quad32_double_hi (q:quad32) : double32 =
  let Quad32 q0 q1 q2 q3 = q in
  Double32 q2 q3

val lemma_reverse_reverse_bytes_nat32 (n:nat32) :
  Lemma (reverse_bytes_nat32 (reverse_bytes_nat32 n) == n)
  [SMTPat (reverse_bytes_nat32 (reverse_bytes_nat32 n))]

let lemma_reverse_bytes_quad32 (q:quad32) : 
  Lemma (reverse_bytes_quad32 (reverse_bytes_quad32 q) == q)
  [SMTPat (reverse_bytes_quad32 (reverse_bytes_quad32 q))]
  = ()

val lemma_reverse_reverse_bytes_nat32_seq (s:seq nat32) :
  Lemma (ensures reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s) == s)
  (decreases %[length s])
  [SMTPat (reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s))]
  
val quad32_to_seq (q:quad32) : 
  Tot (s:seq nat32 { length s == 4 /\ 
                     (let q' = Quad32 (index s 0) (index s 1) (index s 2) (index s 3) in
                      q == q')           
                   })


