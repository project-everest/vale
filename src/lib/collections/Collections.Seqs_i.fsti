module Collections.Seqs_i

open Collections.Seqs_s
open FStar.Seq

val lemma_slice_first_exactly_in_append (#a:Type) (x y:seq a) :
  Lemma (slice (append x y) 0 (length x) == x)

val lemma_all_but_last_append (#t:Type) (a:seq t) (b:seq t{length b > 0}) :
  Lemma (all_but_last (append a b) == append a (all_but_last b))

val reverse_seq_append (#a:eqtype) (s:seq a) (t:seq a) :
  Lemma(ensures reverse_seq (append s t) == append (reverse_seq t) (reverse_seq s))

val reverse_reverse_seq (#a:Type) (s:seq a) : 
  Lemma(ensures reverse_seq (reverse_seq s) == s)
  [SMTPat (reverse_seq (reverse_seq s))]
