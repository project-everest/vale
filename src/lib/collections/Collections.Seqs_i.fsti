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

val seq_map_i_indexed (#a:Type) (#b:Type) (f:int->a->b) (s:seq a) (i:int) : 
  Tot (s':seq b { length s' == length s /\
                  (forall j . {:pattern index s' j} 0 <= j /\ j < length s ==> index s' j == f (i + j) (index s j))
                }) 

val seq_map_i (#a:Type) (#b:Type) (f:int->a->b) (s:seq a) :
  Tot (s':seq b { length s' == length s /\
                  (forall j . {:pattern index s' j} 0 <= j /\ j < length s ==> index s' j == f j (index s j))
                }) 

val seq_map_internal_associative (#a:Type) (#b:eqtype) (f:int->a->b) (s:seq a) (pivot:int{0 <= pivot /\ pivot < length s}) :
  Lemma (let left,right = split s pivot in
         seq_map_i f s == seq_map_i_indexed f left 0 @| seq_map_i_indexed f right pivot )
