module Collections.Seqs_i

let lemma_slice_first_exactly_in_append (#a:Type) (x y:seq a) :
  Lemma (slice (append x y) 0 (length x) == x) =
  let xy = append x y in
  let xy_slice = slice xy 0 (length x) in
  let x_slice = slice x 0 (length x) in
  assert(equal xy_slice x_slice);   // OBSERVE: extensionality
  ()

let lemma_all_but_last_append (#t:Type) (a:seq t) (b:seq t{length b > 0}) :
  Lemma (all_but_last (append a b) == append a (all_but_last b)) =
  let ab = all_but_last (append a b) in
  let app_a_b = append a (all_but_last b) in
  assert (equal ab app_a_b)  // OBSERVE: extensionality

let reverse_seq_append (#a:eqtype) (s:seq a) (t:seq a) : 
  Lemma(ensures reverse_seq (append s t) == append (reverse_seq t) (reverse_seq s))
  =
  assert (equal (reverse_seq (append s t)) (append (reverse_seq t) (reverse_seq s)))

let reverse_reverse_seq (#a:Type) (s:seq a) : 
  Lemma(ensures reverse_seq (reverse_seq s) == s)
  =
  assert (equal (reverse_seq (reverse_seq s)) s)
