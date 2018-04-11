module Collections.Seqs_s
open FStar.Seq

unfold let seq_map (#a #b:Type) (f:a -> b) (s:seq a) : seq b =
  init (length s) (fun i -> f (index s i))

let all_but_last (s:seq 'a {length s > 0}) = 
  slice s 0 (length s - 1)

let reverse_seq (#a:Type) (s:seq a) : seq a =
  init (length s) (fun i -> index s (length s - i - 1))

