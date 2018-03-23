module Collections.Seqs_s

open FStar.Seq

let all_but_last (s:seq 'a {length s > 0}) = 
  slice s 0 (length s - 1)

let rec reverse_seq (#a:eqtype) (s:seq a) : Tot (s':seq a {length s' == length s}) (decreases %[length s]) =
  if length s = 0 then createEmpty 
  else (lemma_empty s; append (reverse_seq (tail s)) (create 1 (head s)))
