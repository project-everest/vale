module GHash_i

open Types_s
open GHash_s
open FStar.Seq

(*
let rec lemma_all_but_last_append (x y:seq 'a) :
  Lemma (ensures slice (append x y) 0 (length x) == x) (decreases %[length y]) =
  if length y = 0 then 
    (append_empty_r x; 
     lemma_empty y)
  else 
    lemma_all_but_last_append x (all_but_last y);
    assert(slice (append x (all_but_last y)) 0 (length x) == x);
    

let lemma_hash_append (h:quad32) (x y:ghash_plain) : 
  Lemma(ghash h (append x y) == 
	(let h_x = ghash h x in
	 ghash h_x y))
 =
 let xy = append x y in
 if length y = 1 then
   (assert (all_but_last xy == x);
    assert (last xy == last y);
    admit())
 else admit()
*)
