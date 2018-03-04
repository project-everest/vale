module GHash_i

open Types_s
open GHash_s
open GF128_s
open FStar.Seq

let lemma_slice_first_exactly_in_append (#a:eqtype) (x y:seq a) :
  Lemma (slice (append x y) 0 (length x) == x) =
  let xy = append x y in
  let xy_slice = slice xy 0 (length x) in
  let x_slice = slice x 0 (length x) in
  assert(eq xy_slice x_slice);   // OBSERVE: extensionality
  //assert(eq x_slice x);
  ()

#reset-options "--use_two_phase_tc true"
let lemma_all_but_last_append (#t:eqtype) (a:seq t) (b:seq t{length b > 0}) :
  Lemma (all_but_last (append a b) == append a (all_but_last b)) =
  let ab = all_but_last (append a b) in
  let app_a_b = append a (all_but_last b) in
  (*
  assert(length ab == length app_a_b);
  let helper (i:int) : Lemma (0 <= i /\ i < length ab ==> index ab i == index app_a_b i) =
    if 0 <= i && i < length ab then (
      if i < length a then ()
      else ()
    ) else ()
  in
  FStar.Classical.forall_intro helper;
  *)
  assert (eq ab app_a_b)  // OBSERVE: extensionality

let rec ghash_incremental (h:quad32) (y_prev:quad32) (x:ghash_plain) : Tot quad32 (decreases %[length x]) = 
  let h_poly = of_quad32 h in
  let y_i_minus_1 =
    (if length x = 1 then
       y_prev
     else
       ghash_incremental h y_prev (all_but_last x)) in
  let x_i = last x in
  let xor_poly = of_quad32 (quad32_xor y_i_minus_1 x_i) in
  to_quad32 (gf128_mul xor_poly h_poly)

let rec ghash_incremental_to_ghash (h:quad32) (x:ghash_plain) :
  Lemma(ensures ghash_incremental h (Quad32 0 0 0 0) x == ghash h x)
       (decreases %[length x])
  =
  if length x = 1 then ()
  else ghash_incremental_to_ghash h (all_but_last x)

let rec lemma_hash_append (h:quad32) (y_prev:quad32) (a b:ghash_plain) : 
  Lemma(ensures 
        ghash_incremental h y_prev (append a b) == 
	(let y_a = ghash_incremental h y_prev a in
	 ghash_incremental h y_a b))
	(decreases %[length b])
  =
  let ab = append a b in
  assert (last ab == last b);
  if length b = 1 then
    (lemma_slice_first_exactly_in_append a b;
     assert (all_but_last ab == a);
     ())
  else 
    lemma_hash_append h y_prev a (all_but_last b);
    lemma_all_but_last_append a b;
    assert(all_but_last ab == append a (all_but_last b));
  ()
   
