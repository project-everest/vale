module GHash_i

open Types_s
open GHash_s
open GF128_s
open Collections.Seqs_s
open Collections.Seqs_i
open FStar.Seq

#reset-options "--use_two_phase_tc true"
let rec ghash_incremental (h:quad32) (y_prev:quad32) (x:ghash_plain) : Tot quad32 (decreases %[length x]) = 
  let h_poly = gf128_of_quad32 h in
  let y_i_minus_1 =
    (if length x = 1 then
       y_prev
     else
       ghash_incremental h y_prev (all_but_last x)) in
  let x_i = last x in
  let xor_poly = gf128_of_quad32 (quad32_xor y_i_minus_1 x_i) in
  gf128_to_quad32 (gf128_mul xor_poly h_poly)

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
   
let lemma_hash_append3 (h y_init y_mid1 y_mid2 y_final:quad32) (s1 s2 s3:seq quad32) : Lemma
  (requires y_init = Quad32 0 0 0 0 /\
            y_mid1 = (if length s1 > 0 then ghash_incremental h y_init s1 else y_init) /\
            y_mid2 = (if length s2 > 0 then ghash_incremental h y_mid1 s2 else y_mid1) /\
            length s3 > 0 /\
            y_final = ghash_incremental h y_mid2 s3)
  (ensures y_final == ghash h (append s1 (append s2 s3)))
  =
  let s23 = append s2 s3 in
  let s123 = append s1 s23 in
  if length s1 = 0 then (
    assert(eq s123 s23);
    if length s2 = 0 then (
      assert(eq s123 s3);
      ghash_incremental_to_ghash h s3
    ) else
      lemma_hash_append h y_mid1 s2 s3;
      ghash_incremental_to_ghash h s23
  ) else if length s2 = 0 then (
    assert(eq s123 (append s1 s3));
    lemma_hash_append h y_init s1 s3;
    ghash_incremental_to_ghash h (append s1 s3)
  ) else (
    lemma_hash_append h y_init s1 s23;
    lemma_hash_append h y_mid1 s2 s3;
    ghash_incremental_to_ghash h s123;
    ()
  )
