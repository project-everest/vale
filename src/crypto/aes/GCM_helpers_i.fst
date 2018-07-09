module GCM_helpers_i

open FStar.Tactics
open Words_s
open Words.Seq_s
open Types_s
open Types_i
open FStar.Mul
open FStar.Seq
open Opaque_s
open Words.Four_s
open AES_s 
open GCTR_s
open FStar.Math.Lemmas
open Collections.Seqs_i

let slice_work_around (s:seq 'a) (i:int) =
  if 0 <= i && i <= length s then slice s 0 i 
  else slice s 0 0

let index_work_around_quad32 (s:seq quad32) (i:int) =
  if 0 <= i && i < length s then index s i
  else Mkfour 0 0 0 0

let extra_bytes_helper (n:nat) : Lemma
  (requires n % 16 <> 0)
  (ensures bytes_to_quad_size n == n / 16 + 1)
  =
  ()

let bytes_to_quad_size_no_extra_bytes num_bytes = ()
let no_extra_bytes_helper s num_bytes = ()

let le_seq_quad32_to_bytes_tail_prefix (s:seq quad32) (num_bytes:nat) =
  let num_extra = num_bytes % 16 in
  let num_blocks = num_bytes / 16 in
  let final = index s num_blocks in
  let x  = slice (le_seq_quad32_to_bytes s) (num_blocks * 16) num_bytes in
  let x' = slice (le_quad32_to_bytes final) 0 num_extra in

  le_seq_quad32_to_bytes_of_singleton final;
  assert (le_quad32_to_bytes final == le_seq_quad32_to_bytes (create 1 final));
  assert (equal (create 1 final) (slice s num_blocks (length s)));

  assert (x' == slice (le_seq_quad32_to_bytes (slice s num_blocks (length s))) 0 num_extra);
  slice_commutes_le_seq_quad32_to_bytes s num_blocks (length s);
  assert (x' == slice (slice (le_seq_quad32_to_bytes s) (num_blocks * 16) (length s * 16)) 0 num_extra);
  assert (x' == slice (le_seq_quad32_to_bytes s) (num_blocks * 16) num_bytes);

  assert (equal x' x);
  ()

let index_helper (s:seq quad32) (num_bytes:int) : Lemma
  (requires 1 <= num_bytes /\
             num_bytes < 16 * length s /\
             16 * (length s - 1) < num_bytes /\
             num_bytes % 16 <> 0 /\
             length s == bytes_to_quad_size num_bytes)
  (ensures (let num_blocks = num_bytes / 16 in
            index s num_blocks == index_work_around_quad32 (slice_work_around s (bytes_to_quad_size num_bytes)) num_blocks))
  =
  ()

let pad_to_128_bits_multiples (b:seq nat8) : Lemma
  (let full_blocks = (length b) / 16 * 16 in
   let full_bytes, partial_bytes = split b full_blocks in
   pad_to_128_bits b == full_bytes @| pad_to_128_bits partial_bytes)
  =
  let full_blocks = (length b) / 16 * 16 in
  let full_bytes, partial_bytes = split b full_blocks in
  if length b < 16 then (
    assert (full_bytes == createEmpty);
    assert (partial_bytes == b);
    append_empty_l(pad_to_128_bits partial_bytes);
    ()
  ) else (
    assert (length full_bytes + length partial_bytes == length b);
    assert (length full_bytes % 16 == 0);
    let num_extra_bytes = length b % 16 in
    assert (num_extra_bytes == (length partial_bytes) % 16);
    if num_extra_bytes = 0 then (
      lemma_split b full_blocks;
      assert (b == full_bytes @| partial_bytes);
      ()
    ) else (
      let pad = create (16 - num_extra_bytes) 0 in
      assert (equal (b @| pad) (full_bytes @| (partial_bytes @| pad)));
      ()
    );
    ()
  )

let pad_to_128_bits_le_quad32_to_bytes (s:seq quad32) (num_bytes:int) =
  let num_extra = num_bytes % 16 in
  let num_blocks = num_bytes / 16 in
  let full_quads,final_quads = split s num_blocks in
  assert(length final_quads == 1);
  let final_quad = index final_quads 0 in
  let b = slice (le_seq_quad32_to_bytes s) 0 num_bytes in
  pad_to_128_bits_multiples b; // ==>  pad_to_128_bits b == full_bytes @| pad_to_128_bits partial_bytes
  let full_blocks = (length b) / 16 * 16 in
  let full_bytes, partial_bytes = split b full_blocks in
  // Need to show that full_bytes == le_seq_quad32_to_bytes full_quads
  // Need to show that le_quad32_to_bytes final_quad == partial_bytes

  // full_bytes == slice (slice (le_seq_quad32_to_bytes s) 0 num_bytes) 0 full_blocks
  // This should be from slice_slice
  //            == slice (le_seq_quad32_bot_bytes s) 0 full_blocks
  //            == slice (le_seq_quad32_bot_bytes s) 0 (num_blocks * 16)
  //    This follows from slice_commutes_le_seq_quad32_to_bytes0
  // le_seq_quad32_to_bytes full_quads == le_seq_quad32_to_bytes (slice s 0 num_blocks)

  slice_commutes_le_seq_quad32_to_bytes0 s num_blocks;  
  // ==>
  (*
    assert (slice (le_seq_quad32_to_bytes s) 0 (num_blocks * 16) ==
            le_seq_quad32_to_bytes (slice s 0 num_blocks));
  *)
  slice_slice (le_seq_quad32_to_bytes s) 0 num_bytes 0 full_blocks;
  assert (full_bytes == le_seq_quad32_to_bytes full_quads);

  // slice (le_quad32_to_bytes final_quad) 0 num_extra == slice (le_quad32_to_bytes (index (slice s num_blocks (length s)) 0)) 0 num_extra
  // F* believes assert (final_quad == index s num_blocks), so we have:
  //               == slice (le_quad32_to_bytes (index s num_blocks)) 0 num_extra
  //
  //               == slice (le_quad32_to_bytes (index s num_blocks)) 0 num_extra 
  // from le_seq_quad32_to_bytes_tail_prefix
  //               == slice (le_seq_quad32_to_bytes s) (num_blocks * 16) num_bytes
  //               == slice (le_seq_quad32_to_bytes s) full_blocks num_bytes
  //  From slice_slice
  // partial_bytes == slice (slice (le_seq_quad32_to_bytes s) 0 num_bytes) full_blocks num_bytes 
  
  slice_slice (le_seq_quad32_to_bytes s) 0 num_bytes full_blocks num_bytes;
  le_seq_quad32_to_bytes_tail_prefix s num_bytes;
  ()


(*
let slice_le_quad32_to_bytes_is_mod (q:quad32) (num_bytes:int) : Lemma
  (requires 1 <= num_bytes /\ num_bytes < 16)
  (ensures four_to_nat 32 (slice (le_quad32_to_bytes q) 0 num_bytes) == (four_to_nat 32 q) % (pow2 (8*num_bytes)))
  =
  ()
      
let insert_0_is_padding (q:quad32) : 
  Lemma (let q' = insert_nat64 q 0 1 in
         q' == le_bytes_to_quad32 (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 8)))
  =
  ()
*)


#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=true --max_fuel 2 --initial_fuel 2 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.nl_arith_repr native --z3rlimit 10"
let le_quad32_to_bytes_sel (q : quad32) (i:nat{i < 16}) :
    Lemma(let Mkfour q0 q1 q2 q3 = q in
	      (i < 4 ==> index (le_quad32_to_bytes q) i = four_select (nat_to_four 8 q0) (i % 4)) /\
	      (4 <= i /\ i < 8 ==> index (le_quad32_to_bytes q) i = four_select (nat_to_four 8 q1) (i % 4)) /\
 	      (8 <= i /\ i < 12  ==> index (le_quad32_to_bytes q) i = four_select (nat_to_four 8 q2) (i % 4)) /\
	      (12 <= i /\ i < 16 ==> index (le_quad32_to_bytes q) i = four_select (nat_to_four 8 q3) (i % 4)))
  = reveal_opaque (le_quad32_to_bytes_def);
    let Mkfour q0 q1 q2 q3 = q in
    assert (index (Words.Seq_s.four_to_seq_LE q) 0 == q0);
    assert (index (Words.Seq_s.four_to_seq_LE q) 1 == q1);
    assert (index (Words.Seq_s.four_to_seq_LE q) 2 == q2);
    assert (index (Words.Seq_s.four_to_seq_LE q) 3 == q3);
    let Mkfour q00 q01 q02 q03 = nat_to_four 8 q0 in
    let Mkfour q10 q11 q12 q13 = nat_to_four 8 q1 in
    let Mkfour q20 q21 q22 q23 = nat_to_four 8 q2 in
    let Mkfour q30 q31 q32 q33 = nat_to_four 8 q3 in
    assert_by_tactic (four_select (nat_to_four 8 q0) 0 == q00)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q0) 1 == q01)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q0) 2 == q02)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q0) 3 == q03)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);

    assert_by_tactic (four_select (nat_to_four 8 q1) 0 == q10)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q1) 1 == q11)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q1) 2 == q12)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q1) 3 == q13)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);

    assert_by_tactic (four_select (nat_to_four 8 q2) 0 == q20)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q2) 1 == q21)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q2) 2 == q22)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q2) 3 == q23)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);

    assert_by_tactic (four_select (nat_to_four 8 q3) 0 == q30)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q3) 1 == q31)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q3) 2 == q32)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
    assert_by_tactic (four_select (nat_to_four 8 q3) 3 == q33)
      (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);

    assert(i < 4 ==> (fun n ->
	four_select (index (init (length (four_to_seq_LE q))
                           (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
			     (n / 4))
			 (n % 4)) i == four_select (nat_to_four 8 q0) i);
    assert(4 <= i /\ i < 8 ==> (fun n ->
      four_select (index (init (length (four_to_seq_LE q))
                       (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
		  (n / 4))
		     (n % 4)) i == four_select (nat_to_four 8 q1) (i % 4));
    assert(8 <= i /\ i < 12 ==> (fun n ->
      four_select (index (init (length (four_to_seq_LE q))
                       (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
		  (n / 4))
		     (n % 4)) i == four_select (nat_to_four 8 q2) (i % 4));
    assert(12 <= i /\ i < 16 ==> (fun n ->
      four_select (index (init (length (four_to_seq_LE q))
                       (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
		  (n / 4))
		     (n % 4)) i == four_select (nat_to_four 8 q3) (i % 4));
    assert_by_tactic (i < 16 ==> index (le_quad32_to_bytes_def q) i = 
		     (index (init (length (init (length (four_to_seq_LE q))
			   (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x))) *
								       4)
			   (fun n ->
			     four_select (index (init (length (four_to_seq_LE q))
					 (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
			     (n / 4))
			   (n % 4))) i))
    			 (fun () -> norm[primops; delta_only ["Types_s.le_quad32_to_bytes_def"; 
    			 "Collections.Seqs_s.seq_map"; "Collections.Seqs_s.compose"; 
    			 "Words.Seq_s.seq_four_to_seq_LE"]]; dump " after norm2");
  assert(i < 4 ==> index (le_quad32_to_bytes_def q) i == four_select (nat_to_four 8 q0) i);
  assert(4 <= i /\ i < 8 ==> index (le_quad32_to_bytes_def q) i == four_select (nat_to_four 8 q1) (i % 4));
  assert(8 <= i /\ i < 12 ==> index (le_quad32_to_bytes_def q) i == four_select (nat_to_four 8 q2) (i % 4));
  assert(12 <= i /\ i < 16 ==> index (le_quad32_to_bytes_def q) i == four_select (nat_to_four 8 q3) (i % 4))


#reset-options "--smtencoding.elim_box true --z3rlimit 10 --z3refresh --max_ifuel 1 --initial_fuel 0 --max_fuel 2"
let pad_to_128_bits_lower (q:quad32) (num_bytes:int) =
  let Mkfour x0 x1 x2 x3 = q in
  assert (num_bytes * 8 < 64);
  pow2_lt_compat 64 (num_bytes * 8);
  modulo_range_lemma (lo64 q) (pow2 (num_bytes * 8));
  let new_lo = (lo64 q) % pow2 (num_bytes * 8) in
  assert_norm (pow2 64 == pow2_64); // refinement on Words_s.pow2_64?
  assert (new_lo < pow2_64);
  let q' = insert_nat64 (insert_nat64 q 0 1) new_lo 0 in
  assert_by_tactic (insert_nat64 (Mkfour x0 x1 x2 x3) 0 1 == Mkfour x0 x1 0 0)
    (fun () -> norm[delta;primops];  trefl ());
  let new_lo_two = Words.Two_s.nat_to_two 32 new_lo in

  let helper new_lo_o :
    Lemma (let Mktwo new_lo_lo new_lo_hi = Words.Two_s.nat_to_two 32 new_lo_o in
	  insert_nat64 (insert_nat64 q 0 1) new_lo_o 0 == Mkfour new_lo_lo new_lo_hi 0 0) =
    assert_by_tactic (
      let Mktwo new_lo_lo new_lo_hi = Words.Two_s.nat_to_two 32 new_lo_o in
      insert_nat64 (Mkfour x0 x1 0 0) new_lo_o 0 == Mkfour new_lo_lo new_lo_hi 0 0)
        (fun () -> norm[delta; primops]; trefl ())
  in
    helper new_lo;
    assert_norm (lo64 (Mkfour x0 x1 x2 x3) == Words.Two_s.two_to_nat 32 (Mktwo x0 x1));
    assert (new_lo == (Words.Two_s.two_to_nat_unfold 32 (Mktwo x0 x1)) % pow2 (num_bytes * 8));
    assert (q' == Mkfour new_lo_two.lo new_lo_two.hi 0 0); 

    // Easier to prove that le_quad32_to_bytes q' == ... and then derive the goal from injectivity.
    let q'_bytes = le_quad32_to_bytes q' in
    FStar.Classical.forall_intro (le_quad32_to_bytes_sel q');
    FStar.Classical.forall_intro (le_quad32_to_bytes_sel q);
    assert (q'_bytes == le_quad32_to_bytes (Mkfour new_lo_two.lo new_lo_two.hi 0 0));
    assert (forall i. i <= 8 /\ i < 16 ==> index q'_bytes i == 0);
    assert (forall i. i <= 8 /\ i < 16 ==> index (slice (le_quad32_to_bytes q) 0 num_bytes) i == 0);
    assert (forall i. i < 4 ==> index q'_bytes i == four_select (nat_to_four 8 new_lo_two.lo) i);
    assert (forall i. i < 4 ==> index (slice (le_quad32_to_bytes q) 0 num_bytes) i == 
			   four_select (nat_to_four 8 x0) i);
    assert (forall i. i < 4 ==> four_select (nat_to_four 8 x0) i == four_select (nat_to_four 8 new_lo_two.hi) i);
    assert (forall i. i <= 4 /\ i < 8 ==> index q'_bytes i == four_select (nat_to_four 8 x1) (i % 4));
    assert (forall i. i <= 4 /\ i < 8 ==> index (slice (le_quad32_to_bytes q) 0 num_bytes) i == 
				       four_select (nat_to_four 8 new_lo_two.hi) (i % 4));
    assert (forall i. i <= 4 /\ i < 8 ==> four_select (nat_to_four 8 x1) i == four_select (nat_to_four 8 new_lo_two.hi) i)
    
            
let pad_to_128_bits_upper (q:quad32) (num_bytes:int) =
  let Mkfour x0 x1 x2 x3 = q in
  let new_hi = (hi64 q) % pow2 ((num_bytes - 8) * 8) in
  assert_norm (pow2 64 == pow2_64); // refinement on Words_s.pow2_64?
  assert (new_hi < pow2_64);
  let q' = insert_nat64 q new_hi 1 in
  let new_hi_two = Words.Two_s.nat_to_two 32 new_hi in
  assert_by_tactic (insert_nat64 (Mkfour x0 x1 x2 x3) new_hi 1 == Mkfour x0 x1 new_hi_two.lo new_hi_two.hi)
    (fun () -> norm[delta]; trefl ());

  assert_norm (hi64 (Mkfour x0 x1 x2 x3) == Words.Two_s.two_to_nat 32 (Mktwo x2 x3));
  assert (new_hi == (Words.Two_s.two_to_nat_unfold 32 (Mktwo x2 x3)) % pow2 ((num_bytes - 8) * 8));
  assert (q' == Mkfour x0 x1 new_hi_two.lo new_hi_two.hi); 

  // Easier to prove that le_quad32_to_bytes q' == ... and then derive the goal from injectivity.
  let q'_bytes = le_quad32_to_bytes q' in
  FStar.Classical.forall_intro (le_quad32_to_bytes_sel q');
  FStar.Classical.forall_intro (le_quad32_to_bytes_sel q);
  assert (q'_bytes == le_quad32_to_bytes (Mkfour x0 x1 new_hi_two.lo new_hi_two.hi));
  assert (forall i. i <= 8 /\ i < 12 ==> index q'_bytes i == four_select (nat_to_four 8 new_hi_two.lo) (i % 4));
  assert (forall i. i <= 8 /\ i < 12 ==> index (slice (le_quad32_to_bytes q) 0 num_bytes) i == 
					     four_select (nat_to_four 8 new_hi_two.lo) (i % 4));
  assert (forall i. i <= 12 /\ i < 16 ==> index q'_bytes i == four_select (nat_to_four 8 new_hi_two.hi) (i % 4));
  assert (forall i. i <= 12 /\ i < 16 ==> index (slice (le_quad32_to_bytes q) 0 num_bytes) i == 
					     four_select (nat_to_four 8 new_hi_two.hi) (i % 4));
  assert (forall i. i < 4 ==> index q'_bytes i == four_select (nat_to_four 8 x0) (i % 4));
  assert (forall i. i < 4 ==> index (slice (le_quad32_to_bytes q) 0 num_bytes) i == 
					     four_select (nat_to_four 8 x0) (i % 4));
  assert (forall i. i <= 4 /\ i < 8 ==> index q'_bytes i == four_select (nat_to_four 8 x1) (i % 4));
  assert (forall i. i <= 4 /\ i < 8 ==> index (slice (le_quad32_to_bytes q) 0 num_bytes) i == 
				     four_select (nat_to_four 8 x1) (i % 4))
