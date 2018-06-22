module GCM_helpers_i

open Words_s
open Words.Seq_s
open Types_s
open Types_i
open FStar.Mul
open FStar.Seq
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
let pad_to_128_bits_lower (q:quad32) (num_bytes:int) =
  admit();       ///////////////////////////////  TODO!!!  //////////////////////////////////////////////////////////////
  ()
            
let pad_to_128_bits_upper (q:quad32) (num_bytes:int) =
  admit();       ///////////////////////////////  TODO!!!  //////////////////////////////////////////////////////////////
  ()
                   
  
