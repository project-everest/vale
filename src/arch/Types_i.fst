module Types_i

open Types_s
open TypesNative_i
open Collections.Seqs_i
open Words_s

let lemma_BitwiseXorCommutative x y =
  lemma_ixor_nth_all 32;
  lemma_equal_nth 32 (x *^ y) (y *^ x)

let lemma_BitwiseXorWithZero n =
  lemma_ixor_nth_all 32;
  lemma_zero_nth 32;
  lemma_equal_nth 32 (n *^ 0) n

let lemma_BitwiseXorCancel n =
  lemma_ixor_nth_all 32;
  lemma_zero_nth 32;
  lemma_equal_nth 32 (n *^ n) 0

let lemma_BitwiseXorCancel64 (n:nat64) =
  lemma_ixor_nth_all 64;
  lemma_zero_nth 64;
  lemma_equal_nth 64 (ixor n n) 0 

let lemma_BitwiseXorAssociative x y z =
  lemma_ixor_nth_all 32;
  lemma_equal_nth 32 (x *^ (y *^ z)) ((x *^ y) *^ z)

let xor_lemmas () =
  FStar.Classical.forall_intro_2 lemma_BitwiseXorCommutative;
  FStar.Classical.forall_intro lemma_BitwiseXorWithZero;
  FStar.Classical.forall_intro lemma_BitwiseXorCancel;
  FStar.Classical.forall_intro lemma_BitwiseXorCancel64;
  FStar.Classical.forall_intro_3 lemma_BitwiseXorAssociative;
  ()

let lemma_quad32_xor () =
  xor_lemmas()

let lemma_reverse_reverse_bytes_nat32 (n:nat32) :
  Lemma (reverse_bytes_nat32 (reverse_bytes_nat32 n) == n)
  =
  let r = reverse_seq (nat32_to_be_bytes n) in
  be_bytes_to_nat32_to_be_bytes r;
  ()

let lemma_reverse_bytes_quad32 (q:quad32) =
  reveal_reverse_bytes_quad32 q;
  reveal_reverse_bytes_quad32 (reverse_bytes_quad32 q);
  ()

let lemma_reverse_reverse_bytes_nat32_seq (s:seq nat32) :
  Lemma (ensures reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s) == s)
  =
  reveal_reverse_bytes_nat32_seq s;
  reveal_reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s);
  assert (equal (reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s)) s)

open Words.Two_s

let nat_to_two_to_nat (n1 n2:nat32) : Lemma
  (nat_to_two 32 (two_to_nat 32 (Mktwo n1 n2)) == Mktwo n1 n2)
  =
  assert (two_to_nat 32 (Mktwo n1 n2) == int_to_natN pow2_64 (n1 + n2 * pow2_32));
  admit()

let push_pop_xmm (x y:quad32) : Lemma 
  (let x_two = four_to_two_two x in
   let x_hi = two_to_nat 32 (two_select x_two 1) in
   let x_lo = two_to_nat 32 (two_select x_two 0) in
   let x' = insert_nat64 (insert_nat64 y x_hi true) x_lo false in
   x == x')
   =
   let x_hi = x.hi2 + pow2_32 `op_Multiply` x.hi3 in
   let Mktwo lo hi = nat_to_two 32 x_hi in
   assert (lo == x_hi % pow2_32);
   //()
   assert (hi == (x_hi / pow2_32) % pow2_32);
   assert (lo == x.hi2);
   ()
