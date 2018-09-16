module Arch.TypesNative

let lemma_equal_nth n x y =
  UInt.to_vec_lemma_2 #n x y

let lemma_zero_nth n =
  let f (i:nat{i < n}) : Lemma (not (nth #n 0 i)) = UInt.zero_nth_lemma #n i in
  FStar.Classical.forall_intro f //(UInt.zero_nth_lemma #n)

let lemma_quad32_vec_equal a b =
  let Mkfour a0 a1 a2 a3 = a in
  let Mkfour b0 b1 b2 b3 = b in
  UInt.to_vec_lemma_2 #32 a0 b0;
  UInt.to_vec_lemma_2 #32 a1 b1;
  UInt.to_vec_lemma_2 #32 a2 b2;
  UInt.to_vec_lemma_2 #32 a3 b3;
  ()

let lemma_iand_nth_i n x y i =
  reveal_iand n x y

let lemma_ixor_nth_i n x y i =
  reveal_ixor n x y

let lemma_ior_nth_i n x y i =
  reveal_ior n x y

let lemma_inot_nth_i n x i =
  reveal_inot n x

let lemma_ishl_nth_i n x y i =
  reveal_ishl n x y

let lemma_ishr_nth_i n x y i =
  reveal_ishr n x y

let lemma_iand_nth n x y =
  FStar.Classical.forall_intro (lemma_iand_nth_i n x y)

let lemma_ixor_nth n x y =
  FStar.Classical.forall_intro (lemma_ixor_nth_i n x y)

let lemma_ior_nth n x y =
  FStar.Classical.forall_intro (lemma_ior_nth_i n x y)

let lemma_inot_nth n x =
  FStar.Classical.forall_intro (lemma_inot_nth_i n x)

let lemma_ishl_nth n x y =
  FStar.Classical.forall_intro (lemma_ishl_nth_i n x y)

let lemma_ishr_nth n x y =
  FStar.Classical.forall_intro (lemma_ishr_nth_i n x y)

let lemma_iand_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_iand_nth n)

let lemma_ixor_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_ixor_nth n)

let lemma_ior_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_ior_nth n)

let lemma_inot_nth_all n =
  FStar.Classical.forall_intro (lemma_inot_nth n)

let lemma_ishl_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_ishl_nth n)

let lemma_ishr_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_ishr_nth n)

let reveal_iand_all n =
  FStar.Classical.forall_intro_2 (reveal_iand n)

let reveal_ixor_all n =
  FStar.Classical.forall_intro_2 (reveal_ixor n)

let reveal_ior_all n =
  FStar.Classical.forall_intro_2 (reveal_ior n)

let reveal_inot_all n =
  FStar.Classical.forall_intro (reveal_inot n)

let reveal_ishl_all n =
  FStar.Classical.forall_intro_2 (reveal_ishl n)

let reveal_ishr_all n =
  FStar.Classical.forall_intro_2 (reveal_ishr n)

