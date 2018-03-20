module Types_i

open Types_s
open TypesNative_i
open Collections.Seqs_i

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

let lemma_BitwiseXorAssociative x y z =
  lemma_ixor_nth_all 32;
  lemma_equal_nth 32 (x *^ (y *^ z)) ((x *^ y) *^ z)

let xor_lemmas () =
  FStar.Classical.forall_intro_2 lemma_BitwiseXorCommutative;
  FStar.Classical.forall_intro lemma_BitwiseXorWithZero;
  FStar.Classical.forall_intro lemma_BitwiseXorCancel;
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

let rec lemma_reverse_reverse_bytes_nat32_seq (s:seq nat32) :
  Lemma (ensures reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s) == s)
  (decreases %[length s])
  =
  lemma_empty s;
  if length s = 0 then ()
  else (
    lemma_reverse_reverse_bytes_nat32 (head s); 
    //assert (reverse_bytes_nat32 (reverse_bytes_nat32 (head s)) == head s);
    lemma_reverse_reverse_bytes_nat32_seq (tail s);
    //assert (reverse_bytes_nat32_seq (reverse_bytes_nat32_seq (tail s)) == tail s);
    let r_s = reverse_bytes_nat32_seq s in
    //assert (head r_s == reverse_bytes_nat32 (head s));
    //assert (cons (head s) (tail s) == s);
    lemma_tl (reverse_bytes_nat32 (head s)) (reverse_bytes_nat32_seq (tail s));
    //assert (tail r_s == reverse_bytes_nat32_seq (tail s));
    ()
  )

#reset-options "--max_fuel 5 --initial_fuel 5"
let quad32_to_seq (q:quad32) : 
  Tot (s:seq nat32 { length s == 4 /\ 
                     (let q' = Quad32 (index s 0) (index s 1) (index s 2) (index s 3) in
                      q == q')           
                   }) =
  let l = [q.lo; q.mid_lo; q.mid_hi; q.hi] in
  let s = of_list l in
  lemma_of_list_length s l; 
  lemma_of_list s l 0;
  lemma_of_list s l 1;
  lemma_of_list s l 2;
  lemma_of_list s l 3;  
  of_list l
