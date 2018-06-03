module AES256_helpers_i

open Words_s
open Types_s
open FStar.Seq
open AES_s

// syntax for seq accesses, s.[index] and s.[index] <- value
unfold
let op_String_Access (#a:Type) (s:seq a) (i:nat{ i < length s}) : Tot a = index s i

unfold
let op_String_Assignment = Seq.upd

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Mkfour v0 v1 v2 v3 = q in
  Mkfour 0 v0 v1 v2


// Redefine key expansion in terms of quad32 values rather than nat32 values,
// then prove both definitions are equivalent.

let round_key_256_rcon (prev0 prev1:quad32) (rcon:nat32) (round:int) : quad32 =
  let Mkfour v0 v1 v2 v3 = prev0 in
  let Mkfour v4 v5 v6 v7 = prev1 in  
  let c1 = if round % 2 = 0 then sub_word (rot_word_LE v7) *^ rcon else sub_word v7 in
  let w0 = v0 *^ c1 in
  let w1 = v1 *^ w0 in
  let w2 = v2 *^ w1 in
  let w3 = v3 *^ w2 in
  Mkfour w0 w1 w2 w3
 
let round_key_256 (prev0 prev1:quad32) (round:nat) : quad32 =
  round_key_256_rcon prev0 prev1 (aes_rcon (round / 2 - 1)) round

let rec expand_key_256 (key:aes_key_LE AES_256) (round:nat) : quad32 =
  if round = 0 then Mkfour key.[0] key.[1] key.[2] key.[3]
  else if round = 1 then Mkfour key.[4] key.[5] key.[6] key.[7]
  else round_key_256 (expand_key_256 key (round - 2)) (expand_key_256 key (round - 1)) round

#reset-options "--initial_fuel 8 --max_fuel 8 --max_ifuel 0"
let lemma_expand_key_256_0 (key:aes_key_LE AES_256) : Lemma
  (equal key (expand_key AES_256 key 8))
  = ()

open FStar.Mul
#reset-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0 --z3rlimit 30"
let lemma_expand_key_256_i (key:aes_key_LE AES_256) (i:nat) : Lemma
  (requires
    1 < i /\ i < 15
  )
  (ensures (
    let m = 4 * (i - 2) in
    let n = 4 * i in
    let v = expand_key AES_256 key n in          // Current
    let w = expand_key AES_256 key (n + 4) in    // Next 4 words
    let prev0 = Mkfour v.[m + 0] v.[m + 1] v.[m + 2] v.[m + 3] in  // Penultimate 4 words in Current
    let prev1 = Mkfour v.[m + 4] v.[m + 5] v.[m + 6] v.[m + 7] in  // Ultimate 4 words in Current
    let Mkfour r0 r1 r2 r3 = round_key_256 prev0 prev1 i in        // Calc NextQuad from quads at end of Current
    r0 == w.[n + 0] /\ r1 == w.[n + 1] /\ r2 == w.[n + 2] /\ r3 == w.[n + 3]  // NextQuad == Next 4 words
  ))
  =
  let n = 4 * i in
  // unfold expand_key 8 times (could use fuel, but that unfolds everything):
  let _ = expand_key AES_256 key (n + 1) in
  let _ = expand_key AES_256 key (n + 2) in
  let _ = expand_key AES_256 key (n + 3) in
  let _ = expand_key AES_256 key (n + 4) in
  if i < 14 then (
    let _ = expand_key AES_256 key (n + 5) in
    let _ = expand_key AES_256 key (n + 6) in
    let _ = expand_key AES_256 key (n + 7) in
    ()
  ) else ();
  ()
#reset-options

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
let rec lemma_expand_append (key:aes_key_LE AES_256) (size1:nat) (size2:nat) : Lemma
  (requires size1 <= size2 /\ size2 <= 60)
  (ensures equal (expand_key AES_256 key size1) (slice (expand_key AES_256 key size2) 0 size1))
  (decreases size2)
  =
  if size1 < size2 then lemma_expand_append key size1 (size2 - 1)

//#reset-options "--initial_fuel 8 --max_fuel 8 --max_ifuel 0"
let lemma_expand_key_256_0_corollary (key:aes_key_LE AES_256) : Lemma
  ((let s = key_schedule_to_round_keys 1 (expand_key AES_256 key 60) in
    expand_key_256 key 0 == s.[0]) /\
   (let s = key_schedule_to_round_keys 2 (expand_key AES_256 key 60) in
    expand_key_256 key 1 == s.[1]))
  =
  lemma_expand_key_256_0 key;
  //let s = key_schedule_to_round_keys 1 (expand_key AES_256 key 60) in
  //let s' = expand_key_256 key 0 in
  //assert (s' == Mkfour key.[0] key.[1] key.[2] key.[3]);
  //let e = expand_key AES_256 key 60 in
  //assert (s == append createEmpty (create 1 (Mkfour e.[0] e.[1] e.[2] e.[3])));
  //append_empty_l (create 1 (Mkfour e.[0] e.[1] e.[2] e.[3]));
  //assert (s == create 1 (Mkfour e.[0] e.[1] e.[2] e.[3]));
  lemma_expand_append key 8 60;
  //append_empty_l (create 1 (index key 0));
  //  assert (s' == s.[0]);
  ()


#reset-options "--z3rlimit 30 --initial_fuel 4 --max_fuel 4 --max_ifuel 0"
// quad32 key expansion is equivalent to nat32 key expansion
let rec lemma_expand_key_256 (key:aes_key_LE AES_256) (size:nat) : Lemma
  (requires size <= 15)
  (ensures (
    let s = key_schedule_to_round_keys size (expand_key AES_256 key 60) in
    (forall (i:nat).{:pattern (expand_key_256 key i)} i < size ==> expand_key_256 key i == s.[i])
  ))
  =
  lemma_expand_append key (4 * size) 60;
  // assert (equal (expand_key AES_256 key (4 * size)) (slice (expand_key AES_256 key 60) 0 (4 * size)));
  if size = 0 then ()
  else
  (
    let i = size - 1 in
    lemma_expand_append key (4 * i) 60;
    lemma_expand_key_256 key i;  // Prove the quantifier above for i < size - 1
    // Prove for i == size - 1
    (if i = 0 || i = 1 then (lemma_expand_key_256_0_corollary key)
     else (
       lemma_expand_key_256_i key i; // ==> 
       // round_key_256 prev0 prev1 i ~= (expand_key AES_256 key (4*i + 4)).[4*i, 4*i + 1, ... 4*i + 3]
       //                             ~= (expand_key AES_256 key (4*i + 4)).[4*size - 4 ... 4*size - 1]
       //                             ~= (expand_key AES_256 key  (4*size)).[4*size - 4 ... 4*size - 1]

       let prev0 = expand_key_256 key (i - 2) in
       let prev1 = expand_key_256 key (i - 1) in
       assert (expand_key_256 key i == round_key_256 prev0 prev1 i);

       let m = 4 * (i - 2) in
       let n = 4 * i in
       let v' = expand_key AES_256 key n in          // Current
       let w' = expand_key AES_256 key (n + 4) in    // Next 4 words
       let prev0' = Mkfour v'.[m + 0] v'.[m + 1] v'.[m + 2] v'.[m + 3] in  // Penultimate 4 words in Current
       let prev1' = Mkfour v'.[m + 4] v'.[m + 5] v'.[m + 6] v'.[m + 7] in  // Ultimate 4 words in Current
       assert (Mkfour w'.[n] w'.[n + 1] w'.[n + 2] w'.[n + 3] == round_key_256 prev0' prev1' i);
       // ==> (expand_key AES_256 key (4 * i + 4)).[4*i ... 4*i + 3] == round_key_256 prev0' prev1' i
       // ==> (expand_key AES_256 key (4 * size)).[4*size - 4 ... 4*size - 1] == round_key_256 prev0' prev1' i


       // prev0' == (expand_key AES_256 key 4*i).[4 * (i-2) ... 4 * (i - 2) + 3]
       // prev0  == expand_key_256 key (i - 2)
       //                { induction hypothesis }
       //        == s.[i-2]

       //lemma_expand_append key (4 * (i-2)) 60;
       //assert (prev0 == prev0');  // Fails here.  Succeeds below
       assert (prev1 == prev1');   // OBSERVE
       
       // Definition of expand_key_256:
       // expand_key_256 key i ==
       //    round_key_256 (expand_key_256 key (i - 2)) (expand_key_256 key (i - 1)) i
       
       let s = key_schedule_to_round_keys size (expand_key AES_256 key 60) in
       // s = let round_keys = key_schedule_to_round_keys (size - 1) w in
       //     let rk = Mkfour w.[4 * size - 4] w.[4 * size - 3] w.[4 * size - 2] w.[4 * size - 1] in
       //     append round_keys (create 1 rk)
       // s.[i] == s.[size - 1] 
       //       ~=  Mkfour w.[4 * size - 4] w.[4 * size - 3] w.[4 * size - 2] w.[4 * size - 1]
       
       // Following is from: lemma_expand_append key (4 * i) 60;
       //assert (equal (expand_key AES_256 key (4 * i)) (slice (expand_key AES_256 key 60) 0 (4 * i)));

       let w = expand_key AES_256 key 60 in
       assert (w.[4 * size - 4] == (expand_key AES_256 key (4*size)).[4 * size - 4]);
       assert (w.[4 * size - 3] == (expand_key AES_256 key (4*size)).[4 * size - 3]);
       assert (w.[4 * size - 2] == (expand_key AES_256 key (4*size)).[4 * size - 2]);
       assert (w.[4 * size - 1] == (expand_key AES_256 key (4*size)).[4 * size - 1]);
       assert (s.[i] == Mkfour w.[4 * size - 4] w.[4 * size - 3] w.[4 * size - 2] w.[4 * size - 1]);

       assert (s.[i-2] == Mkfour w.[4 * (i - 1) - 4] w.[4 * (i - 1) - 3] w.[4 * (i - 1) - 2] w.[4 * (i - 1) - 1]);  // Needs extra fuel above
       assert (prev0 == prev0');
       ()
     )
    )     
  )
#reset-options

// Refine round_key_256 to a SIMD computation
let simd_round_key_256 (prev0 prev1:quad32) (rcon:nat32) (round:int) : quad32 =
  let r = if round % 2 = 0 then rot_word_LE (sub_word prev1.hi3) *^ rcon else sub_word prev1.hi3 in
  let q = prev0 in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  q *^^ Mkfour r r r r

// SIMD version of round_key_256 is equivalent to scalar round_key_256
let lemma_simd_round_key (prev0 prev1:quad32) (rcon:nat32) (round:int) : Lemma
  (simd_round_key_256 prev0 prev1 rcon round == round_key_256_rcon prev0 prev1 rcon round)
  =
  commute_rot_word_sub_word prev1.hi3;
  Types_i.xor_lemmas ()

let lemma_round_key_256_rcon_odd (prev0 prev1:quad32) (rcon:nat32) (round:int) : Lemma
  (requires ~(round % 2 == 0))
  (ensures round_key_256_rcon prev0 prev1 rcon round == round_key_256_rcon prev0 prev1 0 round)
  =
  ()
