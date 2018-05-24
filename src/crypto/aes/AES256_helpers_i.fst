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

#reset-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0 --z3rlimit 10"
open FStar.Mul

let mod_helper (i n:int) : Lemma
  (requires 1 < i /\ i < 14 /\ i % 2 == 1 /\ n == 4 * i)
  (ensures  ~(n % 8 == 0))
  =
  ()

#reset-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0 --z3rlimit 30"
let lemma_expand_key_256_i (key:aes_key_LE AES_256) (i:nat) : Lemma
  (requires
    1 < i /\ i < 14
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
  let _ = expand_key AES_256 key (n + 5) in
  let _ = expand_key AES_256 key (n + 6) in
  let _ = expand_key AES_256 key (n + 7) in
  ()
#reset-options

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
let rec lemma_expand_append (key:aes_key_LE AES_256) (size1:nat) (size2:nat) : Lemma
  (requires size1 <= size2 /\ size2 <= 60)
  (ensures equal (expand_key AES_256 key size1) (slice (expand_key AES_256 key size2) 0 size1))
  (decreases size2)
  =
  if size1 < size2 then lemma_expand_append key size1 (size2 - 1)

#reset-options "--z3rlimit 10"
// quad32 key expansion is equivalent to nat32 key expansion
let rec lemma_expand_key_256 (key:aes_key_LE AES_256) (size:nat) : Lemma
  (requires size <= 15)
  (ensures (
    let s = key_schedule_to_round_keys size (expand_key AES_256 key 60) in
    (forall (i:nat).{:pattern (expand_key_256 key i)} i < size ==> expand_key_256 key i == s.[i])
  ))
  =
  lemma_expand_append key (4 * size) 60;
  if size = 0 then ()
  else
  (
    let i = size - 1 in
    lemma_expand_append key (4 * i) 60;
    lemma_expand_key_256 key i;
    if i = 0 then lemma_expand_key_256_0 key
    else lemma_expand_key_256_i key i
  )
#reset-options

// Refine round_key_256 to a SIMD computation
let simd_round_key_256 (prev:quad32) (rcon:nat32) : quad32 =
  let r = rot_word_LE (sub_word prev.hi3) *^ rcon in
  let q = prev in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  q *^^ Mkfour r r r r

// SIMD version of round_key_256 is equivalent to scalar round_key_256
let lemma_simd_round_key (prev:quad32) (rcon:nat32) : Lemma
  (simd_round_key_256 prev rcon == round_key_256_rcon prev rcon)
  =
  commute_rot_word_sub_word prev.hi3;
  Types_i.xor_lemmas ()
