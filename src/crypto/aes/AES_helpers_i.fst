module AES_helpers_i

open Types_s
open FStar.Seq
open AES_s
open FStar.Mul

// syntax for seq accesses, s.[index] and s.[index] <- value
unfold
let op_String_Access (#a:Type) (s:seq a) (i:nat{ i < length s}) : Tot a = index s i

unfold
let op_String_Assignment = Seq.upd

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Quad32 v0 v1 v2 v3 = q in
  Quad32 0 v0 v1 v2

assume val lemma_BitwiseXorCommutative (x y:nat32) : Lemma (x *^ y == y *^ x)
assume val lemma_BitwiseXorWithZero (n:nat32) : Lemma (n *^ 0 == n)
assume val lemma_BitwiseXorCancel (n:nat32) : Lemma (n *^ n == 0)
assume val lemma_BitwiseXorAssociative (x y z:nat32) : Lemma (x *^ (y *^ z) == (x *^ y) *^ z)

assume val xor_lemmas (_:unit) : Lemma
  (ensures
    (forall (x y:nat32).{:pattern (x *^ y)} x *^ y == y *^ x) /\
    (forall (n:nat32).{:pattern (n *^ 0)} n *^ 0 == n) /\
    (forall (n:nat32).{:pattern (n *^ n)} n *^ n == 0) /\
    (forall (x y z:nat32).{:pattern (x *^ (y *^ z))} x *^ (y *^ z) == (x *^ y) *^ z)
  )

assume val lemma_RotWordSubWordCommutativity (x:nat32) : Lemma
  (rot_word (sub_word x) == sub_word (rot_word x))


// Redefine key expansion in terms of quad32 values rather than nat32 values,
// then prove both definitions are equivalent.

let round_key_128_rcon (prev:quad32) (rcon:nat32) : quad32 =
  let Quad32 v0 v1 v2 v3 = prev in
  let w0 = v0 *^ (sub_word (rot_word v3) *^ rcon) in
  let w1 = v1 *^ w0 in
  let w2 = v2 *^ w1 in
  let w3 = v3 *^ w2 in
  Quad32 w0 w1 w2 w3

let round_key_128 (prev:quad32) (round:nat) : quad32 =
  round_key_128_rcon prev (aes_rcon (round - 1))

let rec expand_key_128 (key:aes_key AES_128) (round:nat) : quad32 =
  if round = 0 then Quad32 key.[0] key.[1] key.[2] key.[3]
  else round_key_128 (expand_key_128 key (round - 1)) round

#reset-options "--initial_fuel 4 --max_fuel 4 --max_ifuel 0 --z3rlimit 40"
let lemma_expand_key_128_0 (key:aes_key AES_128) : Lemma
  (equal key (expand_key AES_128 key 4))
  = ()

let lemma_expand_key_128_i (key:aes_key AES_128) (i:nat) : Lemma
  (requires
    0 < i /\ i < 11
  )
  (ensures (
    let m = 4 * (i - 1) in
    let n = 4 * i in
    let v = expand_key AES_128 key n in
    let w = expand_key AES_128 key (n + 4) in
    let prev = Quad32 v.[m + 0] v.[m + 1] v.[m + 2] v.[m + 3] in
    let Quad32 r0 r1 r2 r3 = round_key_128 prev i in
    r0 == w.[n + 0] /\ r1 == w.[n + 1] /\ r2 == w.[n + 2] /\ r3 == w.[n + 3]
  ))
  = ()
#reset-options

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
let rec lemma_expand_append (key:aes_key AES_128) (size1:nat) (size2:nat) : Lemma
  (requires size1 <= size2 /\ size2 <= 44)
  (ensures equal (expand_key AES_128 key size1) (slice (expand_key AES_128 key size2) 0 size1))
  (decreases size2)
  =
  if size1 < size2 then lemma_expand_append key size1 (size2 - 1)

// quad32 key expansion is equivalent to nat32 key expansion
let rec lemma_expand_key_128 (key:aes_key AES_128) (size:nat) : Lemma
  (requires size <= 11)
  (ensures (
    let s = key_schedule_to_round_keys size (expand_key AES_128 key 44) in
    (forall (i:nat).{:pattern (expand_key_128 key i)} i < size ==> expand_key_128 key i == s.[i])
  ))
  =
  lemma_expand_append key (4 * size) 44;
  if size = 0 then ()
  else
  (
    let i = size - 1 in
    lemma_expand_append key (4 * i) 44;
    lemma_expand_key_128 key i;
    if i = 0 then lemma_expand_key_128_0 key
    else lemma_expand_key_128_i key i
  )

// Refine round_key_128 to a SIMD computation
let simd_round_key_128 (prev:quad32) (rcon:nat32) : quad32 =
  let r = rot_word (sub_word prev.hi) *^ rcon in
  let q = prev in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  q *^^ Quad32 r r r r

// SIMD version of round_key_128 is equivalent to scalar round_key_128
let lemma_simd_round_key (prev:quad32) (rcon:nat32) : Lemma
  (simd_round_key_128 prev rcon == round_key_128_rcon prev rcon)
  =
  lemma_RotWordSubWordCommutativity prev.hi;
  xor_lemmas ()