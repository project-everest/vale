module Types_s

open Collections.Seqs_s

unfold let nat8_max = 0x100
unfold let nat16_max = 0x10000
unfold let nat32_max = 0x100000000
unfold let nat64_max = 0x10000000000000000
unfold let nat128_max = 0x100000000000000000000000000000000

// Sanity check our constants
let _ = assert_norm (pow2 8 = nat8_max)
let _ = assert_norm (pow2 16 = nat16_max)
let _ = assert_norm (pow2 32 = nat32_max)
let _ = assert_norm (pow2 64 = nat64_max)
let _ = assert_norm (pow2 128 = nat128_max)

let natN (n:nat) = x:nat{x < n}
let nat8 = natN nat8_max
let nat16 = natN nat16_max
let nat32 = natN nat32_max
let nat64 = natN nat64_max
let nat128 = natN nat128_max

let add_wrap (#n:nat) (x:natN n) (y:natN n) : natN n = if x + y < n then x + y else x + y - n

// abstract bitwise operations on integers:
assume val iand : #n:nat -> a:natN n -> b:natN n -> natN n
assume val ixor : #n:nat -> a:natN n -> b:natN n -> natN n
assume val ior : #n:nat -> a:natN n -> b:natN n -> natN n
assume val inot : #n:nat -> a:natN n  -> natN n
assume val ishl : #n:nat -> a:natN n -> s:int -> natN n
assume val ishr : #n:nat -> a:natN n -> s:int -> natN n

// Alias
unfold let nat32_xor (x y:nat32) : nat32 = ixor x y

type twobits = i:int{0 <= i && i < 4}
type bits_of_byte = | Bits_of_Byte :
  lo:twobits ->
  mid_lo:twobits ->  
  mid_hi:twobits ->
  hi:twobits ->
  bits_of_byte

let byte_to_twobits (b:nat8) =
  Bits_of_Byte
    (b % 4)
    ((b / 4) % 4)
    ((b / 16) % 4)
    ((b / 64) % 4)

type double32 = | Double32: lo:nat32 -> hi:nat32 -> double32

type quad32 = | Quad32:
  lo:nat32 ->
  mid_lo:nat32 ->
  mid_hi:nat32 ->
  hi:nat32 ->
  quad32

unfold
let quad32_map (f:nat32 -> nat32) (x:quad32) : quad32 =
  let Quad32 x0 x1 x2 x3 = x in
  Quad32 (f x0) (f x1) (f x2) (f x3)

unfold
let quad32_map2 (f:nat32 -> nat32 -> nat32) (x y:quad32) : quad32 =
  let Quad32 x0 x1 x2 x3 = x in
  let Quad32 y0 y1 y2 y3 = y in
  Quad32 (f x0 y0) (f x1 y1) (f x2 y2) (f x3 y3)

let quad32_xor (x y:quad32) : quad32 = quad32_map2 nat32_xor x y

let select_word (q:quad32) (selector:twobits) =
  match selector with
  | 0 -> q.lo
  | 1 -> q.mid_lo
  | 2 -> q.mid_hi
  | 3 -> q.hi

let insert_nat32 (q:quad32) (n:nat32) (i:twobits) =
  match i with 
  | 0 -> Quad32 n q.mid_lo q.mid_hi q.hi
  | 1 -> Quad32 q.lo n q.mid_hi q.hi
  | 2 -> Quad32 q.lo q.mid_lo n q.hi
  | 3 -> Quad32 q.lo q.mid_lo q.mid_hi n

open FStar.Seq

assume val be_bytes_to_nat32 (b:seq nat8 {length b == 4}) : Tot nat32
assume val nat32_to_be_bytes (n:nat32) : Tot (b:seq nat8 { length b = 4 /\ be_bytes_to_nat32 b == n }) 

assume val be_bytes_to_nat32_to_be_bytes (b:seq nat8 {length b == 4}) : 
  Lemma (nat32_to_be_bytes (be_bytes_to_nat32 b) == b)

let reverse_bytes_nat32 (n:nat32) : Tot (nat32) =
  be_bytes_to_nat32 (reverse_seq (nat32_to_be_bytes n))

let reverse_bytes_quad32 (q:quad32) : quad32 =
  Quad32 (reverse_bytes_nat32 q.hi)
	 (reverse_bytes_nat32 q.mid_hi)
	 (reverse_bytes_nat32 q.mid_lo)
	 (reverse_bytes_nat32 q.lo)
