module Types_s

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

type quad32 = | Quad32:
  lo:nat32 ->
  mid_lo:nat32 ->
  mid_hi:nat32 ->
  hi:nat32 ->
  quad32

let quad32_xor (x y:quad32) = Quad32
  (ixor x.lo y.lo)
  (ixor x.mid_lo y.mid_lo)
  (ixor x.mid_hi y.mid_hi)
  (ixor x.hi y.hi)   

let select_word (q:quad32) (selector:twobits) =
  match selector with
  | 0 -> q.lo
  | 1 -> q.mid_lo
  | 2 -> q.mid_hi
  | 3 -> q.hi
