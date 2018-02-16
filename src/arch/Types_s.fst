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

assume val logand : #n:nat -> a:natN n -> b:natN n -> natN n
assume val logxor : #n:nat -> a:natN n -> b:natN n -> natN n
assume val logor : #n:nat -> a:natN n -> b:natN n -> natN n
assume val lognot : #n:nat -> a:natN n  -> natN n
assume val shift_left : #n:nat -> a:natN n -> s:int -> natN n
assume val shift_right : #n:nat -> a:natN n -> s:int -> natN n
