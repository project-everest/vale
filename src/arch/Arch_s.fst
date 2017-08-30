module Arch_s

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

type nat8 = x:nat{x < nat8_max}
type nat16 = x:nat{x < nat16_max}
type nat32 = x:nat{x < nat32_max}
type nat64 = x:nat{x < nat64_max}
type nat128 = x:nat{x < nat128_max}

