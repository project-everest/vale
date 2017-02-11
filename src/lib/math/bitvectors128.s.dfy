include "../util/types.s.dfy"

module bitvectors128_s
{
import opened types_s

function{:opaque} U128(b:bv128 ):uint128 { b as uint128  }
function{:opaque} B128(i:uint128):bv128 { i as bv128 }
function{:opaque} bv128add(x:bv128, y:bv128):bv128 { x + y }
function{:opaque} bv128sub(x:bv128, y:bv128):bv128 { x - y }
function{:opaque} bv128mul(x:bv128, y:bv128):bv128 { x * y }
function{:opaque} bv128div(x:bv128, y:bv128):bv128 requires y != 0 { x / y }
function{:opaque} bv128mod(x:bv128, y:bv128):bv128 requires y != 0 { x % y }
function{:opaque} bv128and(x:bv128, y:bv128):bv128 { x & y }
function{:opaque} bv128or (x:bv128, y:bv128):bv128 { x | y }
function{:opaque} bv128xor(x:bv128, y:bv128):bv128 { x ^ y }
function{:opaque} bv128shl(x:bv128, y:bv128):bv128 requires y < 128 { x << y }
function{:opaque} bv128shr(x:bv128, y:bv128):bv128 requires y < 128 { x >> y }
function{:opaque} bv128rol(x:bv128, y:bv128):bv128 requires y < 128 { reveal_U128(); x.RotateLeft(U128(y)) }
function{:opaque} bv128ror(x:bv128, y:bv128):bv128 requires y < 128 { reveal_U128(); x.RotateRight(U128(y)) }
function{:opaque} bv128not(x:bv128):bv128 { !x }

function{:opaque} mod2_128(x:int):uint128 { x % 0x1_00000000_00000000_00000000_00000000 }

lemma{:axiom} lemma_B128(x:bv128) ensures B128(U128(x)) == x;
lemma{:axiom} lemma_U128(x:uint128) ensures U128(B128(x)) == x;
lemma{:axiom} lemma_bv128add(x:uint128, y:uint128) ensures mod2_128(x + y) == U128(bv128add(B128(x), B128(y)))
lemma{:axiom} lemma_bv128sub(x:uint128, y:uint128) ensures mod2_128(x - y) == U128(bv128sub(B128(x), B128(y)))
lemma{:axiom} lemma_bv128mul(x:uint128, y:uint128) ensures mod2_128(x * y) == U128(bv128mul(B128(x), B128(y)))
lemma{:axiom} lemma_bv128div(x:uint128, y:uint128) requires y != 0 ensures B128(y) != 0 ensures x / y == U128(bv128div(B128(x), B128(y)))
lemma{:axiom} lemma_bv128mod(x:uint128, y:uint128) requires y != 0 ensures B128(y) != 0 ensures x % y == U128(bv128mod(B128(x), B128(y)))

// x <= y, x > y --> use lemma_bv_le128(x, y)
// x >= y, x < y --> use lemma_bv_le128(y, x)
lemma{:axiom} lemma_bv128le (x:uint128, y:uint128) ensures x <= y <==> B128(x) <= B128(y)

} // end module
