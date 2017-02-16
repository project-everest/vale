include "../util/types.s.dfy"

module bitvectors16_s
{
import opened types_s

function{:opaque} U16(b:bv16 ):uint16 { b as uint16  }
function{:opaque} B16(i:uint16):bv16 { i as bv16 }
function{:opaque} bv16add(x:bv16, y:bv16):bv16 { x + y }
function{:opaque} bv16sub(x:bv16, y:bv16):bv16 { x - y }
function{:opaque} bv16mul(x:bv16, y:bv16):bv16 { x * y }
function{:opaque} bv16div(x:bv16, y:bv16):bv16 requires y != 0 { x / y }
function{:opaque} bv16mod(x:bv16, y:bv16):bv16 requires y != 0 { x % y }
function{:opaque} bv16and(x:bv16, y:bv16):bv16 { x & y }
function{:opaque} bv16or (x:bv16, y:bv16):bv16 { x | y }
function{:opaque} bv16xor(x:bv16, y:bv16):bv16 { x ^ y }
function{:opaque} bv16shl(x:bv16, y:bv16):bv16 requires y < 16 { x << y }
function{:opaque} bv16shr(x:bv16, y:bv16):bv16 requires y < 16 { x >> y }
function{:opaque} bv16rol(x:bv16, y:bv16):bv16 requires y < 16 { reveal_U16(); x.RotateLeft(U16(y)) }
function{:opaque} bv16ror(x:bv16, y:bv16):bv16 requires y < 16 { reveal_U16(); x.RotateRight(U16(y)) }
function{:opaque} bv16not(x:bv16):bv16 { !x }

function{:opaque} mod2_16(x:int):uint16 { x % 0x10000 }

lemma{:axiom} lemma_B16(x:bv16) ensures B16(U16(x)) == x;
lemma{:axiom} lemma_U16(x:uint16) ensures U16(B16(x)) == x;
lemma{:axiom} lemma_bv16add(x:uint16, y:uint16) ensures mod2_16(x + y) == U16(bv16add(B16(x), B16(y)))
lemma{:axiom} lemma_bv16sub(x:uint16, y:uint16) ensures mod2_16(x - y) == U16(bv16sub(B16(x), B16(y)))
lemma{:axiom} lemma_bv16mul(x:uint16, y:uint16) ensures mod2_16(x * y) == U16(bv16mul(B16(x), B16(y)))
lemma{:axiom} lemma_bv16div(x:uint16, y:uint16) requires y != 0 ensures B16(y) != 0 ensures x / y == U16(bv16div(B16(x), B16(y)))
lemma{:axiom} lemma_bv16mod(x:uint16, y:uint16) requires y != 0 ensures B16(y) != 0 ensures x % y == U16(bv16mod(B16(x), B16(y)))

// x <= y, x > y --> use lemma_bv_le16(x, y)
// x >= y, x < y --> use lemma_bv_le16(y, x)
lemma{:axiom} lemma_bv16le (x:uint16, y:uint16) ensures x <= y <==> B16(x) <= B16(y)

} // end module
