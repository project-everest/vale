include "../util/types.s.dfy"

module bitvectors32_s
{
import opened types_s

function{:opaque} U32(b:bv32 ):uint32 { b as uint32  }
function{:opaque} B32(i:uint32):bv32 { i as bv32 }
function{:opaque} bv32add(x:bv32, y:bv32):bv32 { x + y }
function{:opaque} bv32sub(x:bv32, y:bv32):bv32 { x - y }
function{:opaque} bv32mul(x:bv32, y:bv32):bv32 { x * y }
function{:opaque} bv32div(x:bv32, y:bv32):bv32 requires y != 0 { x / y }
function{:opaque} bv32mod(x:bv32, y:bv32):bv32 requires y != 0 { x % y }
function{:opaque} bv32and(x:bv32, y:bv32):bv32 { x & y }
function{:opaque} bv32or (x:bv32, y:bv32):bv32 { x | y }
function{:opaque} bv32xor(x:bv32, y:bv32):bv32 { x ^ y }
function{:opaque} bv32shl(x:bv32, y:bv32):bv32 requires y < 32 { x << y }
function{:opaque} bv32shr(x:bv32, y:bv32):bv32 requires y < 32 { x >> y }
function{:opaque} bv32rol(x:bv32, y:bv32):bv32 requires y < 32 { reveal_U32(); x.RotateLeft(U32(y)) }
function{:opaque} bv32ror(x:bv32, y:bv32):bv32 requires y < 32 { reveal_U32(); x.RotateRight(U32(y)) }
function{:opaque} bv32not(x:bv32):bv32 { !x }

function{:opaque} mod2_32(x:int):uint32 { x % 0x1_0000_0000 }

lemma{:axiom} lemma_B32(x:bv32) ensures B32(U32(x)) == x;
lemma{:axiom} lemma_U32(x:uint32) ensures U32(B32(x)) == x;
lemma{:axiom} lemma_bv32add(x:uint32, y:uint32) ensures mod2_32(x + y) == U32(bv32add(B32(x), B32(y)))
lemma{:axiom} lemma_bv32sub(x:uint32, y:uint32) ensures mod2_32(x - y) == U32(bv32sub(B32(x), B32(y)))
lemma{:axiom} lemma_bv32mul(x:uint32, y:uint32) ensures mod2_32(x * y) == U32(bv32mul(B32(x), B32(y)))
lemma{:axiom} lemma_bv32div(x:uint32, y:uint32) requires y != 0 ensures B32(y) != 0 ensures x / y == U32(bv32div(B32(x), B32(y)))
lemma{:axiom} lemma_bv32mod(x:uint32, y:uint32) requires y != 0 ensures B32(y) != 0 ensures x % y == U32(bv32mod(B32(x), B32(y)))

// x <= y, x > y --> use lemma_bv_le32(x, y)
// x >= y, x < y --> use lemma_bv_le32(y, x)
lemma{:axiom} lemma_bv32le (x:uint32, y:uint32) ensures x <= y <==> B32(x) <= B32(y)

} // end module
