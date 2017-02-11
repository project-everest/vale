include "../util/types.s.dfy"

module bitvectors64_s
{
import opened types_s

function{:opaque} U64(b:bv64 ):uint64 { b as uint64  }
function{:opaque} B64(i:uint64):bv64 { i as bv64 }
function{:opaque} bv64add(x:bv64, y:bv64):bv64 { x + y }
function{:opaque} bv64sub(x:bv64, y:bv64):bv64 { x - y }
function{:opaque} bv64mul(x:bv64, y:bv64):bv64 { x * y }
function{:opaque} bv64div(x:bv64, y:bv64):bv64 requires y != 0 { x / y }
function{:opaque} bv64mod(x:bv64, y:bv64):bv64 requires y != 0 { x % y }
function{:opaque} bv64and(x:bv64, y:bv64):bv64 { x & y }
function{:opaque} bv64or (x:bv64, y:bv64):bv64 { x | y }
function{:opaque} bv64xor(x:bv64, y:bv64):bv64 { x ^ y }
function{:opaque} bv64shl(x:bv64, y:bv64):bv64 requires y < 64 { x << y }
function{:opaque} bv64shr(x:bv64, y:bv64):bv64 requires y < 64 { x >> y }
function{:opaque} bv64rol(x:bv64, y:bv64):bv64 requires y < 64 { reveal_U64(); x.RotateLeft(U64(y)) }
function{:opaque} bv64ror(x:bv64, y:bv64):bv64 requires y < 64 { reveal_U64(); x.RotateRight(U64(y)) }
function{:opaque} bv64not(x:bv64):bv64 { !x }

function{:opaque} mod2_64(x:int):uint64 { x % 0x1_0000_0000_0000_0000 }

lemma{:axiom} lemma_B64(x:bv64) ensures B64(U64(x)) == x;
lemma{:axiom} lemma_U64(x:uint64) ensures U64(B64(x)) == x;
lemma{:axiom} lemma_bv64add(x:uint64, y:uint64) ensures mod2_64(x + y) == U64(bv64add(B64(x), B64(y)))
lemma{:axiom} lemma_bv64sub(x:uint64, y:uint64) ensures mod2_64(x - y) == U64(bv64sub(B64(x), B64(y)))
lemma{:axiom} lemma_bv64mul(x:uint64, y:uint64) ensures mod2_64(x * y) == U64(bv64mul(B64(x), B64(y)))
lemma{:axiom} lemma_bv64div(x:uint64, y:uint64) requires y != 0 ensures B64(y) != 0 ensures x / y == U64(bv64div(B64(x), B64(y)))
lemma{:axiom} lemma_bv64mod(x:uint64, y:uint64) requires y != 0 ensures B64(y) != 0 ensures x % y == U64(bv64mod(B64(x), B64(y)))

// x <= y, x > y --> use lemma_bv_le64(x, y)
// x >= y, x < y --> use lemma_bv_le64(y, x)
lemma{:axiom} lemma_bv64le (x:uint64, y:uint64) ensures x <= y <==> B64(x) <= B64(y)

} // end module
