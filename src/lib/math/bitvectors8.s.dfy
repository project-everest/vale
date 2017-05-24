include "../util/types.s.dfy"

module bitvectors8_s
{
import opened types_s

function{:opaque} U8(b:bv8 ):uint8 { b as uint8  }
function{:opaque} B8(i:uint8):bv8 { i as bv8 }
function{:opaque} bv8add(x:bv8, y:bv8):bv8 { x + y }
function{:opaque} bv8sub(x:bv8, y:bv8):bv8 { x - y }
function{:opaque} bv8mul(x:bv8, y:bv8):bv8 { x * y }
function{:opaque} bv8div(x:bv8, y:bv8):bv8 requires y != 0 { x / y }
function{:opaque} bv8mod(x:bv8, y:bv8):bv8 requires y != 0 { x % y }
function{:opaque} bv8and(x:bv8, y:bv8):bv8 { x & y }
function{:opaque} bv8or (x:bv8, y:bv8):bv8 { x | y }
function{:opaque} bv8xor(x:bv8, y:bv8):bv8 { x ^ y }
function{:opaque} bv8shl(x:bv8, y:bv8):bv8 requires y < 8 { x << y }
function{:opaque} bv8shr(x:bv8, y:bv8):bv8 requires y < 8 { x >> y }
function{:opaque} bv8rol(x:bv8, y:bv8):bv8 requires y < 8 { reveal_U8(); x.RotateLeft(U8(y)) }
function{:opaque} bv8ror(x:bv8, y:bv8):bv8 requires y < 8 { reveal_U8(); x.RotateRight(U8(y)) }
function{:opaque} bv8not(x:bv8):bv8 { !x }

function{:opaque} mod2_8(x:int):uint8 { x % 0x100 }

lemma{:axiom} lemma_B8(x:bv8) ensures B8(U8(x)) == x;
lemma{:axiom} lemma_U8(x:uint8) ensures U8(B8(x)) == x;
lemma{:axiom} lemma_bv8add(x:uint8, y:uint8) ensures mod2_8(x + y) == U8(bv8add(B8(x), B8(y)))
lemma{:axiom} lemma_bv8sub(x:uint8, y:uint8) ensures mod2_8(x - y) == U8(bv8sub(B8(x), B8(y)))
lemma{:axiom} lemma_bv8mul(x:uint8, y:uint8) ensures mod2_8(x * y) == U8(bv8mul(B8(x), B8(y)))
lemma{:axiom} lemma_bv8div(x:uint8, y:uint8) requires y != 0 ensures B8(y) != 0 ensures x / y == U8(bv8div(B8(x), B8(y)))
lemma{:axiom} lemma_bv8mod(x:uint8, y:uint8) requires y != 0 ensures B8(y) != 0 ensures x % y == U8(bv8mod(B8(x), B8(y)))

// x <= y, x > y --> use lemma_bv_le8(x, y)
// x >= y, x < y --> use lemma_bv_le8(y, x)
lemma{:axiom} lemma_bv8le (x:uint8, y:uint8) ensures x <= y <==> B8(x) <= B8(y)

} // end module
