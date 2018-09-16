include "types.dfy"

module ops {

import opened types

///////////////////////////
// Operations on bv32s
///////////////////////////
function method {:opaque} BitAdd(x:bv32, y:bv32): bv32
{
    x + y
}

function method {:opaque} BitSub(x:bv32, y:bv32): bv32
{
    x - y
}

function method {:opaque} BitAnd(x:bv32, y:bv32): bv32
{
    x & y
}

function method {:opaque} BitOr(x:bv32, y:bv32): bv32
{
    x | y
}

function method {:opaque} BitXor(x:bv32, y:bv32): bv32
{
    x ^ y
}

function method {:opaque} BitXor64(x:bv64, y:bv64): bv64
{
    x ^ y
}

function method {:opaque} BitMod(x:bv32, y:bv32): bv32
    requires y != 0
{
    x % y
}

function method {:opaque} BitDiv(x:bv32, y:bv32): bv32
    requires y != 0
{
    x / y
}

function method {:opaque} BitMul(x:bv32, y:bv32): bv32
{
    x * y
}

function method {:opaque} BitNot(x:bv32): bv32
{
    !x
}

function method {:opaque} BitShiftLeft(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    x << amount
}

function method {:opaque} BitShiftRight(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    x >> amount
}

function method {:opaque} BitRotateRight(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    // TODO: Replace with Dafny's builtin operator for this
    (x >> amount) | (x << (32 - amount))
}

function method {:opaque} BitRotateLeft(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    // TODO: Replace with Dafny's builtin operator for this
    (x << amount) | (x >> (32 - amount))
}

////////////////////////
// Operations on words
////////////////////////

function BitwiseAnd(x:uint32, y:uint32) : uint32
{
    BitsToWord(BitAnd(WordToBits(x), WordToBits(y)))
}

function BitwiseOr(x:uint32, y:uint32):uint32
{
    BitsToWord(BitOr(WordToBits(x), WordToBits(y)))
}

function BitwiseNot(x:uint32) : uint32
{
    BitsToWord(BitNot(WordToBits(x)))
}

function BitwiseXor(x:uint32, y:uint32) : uint32
{
    BitsToWord(BitXor(WordToBits(x), WordToBits(y)))
}

function BitwiseXor64(x:uint64, y:uint64) : uint64
{
    BitsToWord64(BitXor64(WordToBits64(x), WordToBits64(y)))
}

function RotateRight(x:uint32, amount:uint32) : uint32
    requires amount < 32;
{
    BitsToWord(BitRotateRight(WordToBits(x), amount))
}

function RotateLeft(x:uint32, amount:uint32):uint32
    requires amount < 32;
{
    BitsToWord(BitRotateLeft(WordToBits(x), amount))
}

function RightShift(x:uint32, amount:uint32) : uint32
    requires amount < 32;
{
    BitsToWord(BitShiftRight(WordToBits(x), amount))
}

function LeftShift(x:uint32, amount:uint32) : uint32
    requires amount < 32;
{
    BitsToWord(BitShiftLeft(WordToBits(x), amount))
}

function {:opaque} BitwiseAdd32(x:uint32, y:uint32):uint32
{
    (x + y) % 0x1_0000_0000
}

function {:opaque} BitwiseAdd64(x:uint64, y:uint64):uint64
{
    (x + y) % 0x1_0000_0000_0000_0000
}

function BitwiseSub32(x:uint32, y:uint32):uint32
{
    BitsToWord(BitSub(WordToBits(x), WordToBits(y)))
}

function BitwiseMul32(x:uint32, y:uint32):uint32
{
    BitsToWord(BitMul(WordToBits(x), WordToBits(y)))
}

function BitwiseDiv32(x:uint32, y:uint32):uint32
    requires y != 0;
{
    if WordToBits(y) == 0 then 0 else BitsToWord(BitDiv(WordToBits(x), WordToBits(y)))
}

function BitwiseMod32(x:uint32, y:uint32):uint32
    requires y != 0;
{
    if WordToBits(y) == 0 then 0 else BitsToWord(BitMod(WordToBits(x), WordToBits(y)))
}

function QuadwordXor(a:Quadword, b:Quadword) : Quadword
{
    Quadword(BitwiseXor(a.lo, b.lo),
             BitwiseXor(a.mid_lo, b.mid_lo),
             BitwiseXor(a.mid_hi, b.mid_hi),
             BitwiseXor(a.hi, b.hi))
}

lemma {:axiom} lemma_BitMulEquiv(x:uint32, y:uint32)
    requires 0 <= x * y < 0x1_0000_0000;
    ensures  BitsToWord(BitMul(WordToBits(x), WordToBits(y))) == x * y;

lemma {:axiom} lemma_BitDivEquiv(x:uint32, y:uint32)
    requires y != 0;
    requires WordToBits(y) != 0;
    ensures  BitsToWord(BitDiv(WordToBits(x), WordToBits(y))) == x / y;

lemma {:axiom} lemma_BitCmpEquiv(x:uint32, y:uint32)
    ensures x > y ==> WordToBits(x) > WordToBits(y)
    ensures x < y ==> WordToBits(x) < WordToBits(y)
    ensures x == y ==> WordToBits(x) == WordToBits(y)

lemma {:axiom} lemma_RotateRightCommutesXor(x:uint32, amt_0:nat, amt_1:nat, amt_2:nat)
    requires 0 <= amt_0 < 32;
    requires 0 <= amt_1 < 32;
    requires 0 <= amt_2 < 32;
    requires amt_1 >= amt_0;
    requires amt_2 >= amt_0;
    ensures  RotateRight(BitwiseXor(BitwiseXor(x, RotateRight(x, amt_1-amt_0)), RotateRight(x, amt_2-amt_0)), amt_0)
             == BitwiseXor(BitwiseXor(RotateRight(x, amt_0), RotateRight(x, amt_1)),
                           RotateRight(x, amt_2));
// TODO: Waiting on Dafny to support RotateRight
//{
//    reveal_BitXor();
//    reveal_RotateRight();
//    lemma_BitsAndWordConversions();
//}

lemma {:axiom} lemma_BitShiftsSum(x: bv32, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures BitShiftLeft(x, a + b) == BitShiftLeft(BitShiftLeft(x, a), b)
    ensures BitShiftRight(x, a + b) == BitShiftRight(BitShiftRight(x, a), b)

function {:opaque} BitwiseMul64(x:uint64, y:uint64):uint64 { (x * y) % 0x1_0000_0000_0000_0000 }
function {:opaque} BitwiseMul64hi(x:uint64, y:uint64):uint64 { ((x * y) / 0x1_0000_0000_0000_0000) % 0x1_0000_0000_0000_0000 }

function{:opaque} BitAnd64(x:bv64, y:bv64):bv64 { x & y }
function{:opaque} BitwiseAnd64_opaque(x:uint64, y:uint64):uint64 { BitsToWord64(BitAnd64(WordToBits64(x), WordToBits64(y))) }
function BitwiseAnd64(x:uint64, y:uint64):uint64 { BitwiseAnd64_opaque(x, y) }

lemma{:axiom} lemma_bitwise_shifts64(x:uint64)
    requires x < 64
    ensures  WordToBits64(x) < 64

function{:opaque} BitShl64(x:bv64, y:bv64):bv64 requires y < 64 { x << y }
function{:opaque} BitwiseShl64_opaque(x:uint64, y:uint64):uint64
    requires y < 64
{
    lemma_bitwise_shifts64(y);
    BitsToWord64(BitShl64(WordToBits64(x), WordToBits64(y)))
}
function BitwiseShl64(x:uint64, y:uint64):uint64
    requires y < 64
{
    BitwiseShl64_opaque(x, y)
}

function{:opaque} BitShr64(x:bv64, y:bv64):bv64 requires y < 64 { x >> y }
function{:opaque} BitwiseShr64_opaque(x:uint64, y:uint64):uint64
    requires y < 64
{
    lemma_bitwise_shifts64(y);
    BitsToWord64(BitShr64(WordToBits64(x), WordToBits64(y)))
}
function BitwiseShr64(x:uint64, y:uint64):uint64
    requires y < 64
{
    BitwiseShr64_opaque(x, y)
}

} // end module ops
