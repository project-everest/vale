include "operations.s.dfy"
include "../math/power2.s.dfy"

module operations_i {

import opened operations_s
import opened Math__power2_s

// useful properties of power2
predicate power2_properties(n:nat)
{
    (n >= 2 ==> power2(n) % 4 == 0)
    && power2(10) == 0x400
    && power2(12) == 0x1000
}

lemma lemma_power2_properties(n:nat)
    ensures power2_properties(n)
{
    reveal_power2();
}

lemma lemma_WordToBitsPreservesZeroness(w:uint32)
    ensures  w == 0 <==> WordToBits(w) == 0;
{
    reveal_WordToBits();
    lemma_WordToBitsToWord(w);

    if w == 0 {
        calc {
            WordToBits(w);
            w as bv32;
            0 as bv32;
            0;
        }
    }
    else {
        assert WordToBits(w) != 0;
    }

    if WordToBits(w) == 0 {
        assert w == 0;
    }
    else {
        assert w != 0;
    }
}

lemma lemma_BitsToWordPreservesZeroness(b:bv32)
    ensures  b == 0 <==> BitsToWord(b) == 0;
{
    var w := BitsToWord(b);
    lemma_WordToBitsPreservesZeroness(w);
    lemma_BitsToWordToBits(b);
}

lemma lemma_BitsAndWordConversions()
    ensures forall w:uint32 :: BitsToWord(WordToBits(w)) == w;
    ensures forall b:bv32 :: WordToBits(BitsToWord(b)) == b;
{
    forall w:uint32
        ensures BitsToWord(WordToBits(w)) == w;
    {
        lemma_WordToBitsToWord(w);
    }
    forall b:bv32
        ensures WordToBits(BitsToWord(b)) == b;
    {
        lemma_BitsToWordToBits(b);
    }
}

lemma lemma_BitwiseDiv32Simplified(x:uint32, y:uint32)
    requires y != 0;
    ensures  WordToBits(y) != 0;
    ensures  BitwiseDiv32(x, y) == BitsToWord(BitDiv(WordToBits(x), WordToBits(y)));
{
    var z := BitwiseDiv32(x, y);
    lemma_WordToBitsPreservesZeroness(y);
}

lemma lemma_BitwiseMod32Simplified(x:uint32, y:uint32)
    requires y != 0;
    ensures  WordToBits(y) != 0;
    ensures  BitwiseMod32(x, y) == BitsToWord(BitMod(WordToBits(x), WordToBits(y)));
{
    var z := BitwiseMod32(x, y);
    lemma_WordToBitsPreservesZeroness(y);
}

lemma lemma_BitXorWithZero(x:bv32)
    ensures BitXor(x, 0) == x;
{
    reveal_BitXor();
}

lemma lemma_BitwiseXorWithZero(x:uint32)
    ensures BitwiseXor(x, 0) == x;
{
    calc {
        BitwiseXor(x, 0);
        BitsToWord(BitXor(WordToBits(x), WordToBits(0)));
            { lemma_WordToBitsPreservesZeroness(0); assert WordToBits(0) == 0; }
        BitsToWord(BitXor(WordToBits(x), 0));
            { lemma_BitXorWithZero(WordToBits(x)); }
        BitsToWord(WordToBits(x));
            { lemma_WordToBitsToWord(x); }
        x;
    }
}

lemma lemma_BitXorCommutative(x:bv32, y:bv32)
    ensures BitXor(x, y) == BitXor(y, x);
{
    reveal_BitXor();
}

lemma lemma_BitwiseXorCommutative(x:uint32, y:uint32)
    ensures BitwiseXor(x, y) == BitwiseXor(y, x);
{
    calc {
        BitwiseXor(x, y);
        BitsToWord(BitXor(WordToBits(x), WordToBits(y)));
            { lemma_BitXorCommutative(WordToBits(x), WordToBits(y)); }
        BitsToWord(BitXor(WordToBits(y), WordToBits(x)));
        BitwiseXor(y, x);
    }
}

lemma lemma_BitXorWithItself(x:bv32)
    ensures BitXor(x, x) == 0;
{
    reveal_BitXor();
}

lemma lemma_BitwiseXorWithItself(x:uint32)
    ensures BitwiseXor(x, x) == 0;
{
    calc {
        BitwiseXor(x, x);
        BitsToWord(BitXor(WordToBits(x), WordToBits(x)));
            { lemma_BitXorWithItself(WordToBits(x)); }
        BitsToWord(0);
            { lemma_BitsToWordPreservesZeroness(0); }
        0;
    }
}

lemma lemma_BitXorAssociativity(x:bv32, y:bv32, z:bv32)
    ensures BitXor(x, BitXor(y, z)) == BitXor(BitXor(x, y), z);
{
    reveal_BitXor();
}

lemma lemma_BitwiseXorAssociative(x:uint32, y:uint32, z:uint32)
    ensures BitwiseXor(x, BitwiseXor(y,z)) == BitwiseXor(BitwiseXor(x,y), z);
{
    calc {
        BitwiseXor(x, BitwiseXor(y, z));
        BitsToWord(BitXor(WordToBits(x), WordToBits(BitwiseXor(y, z))));
        BitsToWord(BitXor(WordToBits(x), WordToBits(BitsToWord(BitXor(WordToBits(y), WordToBits(z))))));
            { lemma_BitsToWordToBits(BitXor(WordToBits(y), WordToBits(z))); }
        BitsToWord(BitXor(WordToBits(x), BitXor(WordToBits(y), WordToBits(z))));
            { lemma_BitXorAssociativity(WordToBits(x), WordToBits(y), WordToBits(z)); }
        BitsToWord(BitXor(BitXor(WordToBits(x), WordToBits(y)), WordToBits(z)));
            { lemma_BitsToWordToBits(BitXor(WordToBits(x), WordToBits(y))); }
        BitsToWord(BitXor(WordToBits(BitsToWord(BitXor(WordToBits(x), WordToBits(y)))), WordToBits(z)));
        BitsToWord(BitXor(WordToBits(BitwiseXor(x,y)), WordToBits(z)));
        BitwiseXor(BitwiseXor(x,y), z);
    }
}

lemma lemma_BitAndCommutative(x:bv32, y:bv32)
    ensures BitAnd(x, y) == BitAnd(y, x);
{
    reveal_BitAnd();
}

lemma lemma_BitwiseAndCommutative(x:uint32, y:uint32)
    ensures BitwiseAnd(x, y) == BitwiseAnd(y, x);
{
    calc {
        BitwiseAnd(x, y);
        BitsToWord(BitAnd(WordToBits(x), WordToBits(y)));
            { lemma_BitAndCommutative(WordToBits(x), WordToBits(y)); }
        BitsToWord(BitAnd(WordToBits(y), WordToBits(x)));
        BitwiseAnd(y, x);
    }
}

lemma lemma_BitOrCommutative(x:bv32, y:bv32)
    ensures BitOr(x, y) == BitOr(y, x);
{
    reveal_BitOr();
}

lemma lemma_BitOrAssociative(a: bv32, b:bv32, c: bv32)
    ensures BitOr(a, BitOr(b, c)) == BitOr(BitOr(a, b), c);
{
    reveal_BitOr();
}

lemma lemma_BitwiseOrCommutative(x:uint32, y:uint32)
    ensures BitwiseOr(x, y) == BitwiseOr(y, x);
{
    calc {
        BitwiseOr(x, y);
        BitsToWord(BitOr(WordToBits(x), WordToBits(y)));
            { lemma_BitOrCommutative(WordToBits(x), WordToBits(y)); }
        BitsToWord(BitOr(WordToBits(y), WordToBits(x)));
        BitwiseOr(y, x);
    }
}

lemma lemma_BitOrAndRelation(a: bv32, b:bv32, c: bv32)
    ensures BitAnd(BitOr(a, b), c) == BitOr(BitAnd(a, c), BitAnd(b, c));
{
    reveal_BitAnd();
    reveal_BitOr();
}

lemma lemma_BitwiseAdd32EquivalentToAddMod2To32(x:uint32, y:uint32)
    ensures BitwiseAdd32(x, y) == (x + y) % 0x1_0000_0000;
{
    reveal_BitwiseAdd32();
}

lemma lemma_BitwiseAdd64EquivalentToAddMod2To64(x:uint64, y:uint64)
    ensures BitwiseAdd64(x, y) == (x + y) % 0x1_0000_0000_0000_0000;
{
    reveal_BitwiseAdd64();
}


lemma lemma_BitwiseAdd32Commutative(x:uint32, y:uint32)
    ensures BitwiseAdd32(x, y) == BitwiseAdd32(y, x);
{
    reveal_BitwiseAdd32();
}

lemma lemma_BitwiseAdd32CommutativeAlways()
    ensures forall x:uint32, y:uint32 :: BitwiseAdd32(x, y) == BitwiseAdd32(y, x);
{
    reveal_BitwiseAdd32();
}

lemma lemma_BitwiseCommutative(x:uint32, y:uint32)
    ensures BitwiseAnd(x, y) == BitwiseAnd(y, x);
    ensures BitwiseXor(x, y) == BitwiseXor(y, x);
    ensures BitwiseOr(x, y) == BitwiseOr(y, x);
{
    lemma_BitwiseAndCommutative(x, y);
    lemma_BitwiseOrCommutative(x, y);
    lemma_BitwiseXorCommutative(x, y);
}

lemma lemma_QuadwordXorWithItself(x:Quadword)
    ensures QuadwordXor(x, x) == Quadword(0, 0, 0, 0);
{
    lemma_BitwiseXorWithItself(x.lo);
    lemma_BitwiseXorWithItself(x.mid_lo);
    lemma_BitwiseXorWithItself(x.mid_hi);
    lemma_BitwiseXorWithItself(x.hi);
}

lemma lemma_QuadwordXorAlwaysCommutes()
    ensures forall a, b :: QuadwordXor(a, b) == QuadwordXor(b, a);
{
    forall a, b
        ensures QuadwordXor(a, b) == QuadwordXor(b, a) 
    {
        lemma_BitwiseXorCommutative(a.lo, b.lo);
        lemma_BitwiseXorCommutative(a.mid_lo, b.mid_lo);
        lemma_BitwiseXorCommutative(a.mid_hi, b.mid_hi);
        lemma_BitwiseXorCommutative(a.hi, b.hi);
    }
}

method ComputeBitwiseXor(x:uint, y:uint) returns (z:uint)
    ensures z == BitwiseXor(x as uint32, y as uint32) as uint;
{
    var xb := WordToBits(x as uint32);
    var yb := WordToBits(y as uint32);
    var zb := BitXor(xb, yb);
    z := BitsToWord(zb) as uint;
}

lemma lemma_BitShiftLeft1(x: bv32)
    requires x < 0x80000000;
    ensures  BitShiftLeft(x, 1) == BitMul(x, 2);
{
    calc {
        BitShiftLeft(x, 1);
        { reveal_BitShiftLeft(); }
        x << 1;
        x * 2;
        { reveal_BitMul(); }
        BitMul(x, 2);
    }
}

lemma lemma_BitShiftRight1(x: bv32)
    ensures BitShiftRight(x, 1) == BitDiv(x, 2)
{
    calc {
        BitShiftRight(x, 1);
        { reveal_BitShiftRight(); }
        x >> 1;
        x / 2;
        { reveal_BitDiv(); }
        BitDiv(x, 2);
    }
}

lemma lemma_LeftShift1(x: uint32)
    requires x < 0x80000000
    ensures LeftShift(x, 1) == x * 2
{
    calc {
        LeftShift(x, 1);
        BitsToWord(BitShiftLeft(WordToBits(x), 1));
        { lemma_BitCmpEquiv(x, 0x80000000);
          assert WordToBits(0x80000000) == 0x80000000 by { reveal_WordToBits(); }
          lemma_BitShiftLeft1(WordToBits(x)); }
        BitsToWord(BitMul(WordToBits(x), 2));
        { assert WordToBits(2) == 2 by { reveal_WordToBits(); } }
        BitsToWord(BitMul(WordToBits(x), WordToBits(2)));
        { lemma_BitMulEquiv(x, 2); }
        x * 2;
    }
}

lemma lemma_RightShift1(x: uint32)
    ensures RightShift(x, 1) == x / 2
{
    assert WordToBits(2) == 2 by { reveal_WordToBits(); }

    calc {
        RightShift(x, 1);
        BitsToWord(BitShiftRight(WordToBits(x), 1));
        { lemma_BitShiftRight1(WordToBits(x)); }
        BitsToWord(BitDiv(WordToBits(x), 2));
        BitsToWord(BitDiv(WordToBits(x), WordToBits(2)));
        { lemma_BitDivEquiv(x, 2); }
        x / 2;
    }
}

lemma lemma_ShiftsAdd(x: uint32, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures LeftShift(x, a + b) == LeftShift(LeftShift(x, a), b)
    ensures RightShift(x, a + b) == RightShift(RightShift(x, a), b)
{
    calc {
        LeftShift(x, a + b);
        BitsToWord(BitShiftLeft(WordToBits(x), a + b));
        { lemma_BitShiftsSum(WordToBits(x), a, b); }
        BitsToWord(BitShiftLeft(BitShiftLeft(WordToBits(x), a), b));
        { lemma_BitsToWordToBits(BitShiftLeft(WordToBits(x), a)); }
        BitsToWord(BitShiftLeft(WordToBits(BitsToWord(BitShiftLeft(WordToBits(x), a))), b));
        BitsToWord(BitShiftLeft(WordToBits(LeftShift(x, a)), b));
        LeftShift(LeftShift(x, a), b);
    }

    calc {
        RightShift(x, a + b);
        BitsToWord(BitShiftRight(WordToBits(x), a + b));
        { lemma_BitShiftsSum(WordToBits(x), a, b); }
        BitsToWord(BitShiftRight(BitShiftRight(WordToBits(x), a), b));
        { lemma_BitsToWordToBits(BitShiftRight(WordToBits(x), a)); }
        BitsToWord(BitShiftRight(WordToBits(BitsToWord(BitShiftRight(WordToBits(x), a))), b));
        BitsToWord(BitShiftRight(WordToBits(RightShift(x, a)), b));
        RightShift(RightShift(x, a), b);
    }
}

lemma lemma_LeftShift2(x: uint32)
    requires x < 0x40000000
    ensures LeftShift(x, 2) == x * 4
{
    var x' := LeftShift(x, 1);
    lemma_LeftShift1(x);
    lemma_LeftShift1(x');
    lemma_ShiftsAdd(x, 1, 1);
}

lemma lemma_LeftShift4(x: uint32)
    requires x < 0x10000000
    ensures LeftShift(x, 4) == x * 16
{
    var x' := LeftShift(x, 2);
    lemma_LeftShift2(x);
    lemma_LeftShift2(x');
    lemma_ShiftsAdd(x, 2, 2);
}

lemma lemma_LeftShift12(x: uint32)
    requires x < 0x100000
    ensures LeftShift(x, 12) == x * 4096
{
    var x' := LeftShift(x, 4);
    lemma_LeftShift4(x);
    var x'' := LeftShift(x', 4);
    lemma_LeftShift4(x');
    lemma_ShiftsAdd(x, 4, 4);
    assert x'' == LeftShift(x, 8);
    assert x'' == x * 256;
    var x''' := LeftShift(x'', 4);
    lemma_LeftShift4(x'');
    assert x''' == x * 4096;
    lemma_ShiftsAdd(x, 8, 4);
    assert x''' == LeftShift(x, 12);
}

lemma lemma_RightShift2(x: uint32)
    ensures RightShift(x, 2) == x / 4
{
    var x' := RightShift(x, 1);
    lemma_RightShift1(x);
    lemma_RightShift1(x');
    lemma_ShiftsAdd(x, 1, 1);
}

lemma lemma_RightShift4(x: uint32)
    ensures RightShift(x, 4) == x / 16
{
    var x' := RightShift(x, 2);
    lemma_RightShift2(x);
    lemma_RightShift2(x');
    lemma_ShiftsAdd(x, 2, 2);
}

lemma lemma_RightShift12(x: uint32)
    ensures RightShift(x, 12) == x / 4096
{
    var x' := RightShift(x, 4);
    lemma_RightShift4(x);
    var x'' := RightShift(x', 4);
    lemma_RightShift4(x');
    lemma_ShiftsAdd(x, 4, 4);
    assert x'' == RightShift(x, 8);
    assert x'' == x / 256;
    var x''' := RightShift(x'', 4);
    lemma_RightShift4(x'');
    assert x''' == x / 4096;
    lemma_ShiftsAdd(x, 8, 4);
    assert x''' == RightShift(x, 12);
}

} // end module operations_i
