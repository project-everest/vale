include "types.s.dfy"
include "words_and_bytes.s.dfy"
include "../math/power2.i.dfy"
include "../collections/Seqs.i.dfy"

module words_and_bytes_i {

import opened types_s
import opened Math__power2_i
import opened Math__power2_s
import opened words_and_bytes_s
import opened Collections__Seqs_i

lemma {:induction} lemma_BEByteSeqToInt_bound(bytes:seq<uint8>)
    ensures 0 <= BEByteSeqToInt(bytes);
    ensures BEByteSeqToInt(bytes) < power2(8*|bytes|);
{
    lemma_2toX();
    if bytes == [] {
    } else {
        calc {
            BEByteSeqToInt(bytes[..|bytes|-1]) + 1;
            <=
            power2(8*(|bytes|-1));
        }

        calc {
            BEByteSeqToInt(bytes);
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + (bytes[|bytes|-1] as int);
            <
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + 256;
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + 1 * 256;
            (BEByteSeqToInt(bytes[..|bytes|-1]) + 1) * 256;
            <=
            power2(8*(|bytes|-1)) * 256;
            power2(8*(|bytes|-1)) * power2(8);
                { lemma_power2_adds(8*(|bytes|-1), 8); }
            power2(8*|bytes|);
        }
    }
}

// Prove inverse in one direction: BEByteSeqToInt(BEUintToSeqByte(val, width)) == val
lemma lemma_BEUintToSeqByte_invertability(bytes:seq<uint8>, val:int, width:nat)
    requires bytes == BEUintToSeqByte(val, width);
    requires 0 <= val < power2(8*width);
    requires |bytes| == width;
    ensures  BEByteSeqToInt(bytes) == val;
{
    lemma_2toX32();
    if width == 0 {
        assert BEUintToSeqByte(val, width) == [];
        assert power2(width) == 1;
        assert val == 0;
    } else {
        calc {
            val / 0x100;
            < { lemma_power2_adds(8*width-8, 8);
                lemma_div_by_multiple_is_strongly_ordered(val, power2(8*width), power2(8*width-8), power2(8)); }
            power2(8*width) / 0x100;
            power2(8*width) / power2(8);
                { lemma_power2_div_is_sub(8, 8*width); }
            power2(8*(width - 1));
        }

        calc {
            BEByteSeqToInt(bytes);
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + (bytes[|bytes|-1] as int);
                { lemma_BEUintToSeqByte_invertability(bytes[..|bytes|-1], val / 0x100, width - 1); }
            (val / 0x100) * 256 + (bytes[|bytes|-1] as int);
            val;
        }
    }
}

// Prove inverse in the other direction: BEUintToSeqByte(BEByteSeqToInt(bytes), width) == bytes
lemma lemma_BEByteSeqToInt_invertability(bytes:seq<uint8>, val:int, width:nat)
    requires BEByteSeqToInt(bytes) == val;
    requires 0 <= val < power2(8*width);
    requires |bytes| == width;
    ensures  bytes == BEUintToSeqByte(val, width);
{
    lemma_2toX32();
    if width == 0 {
        assert BEUintToSeqByte(val, width) == [];
        assert power2(width) == 1;
        assert val == 0;
    } else {
        calc {
            val / 0x100;
            < { lemma_power2_adds(8*width-8, 8);
                lemma_div_by_multiple_is_strongly_ordered(val, power2(8*width), power2(8*width-8), power2(8)); }
            power2(8*width) / 0x100;
            power2(8*width) / power2(8);
                { lemma_power2_div_is_sub(8, 8*width); }
            power2(8*(width - 1));
        }

        calc {
            BEUintToSeqByte(val, width);
            BEUintToSeqByte(val/0x100, width - 1) + [ (val % 0x100) as uint8 ];
                { lemma_BEByteSeqToInt_invertability(bytes[..|bytes|-1], val / 0x100, width - 1); }
            bytes[..|bytes|-1] + [ (val % 0x100) as uint8 ];
            bytes;
        }
    }
}

// Inverse lemma forall values
lemma lemma_BEByteSeqToInt_BEUintToSeqByte_invertability()
    ensures forall bytes:seq<uint8>, width:nat ::
            |bytes| == width ==> bytes == BEUintToSeqByte(BEByteSeqToInt(bytes), width);
    ensures forall val:int, width:nat :: 0 <= val < power2(8*width) ==>
            val == BEByteSeqToInt(BEUintToSeqByte(val, width));
{
    forall bytes:seq<uint8>, width:nat | |bytes| == width
        ensures bytes == BEUintToSeqByte(BEByteSeqToInt(bytes), width);
    {
        lemma_BEByteSeqToInt_bound(bytes);
        lemma_BEByteSeqToInt_invertability(bytes, BEByteSeqToInt(bytes), width);
    }
    forall val:int, width:nat | 0 <= val < power2(8*width)
        ensures val   == BEByteSeqToInt(BEUintToSeqByte(val, width));
    {
        lemma_BEUintToSeqByte_invertability(BEUintToSeqByte(val, width), val, width);
    }
}

//lemma lemma_BytesToWord_is_BEByteSeqToInt(b0:uint8, b1:uint8, b2:uint8, b3:uint8)
//    ensures int(BytesToWord(b0, b1, b2, b3)) == BEByteSeqToInt([b0, b1, b2, b3])
//{
//    reveal_BytesToWord();
//}
//
//
//lemma lemma_WordToBytes_is_BEUintToSeqByte(u:uint32)
//    ensures WordToBytes(u) == BEUintToSeqByte(int(u), 4)
//{
//    var bytes := WordToBytes(u);
//    var u_int := int(u);
//
//    reveal_WordToBytes();
////    assert bytes[0] == uint8(u_int / 0x1000000);
////    assert bytes[1] == uint8((u_int / 0x10000) % 0x100);
////    assert bytes[2] == uint8((u_int/0x100) % 0x100);
////    assert bytes[3] == uint8(u_int % 0x100);
////    assume false;
//
//    calc {
//        BEUintToSeqByte(u_int, 4);
//        BEUintToSeqByte(u_int/0x100, 3) + [ uint8(u_int % 0x100) ];
//        BEUintToSeqByte((u_int/0x100/0x100), 2) + [ uint8((u_int/0x100) % 0x100) ] + [ uint8(u_int % 0x100) ];
//            { lemma_div_denominator(int(u_int), 0x100, 0x100); }
//        BEUintToSeqByte((u_int/0x10000), 2) + [ uint8((u_int/0x100) % 0x100) ] + [ uint8(u_int % 0x100) ];
//            { lemma_div_denominator(int(u_int), 0x10000, 0x100); }
//        BEUintToSeqByte(u_int/0x1000000, 1) + [ uint8((u_int / 0x10000) % 0x100) ] + [ uint8((u_int/0x100) % 0x100) ] + [ uint8(u_int % 0x100) ];
//            { lemma_div_denominator(int(u_int), 0x1000000, 0x100); }
//        BEUintToSeqByte(u_int/0x100000000, 0) + [ uint8((u_int / 0x1000000) % 0x100) ] + [ uint8((u_int / 0x10000) % 0x100) ] + [ uint8((u_int/0x100) % 0x100) ] + [ uint8(u_int % 0x100) ];
//        [ uint8((u_int / 0x1000000) % 0x100) ] + [ uint8((u_int / 0x10000) % 0x100) ] + [ uint8((u_int/0x100) % 0x100) ] + [ uint8(u_int % 0x100) ];
//            { lemma_div_denominator(int(u_int), 0x1000000, 0x100); }
//        [ uint8(u_int / 0x1000000) ] + [ uint8((u_int / 0x10000) % 0x100) ] + [ uint8((u_int/0x100) % 0x100) ] + [ uint8(u_int % 0x100) ];
//        [bytes[0]] + [bytes[1]] + [bytes[2]] + [bytes[3]];
//        bytes;
//    }
//}

lemma lemma_SeqAppendCommutes<T>(a:T, b:T, c:T, d:T)
    ensures [a] + [b] + [c] + [d] == [a] + [b] + ([c] + [d]);
{

}

lemma lemma_BytesToWord_WordToBytes_inverses(b0:uint8, b1:uint8, b2:uint8, b3:uint8)
    ensures WordToBytes(BytesToWord(b0,b1,b2,b3)) == [b0,b1,b2,b3];
{
    reveal_BytesToWord();
    reveal_WordToBytes();
    lemma_2toX();
    var bytes := [b0,b1,b2,b3];
    lemma_BEByteSeqToInt_bound(bytes);
    lemma_BEByteSeqToInt_invertability(bytes, BEByteSeqToInt(bytes), 4);
}

lemma lemma_WordToBytes_BytesToWord_inverses(x:uint32)
    ensures var bytes := WordToBytes(x);
            x == BytesToWord(bytes[0], bytes[1], bytes[2], bytes[3]);
{
    var bytes := WordToBytes(x);
    lemma_BEByteSeqToInt_bound(bytes);
    lemma_2toX();

    var val := x as int;
    calc {
        val;
            { lemma_BEByteSeqToInt_BEUintToSeqByte_invertability(); }
        BEByteSeqToInt(BEUintToSeqByte(val, |bytes|));
        BEByteSeqToInt(BEUintToSeqByte(val as int, |bytes|));
            { reveal_WordToBytes(); }
        BEByteSeqToInt(WordToBytes(val as uint32));
        BEByteSeqToInt(bytes);
            { reveal_BytesToWord();
              assert bytes == [bytes[0], bytes[1], bytes[2], bytes[3]]; }
        BytesToWord(bytes[0], bytes[1], bytes[2], bytes[3]) as int;
    }
}

lemma lemma_WordSeqToBytes_Adds(ws1:seq<uint32>, ws2:seq<uint32>)
    ensures WordSeqToBytes(ws1) + WordSeqToBytes(ws2) == WordSeqToBytes(ws1 + ws2);
{
    //lemma_FunctionAdds(ws1, ws2, WordSeqToBytes, WordToBytes);
    if |ws1| == 0 {
    } else {
        calc {
            WordSeqToBytes(ws1) + WordSeqToBytes(ws2);
            WordToBytes(ws1[0]) + WordSeqToBytes(ws1[1..]) + WordSeqToBytes(ws2);
                { SeqAdditionIsAssociative(WordToBytes(ws1[0]), WordSeqToBytes(ws1[1..]), WordSeqToBytes(ws2)); }
            WordToBytes(ws1[0]) + (WordSeqToBytes(ws1[1..]) + WordSeqToBytes(ws2));
                { lemma_WordSeqToBytes_Adds(ws1[1..], ws2); }
            WordToBytes(ws1[0]) + WordSeqToBytes(ws1[1..] + ws2);
                { assert (ws1 + ws2)[0] == ws1[0];
                  assert (ws1 + ws2)[1..] == ws1[1..] + ws2;
                  assert [ws1[0]] + ws1[1..] + ws2 == ws1 + ws2; }
            WordSeqToBytes(ws1 + ws2);
        }
    }
}

lemma lemma_WordToBytes_injective(w1:uint32, w2:uint32)
    requires WordToBytes(w1) == WordToBytes(w2);
    ensures  w1 == w2;
{
    reveal_WordToBytes();
    lemma_BEByteSeqToInt_BEUintToSeqByte_invertability();
    lemma_2toX();
}

lemma lemma_WordSeqToBytes_indexed(ws:seq<uint32>)
    ensures var bytes := WordSeqToBytes(ws);
            forall i :: 0 <= i < |ws| ==> bytes[i*4..(i+1)*4] == WordToBytes(ws[i]);
{
    if |ws| == 0 {
        return;
    }

    var bytes := WordSeqToBytes(ws);
    var ws' := ws[1..];
    var bytes' := bytes[4..];

    calc {
        bytes[0..4] + bytes[4..];
        bytes;
        WordToBytes(ws[0]) + WordSeqToBytes(ws[1..]);
    }
    assert WordToBytes(ws[0]) == bytes[0..4];
    assert bytes' == WordSeqToBytes(ws[1..]);
    lemma_WordSeqToBytes_indexed(ws[1..]);

    forall i | 0 <= i < |ws|
        ensures bytes[i*4..(i+1)*4] == WordToBytes(ws[i]);
    {
        if i == 0 {
            assert bytes[i*4..(i+1)*4] == WordToBytes(ws[i]);
        }
        else {
            calc {
                bytes[i*4..(i+1)*4];
                bytes'[(i-1)*4..(i-1+1)*4];
                WordToBytes(ws'[i-1]);
                WordToBytes(ws[i]);
            }
        }
    }
}

lemma lemma_WordSeqToBytesInjective(ws1:seq<uint32>, ws2:seq<uint32>)
    requires WordSeqToBytes(ws1) == WordSeqToBytes(ws2);
    ensures  ws1 == ws2;
{
    if |ws1| == 0 || |ws2| == 0 {
        return;
    }

    lemma_WordToBytes_injective(ws1[0], ws2[0]);
    lemma_WordSeqToBytesInjective(ws1[1..], ws2[1..]);
}

lemma lemma_RepeatValueTail<T>(n:T, count:int)
    requires count > 0;
    ensures  RepeatValue(n, count)[1..] == RepeatValue(n, count-1);
{
    if count == 1 {
        return;
    }

    calc {
        RepeatValue(n, count)[1..];
        (RepeatValue(n, count-1) + [n])[1..];
        RepeatValue(n, count-1)[1..] + [n];
            { lemma_RepeatValueTail(n, count-1); }
        RepeatValue(n, count-2) + [n];
        RepeatValue(n, count-1);
    }
}

}
