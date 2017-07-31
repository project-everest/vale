include "types.s.dfy"

module words_and_bytes_s {
import opened types_s

predicate isUInt32(n:int)
{
    0 <= n < 0x1_0000_0000
}

// Map an arbitrary number of bytes to an integer
function BEByteSeqToInt(bytes:seq<uint8>) : int
    decreases |bytes|;
{
    if bytes == [] then 0
    else BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + (bytes[|bytes|-1] as int)
}

// Map a big-endian integer to a sequence of bytes
function BEUintToSeqByte(v:int, width:int) : seq<uint8>
    ensures width >= 0 && v >= 0 ==> |BEUintToSeqByte(v, width)| == width;
{
    if width > 0 && v >= 0 then
        BEUintToSeqByte(v/0x100, width - 1) + [ (v % 0x100) as uint8 ]
    else
        []
}

function {:opaque} BytesToWord(b0:uint8, b1:uint8, b2:uint8, b3:uint8) : uint32
{
    var w := BEByteSeqToInt([b0, b1, b2, b3]);
    if 0 <= w < 0x1_0000_0000 then (w as uint32) else 42
    // We defer the proof that BEByteSeqToInt is in bounds to the verified implementation
}

function{:opaque} WordToBytes(w:uint32) : seq<uint8>
    ensures |WordToBytes(w)| == 4;
{
    BEUintToSeqByte(w as int, 4)
//    [ uint8( w/ 0x1000000),
//      uint8((w/   0x10000) % 256),
//      uint8((w/     0x100) % 256),
//      uint8(w              % 256) ]
}

function{:opaque} Word64ToBytes(w:uint64) : seq<uint8>
    ensures |Word64ToBytes(w)| == 8;
{
    BEUintToSeqByte(w as int, 8)
}

function{:opaque} Word128ToBytes(w:uint128) : seq<uint8>
    ensures |Word128ToBytes(w)| == 16;
{
    BEUintToSeqByte(w as int, 16)
}

function {:opaque} Uint64ToBytes(u:uint64) : seq<uint8>
    ensures |Uint64ToBytes(u)| == 8;
{
    [ ( u/ 0x100000000000000) as uint8,
      ((u/   0x1000000000000) % 0x100) as uint8,
      ((u/     0x10000000000) % 0x100) as uint8,
      ((u/       0x100000000) % 0x100) as uint8,
      ((u/         0x1000000) % 0x100) as uint8,
      ((u/           0x10000) % 0x100) as uint8,
      ((u/             0x100) % 0x100) as uint8,
      ((u                   ) % 0x100) as uint8]
}

function WordSeqToBytes(ws:seq<uint32>) : seq<uint8>
    ensures |WordSeqToBytes(ws)| == |ws| * 4;
    //ensures var bytes := WordSeqToBytes(ws); forall i :: 0 <= i < |ws| ==> bytes[i*4..(i+1)*4] == WordToBytes(ws[i]);
{
    if |ws| == 0 then [] else WordToBytes(ws[0]) + WordSeqToBytes(ws[1..])
}

function Word64SeqToBytes(ws:seq<uint64>) : seq<uint8>
    ensures |Word64SeqToBytes(ws)| == |ws| * 8;
    //ensures var bytes := WordSeqToBytes(ws); forall i :: 0 <= i < |ws| ==> bytes[i*4..(i+1)*4] == WordToBytes(ws[i]);
{
    if |ws| == 0 then [] else Word64ToBytes(ws[0]) + Word64SeqToBytes(ws[1..])
}

function RepeatByte(b:uint8, count:int) : seq<uint8>
    requires count >= 0;
    ensures  |RepeatByte(b, count)| == count;
    ensures  forall x :: x in RepeatByte(b, count) ==> x == b;
{
    if count == 0 then [] else RepeatByte(b, count-1) + [b]
}

function RepeatValue<T>(n:T, count:int) : seq<T>
    requires count >= 0;
    ensures  |RepeatValue(n, count)| == count;
    ensures  forall x :: x in RepeatValue(n, count) ==> x == n;
{
    if count == 0 then [] else RepeatValue(n, count-1) + [n]
}

function ConcatenateSeqs<T>(ss:seq<seq<T>>) : seq<T>
{
    if |ss| == 0 then [] else ss[0] + ConcatenateSeqs(ss[1..])
}

}
