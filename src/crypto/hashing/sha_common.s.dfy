include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"

module sha_common_s {

import opened operations_s
import opened words_and_bytes_s

//-///////////////////////////////////////////////////
//- Ch, Maj, BSIG0, BSIG1, SSIG0, SSIG1
//-///////////////////////////////////////////////////

function {:opaque} Ch(x:uint32, y:uint32, z:uint32) : uint32
{
    BitwiseXor(BitwiseAnd(x, y), BitwiseAnd(BitwiseNot(x), z))
}

function {:opaque} Maj(x:uint32, y:uint32, z:uint32) : uint32
{
    BitwiseXor(BitwiseXor(BitwiseAnd(x, y), BitwiseAnd(x, z)), BitwiseAnd(y, z))
}

function {:opaque} Parity(x:uint32, y:uint32, z:uint32) : uint32
{
    BitwiseXor(BitwiseXor(x, y), z)
}

function {:opaque} ft(t:uint32, x:uint32, y:uint32, z:uint32) : uint32
    requires 0 <= t <= 79;
{

    if t >= 0 && t <= 19 then
        Ch(x, y, z)

    else if t >= 40 && t <= 59 then
        Maj(x, y, z)
    else
        Parity(x, y, z)
}

function {:opaque} BSIG0(x:uint32) : uint32
{
    BitwiseXor(BitwiseXor(RotateRight(x, 2), RotateRight(x, 13)), RotateRight(x, 22))
}

function {:opaque} BSIG1(x:uint32) : uint32
{
    BitwiseXor(BitwiseXor(RotateRight(x, 6), RotateRight(x, 11)), RotateRight(x, 25))
}

function {:opaque} SSIG0(x:uint32) : uint32
{
    BitwiseXor(BitwiseXor(RotateRight(x, 7), RotateRight(x, 18)), RightShift(x, 3))
}

function {:opaque} SSIG1(x:uint32) : uint32
{
    BitwiseXor(BitwiseXor(RotateRight(x, 17), RotateRight(x, 19)), RightShift(x, 10))
}

function{:opaque} BreakIntoBlocks<T>(os:seq<T>, block_size:int) : seq<seq<T>>
    requires 0 < block_size;
    decreases |os|;
{
    if |os| == 0 then []
    else if |os| < block_size then [os]
    else [os[..block_size]] + BreakIntoBlocks(os[block_size..], block_size)
}

function MaxBytesForSHA() : int { 0x1FFF_FFFF_FFFF_FFFF }

predicate WordSeqIsProperlySHAPaddedByteSeq(ws:seq<uint32>, bytes:seq<uint8>)
{
       |bytes| <= MaxBytesForSHA()
    && WordSeqToBytes(ws) == bytes + [0x80 as uint8] + RepeatByte(0, (119 - (|bytes| % 64)) % 64) + Uint64ToBytes((|bytes| * 8) as uint64)
}

//- Used to avoid matching loops in some uses of forall
//- (avoid formulas of the form "forall i :: ...a[i]...a[i+1]...", which can loop
//- if the trigger is a[i] and the i+1 in the body is used to instantiate the i in the trigger)
function TBlk(blk:int):bool { true }
function TStep(t:uint32):bool { true }

}
