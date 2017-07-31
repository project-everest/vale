include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"

// Machine translation of the FIPS 180-4 spec:
// http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

module sha512_s {

import opened operations_s
import opened words_and_bytes_s

function method{:opaque} K_SHA512(t:uint32) : uint64
    requires 0 <= t < 80;
{
 [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817][t]
}

function method{:opaque} InitialH_SHA512(j:int) : uint64
    requires 0 <= j <= 7;
{
  [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
   0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179][j]
}

function {:opaque} Sigma0(x:uint64) : uint64
{
  BitwiseXor64(BitwiseXor64(RotateRight64(x, 28), RotateRight64(x, 34)), RotateRight64(x, 39))
}

function {:opaque} Sigma1(x:uint64) : uint64
{
  BitwiseXor64(BitwiseXor64(RotateRight64(x, 14), RotateRight64(x, 18)), RotateRight64(x, 41))
}

function {:opaque} sigma0(x:uint64) : uint64
{
  BitwiseXor64(BitwiseXor64(RotateRight64(x, 1), RotateRight64(x, 8)), RightShift64(x, 7))
}

function {:opaque} sigma1(x:uint64) : uint64
{
  BitwiseXor64(BitwiseXor64(RotateRight64(x, 19), RotateRight64(x, 61)), RightShift64(x, 6))
}

function {:opaque} Ch(x:uint64, y:uint64, z:uint64) : uint64
{
    BitwiseXor64(BitwiseAnd64(x, y), BitwiseAnd64(BitwiseNot64(x), z))
}

function {:opaque} Maj(x:uint64, y:uint64, z:uint64) : uint64
{
    BitwiseXor64(BitwiseXor64(BitwiseAnd64(x, y), BitwiseAnd64(x, z)), BitwiseAnd64(y, z))
}

//- The fields of a SHA256Trace have the following meanings:
//-
//-     M[blk][i]       = word #i of message block #blk
//-     W[blk][t]       = W_t during processing of message block #blk
//-     H[blk][j]       = H_j before processing message block #blk
//-     atoh[blk][t].a  = a before step t of processing of message block #blk
//-     ...
//-     atoh[blk][t].h  = h before step t of processing message block #blk

datatype atoh_Type = atoh_c(a:uint64, b:uint64, c:uint64, d:uint64, e:uint64, f:uint64, g:uint64, h:uint64)
datatype SHA512Trace = SHA512Trace(M:seq<seq<uint64>>, H:seq<seq<uint64>>, W:seq<seq<uint64>>, atoh:seq<seq<atoh_Type>>)

function ConvertAtoHToSeq(v:atoh_Type) : seq<uint64>
{
    [v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h]
}

predicate IsCompleteSHA512Trace(z:SHA512Trace)
{
    (forall i :: 0 <= i < |z.M| ==> |z.M[i]| == 16) &&
    |z.H| == |z.M| + 1 &&
    |z.W| == |z.atoh| == |z.M| &&
    (forall blk :: 0 <= blk <  |z.M| ==> |z.W[blk]| == 80) &&
    (forall blk :: 0 <= blk <  |z.M| ==> |z.atoh[blk]| == 81) &&
    (forall blk :: 0 <= blk <= |z.M| ==> |z.H[blk]| == 8)
}

//- Used to avoid matching loops in some uses of forall
//- (avoid formulas of the form "forall i :: ...a[i]...a[i+1]...", which can loop
//- if the trigger is a[i] and the i+1 in the body is used to instantiate the i in the trigger)
function TBlk(blk:int):bool { true }
function TStep(t:uint64):bool { true }

predicate SHA512TraceHasCorrectHs(z:SHA512Trace)
    requires IsCompleteSHA512Trace(z);
{
    (forall j :: 0 <= j < 8 ==> z.H[0][j] == InitialH_SHA512(j)) &&
    (forall blk:int {:trigger TBlk(blk)} :: TBlk(blk) ==> forall j ::
        0 <= blk < |z.M| && 0 <= j < 8 ==> z.H[blk+1][j] == BitwiseAdd64(ConvertAtoHToSeq(z.atoh[blk][64])[j], z.H[blk][j]))
}

predicate SHA512TraceHasCorrectWs(z:SHA512Trace)
    requires IsCompleteSHA512Trace(z);
{
    forall blk ::
        0 <= blk < |z.M| ==>
        forall t:uint64 {:trigger TStep(t)} :: TStep(t) ==>
            (0 <= t <= 15 ==> z.W[blk][t] == z.M[blk][t]) &&
            (16 <= t <= 79 ==> z.W[blk][t] == BitwiseAdd64(BitwiseAdd64(BitwiseAdd64(sigma1(z.W[blk][t-2]), z.W[blk][t-7]), sigma0(z.W[blk][t-15])),
                                                      z.W[blk][t-16]))
}

predicate SHA512TraceHasCorrectatohs(z:SHA512Trace)
    requires IsCompleteSHA512Trace(z);
{
    forall blk :: 0 <= blk < |z.M| ==>
        ConvertAtoHToSeq(z.atoh[blk][0]) == z.H[blk] &&
        forall t:uint64 {:trigger TStep(t)} :: TStep(t) && 0 <= t <= 79 ==>
            (var T1 := BitwiseAdd64(BitwiseAdd64(BitwiseAdd64(BitwiseAdd64(z.atoh[blk][t].h, Sigma1(z.atoh[blk][t].e)),
                                      Ch(z.atoh[blk][t].e, z.atoh[blk][t].f, z.atoh[blk][t].g)), K_SHA512(t)),
                              z.W[blk][t]);
            var T2 := BitwiseAdd64(Sigma0(z.atoh[blk][t].a), Maj(z.atoh[blk][t].a, z.atoh[blk][t].b, z.atoh[blk][t].c));
            z.atoh[blk][t+1].h == z.atoh[blk][t].g &&
            z.atoh[blk][t+1].g == z.atoh[blk][t].f &&
            z.atoh[blk][t+1].f == z.atoh[blk][t].e &&
            z.atoh[blk][t+1].e == BitwiseAdd64(z.atoh[blk][t].d, T1) &&
            z.atoh[blk][t+1].d == z.atoh[blk][t].c &&
            z.atoh[blk][t+1].c == z.atoh[blk][t].b &&
            z.atoh[blk][t+1].b == z.atoh[blk][t].a &&
            z.atoh[blk][t+1].a == BitwiseAdd64(T1, T2))
}

predicate {:autoReq} SHA512TraceIsCorrect(z:SHA512Trace)
{
    SHA512TraceHasCorrectHs(z) && SHA512TraceHasCorrectWs(z) && SHA512TraceHasCorrectatohs(z)
}

function MaxBytesForSHA() : int { 0x1FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF }

predicate WordSeqIsProperlySHAPaddedByteSeq(ws:seq<uint64>, bytes:seq<uint8>)
{
       |bytes| <= MaxBytesForSHA()
    && Word64SeqToBytes(ws) == bytes + [0x80 as uint8] + RepeatByte(0, ((128 - 1 - 128/8) - (|bytes| % 128)) % 128) + Word128ToBytes((|bytes| * 8) as uint128)
}

predicate DoesTraceDemonstrateSHA512(z:SHA512Trace, message:seq<uint8>, hash:seq<uint64>)
{
       IsCompleteSHA512Trace(z)
    && SHA512TraceIsCorrect(z)
    && |message| <= MaxBytesForSHA()
    && WordSeqIsProperlySHAPaddedByteSeq(ConcatenateSeqs(z.M), message)
    && hash == z.H[|z.H|-1]
}

predicate IsSHA512(message:seq<uint8>, hash:seq<uint64>)
{
    exists z:SHA512Trace :: DoesTraceDemonstrateSHA512(z, message, hash)
}

function {:axiom} SHA512(message:seq<uint8>) : seq<uint64>
    requires |message| <= MaxBytesForSHA();
    ensures  IsSHA512(message, SHA512(message));

    
}
