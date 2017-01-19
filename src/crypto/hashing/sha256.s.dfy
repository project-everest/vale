include "sha_common.s.dfy"
include "hmac_common.s.dfy"

module sha256_s {

import opened sha_common_s
import opened hmac_common_s

function method{:opaque} K_SHA256(t:uint32) : uint32
    requires 0 <= t <= 63;
{
    [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2][t]
}

function method{:opaque} InitialH_SHA256(j:uint32) : uint32
    requires 0 <= j <= 7;
{
    //OneOf8(j, 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19)
    [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19][j]
}

//- The fields of a SHA256Trace have the following meanings:
//-
//-     M[blk][i]       = word #i of message block #blk
//-     W[blk][t]       = W_t during processing of message block #blk
//-     H[blk][j]       = H_j before processing message block #blk
//-     atoh[blk][t].a  = a before step t of processing of message block #blk
//-     ...
//-     atoh[blk][t].h  = h before step t of processing message block #blk

datatype atoh_Type = atoh_c(a:uint32, b:uint32, c:uint32, d:uint32, e:uint32, f:uint32, g:uint32, h:uint32)
datatype SHA256Trace = SHA256Trace_c(M:seq<seq<uint32>>, H:seq<seq<uint32>>, W:seq<seq<uint32>>, atoh:seq<seq<atoh_Type>>)

function ConvertAtoHToSeq(v:atoh_Type) : seq<uint32>
{
    [v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h]
}

predicate IsCompleteSHA256Trace(z:SHA256Trace)
{
    (forall i :: 0 <= i < |z.M| ==> |z.M[i]| == 16) &&
    |z.H| == |z.M| + 1 &&
    |z.W| == |z.atoh| == |z.M| &&
    (forall blk :: 0 <= blk <  |z.M| ==> |z.W[blk]| == 64) &&
    (forall blk :: 0 <= blk <  |z.M| ==> |z.atoh[blk]| == 65) &&
    (forall blk :: 0 <= blk <= |z.M| ==> |z.H[blk]| == 8)
}

predicate SHA256TraceHasCorrectHs(z:SHA256Trace)
    requires IsCompleteSHA256Trace(z);
{
    (forall j :: 0 <= j < 8 ==> z.H[0][j] == InitialH_SHA256(j)) &&
    (forall blk:int {:trigger TBlk(blk)} :: TBlk(blk) ==> forall j ::
        0 <= blk < |z.M| && 0 <= j < 8 ==> z.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z.atoh[blk][64])[j], z.H[blk][j]))
}

predicate SHA256TraceHasCorrectWs(z:SHA256Trace)
    requires IsCompleteSHA256Trace(z);
{
    forall blk ::
        0 <= blk < |z.M| ==>
        forall t:uint32 {:trigger TStep(t)} :: TStep(t) ==>
            (0 <= t <= 15 ==> z.W[blk][t] == z.M[blk][t]) &&
            (16 <= t <= 63 ==> z.W[blk][t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(z.W[blk][t-2]), z.W[blk][t-7]), SSIG0(z.W[blk][t-15])),
                                                      z.W[blk][t-16]))
}

predicate SHA256TraceHasCorrectatohs(z:SHA256Trace)
    requires IsCompleteSHA256Trace(z);
{
    forall blk :: 0 <= blk < |z.M| ==>
        ConvertAtoHToSeq(z.atoh[blk][0]) == z.H[blk] &&
        forall t:uint32 {:trigger TStep(t)} :: TStep(t) && 0 <= t <= 63 ==>
            (var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z.atoh[blk][t].h, BSIG1(z.atoh[blk][t].e)),
                                      Ch(z.atoh[blk][t].e, z.atoh[blk][t].f, z.atoh[blk][t].g)), K_SHA256(t)),
                              z.W[blk][t]);
            var T2 := BitwiseAdd32(BSIG0(z.atoh[blk][t].a), Maj(z.atoh[blk][t].a, z.atoh[blk][t].b, z.atoh[blk][t].c));
            z.atoh[blk][t+1].h == z.atoh[blk][t].g &&
            z.atoh[blk][t+1].g == z.atoh[blk][t].f &&
            z.atoh[blk][t+1].f == z.atoh[blk][t].e &&
            z.atoh[blk][t+1].e == BitwiseAdd32(z.atoh[blk][t].d, T1) &&
            z.atoh[blk][t+1].d == z.atoh[blk][t].c &&
            z.atoh[blk][t+1].c == z.atoh[blk][t].b &&
            z.atoh[blk][t+1].b == z.atoh[blk][t].a &&
            z.atoh[blk][t+1].a == BitwiseAdd32(T1, T2))
}

predicate {:autoReq} SHA256TraceIsCorrect(z:SHA256Trace)
{
    SHA256TraceHasCorrectHs(z) && SHA256TraceHasCorrectWs(z) && SHA256TraceHasCorrectatohs(z)
}

predicate DoesTraceDemonstrateSHA256(z:SHA256Trace, message:seq<uint8>, hash:seq<uint32>)
{
       IsCompleteSHA256Trace(z)
    && SHA256TraceIsCorrect(z)
    && |message| <= MaxBytesForSHA()
    && WordSeqIsProperlySHAPaddedByteSeq(ConcatenateSeqs(z.M), message)
    && hash == z.H[|z.H|-1]
}

predicate IsSHA256(message:seq<uint8>, hash:seq<uint32>)
{
    exists z:SHA256Trace :: DoesTraceDemonstrateSHA256(z, message, hash)
}

function {:axiom} SHA256(message:seq<uint8>) : seq<uint32>
    requires |message| <= MaxBytesForSHA();
    ensures  IsSHA256(message, SHA256(message));

function {:autoReq} HMAC_SHA256(key:seq<uint32>, message:seq<uint8>) : seq<uint32>
{
    SHA256(WordSeqToBytes(SeqXor(key, Opad(16)) + SHA256(WordSeqToBytes(SeqXor(key, Ipad(16))) + message)))
}

}
