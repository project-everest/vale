include "sha256.s.dfy"
include "../../lib/util/words_and_bytes.i.dfy"

module sha256_unique {

import opened sha256_s
import opened words_and_bytes_i

lemma lemma_ConvertAtoHToSeqInjective(x1:atoh_Type, x2:atoh_Type)
    requires ConvertAtoHToSeq(x1) == ConvertAtoHToSeq(x2);
    ensures  x1 == x2;
{
    var s1 := ConvertAtoHToSeq(x1);
    var s2 := ConvertAtoHToSeq(x2);
    calc { x1.a; s1[0]; s2[0]; x2.a; }
    calc { x1.b; s1[1]; s2[1]; x2.b; }
    calc { x1.c; s1[2]; s2[2]; x2.c; }
    calc { x1.d; s1[3]; s2[3]; x2.d; }
    calc { x1.e; s1[4]; s2[4]; x2.e; }
    calc { x1.f; s1[5]; s2[5]; x2.f; }
    calc { x1.g; s1[6]; s2[6]; x2.g; }
    calc { x1.h; s1[7]; s2[7]; x2.h; }
}


lemma lemma_WordSeqIsProperlySHAPaddedByteSeqUnique(ws1:seq<uint32>, ws2:seq<uint32>, bytes:seq<uint8>)
    requires WordSeqIsProperlySHAPaddedByteSeq(ws1, bytes);
    requires WordSeqIsProperlySHAPaddedByteSeq(ws2, bytes);
    ensures  ws1 == ws2;
{
    lemma_WordSeqToBytesInjective(ws1, ws2);
}

lemma lemma_ConcatenateSeqsOfSize16Unique(m1:seq<seq<uint32>>, m2:seq<seq<uint32>>)
    requires ConcatenateSeqs(m1) == ConcatenateSeqs(m2);
    requires forall s :: s in m1 ==> |s| == 16;
    requires forall s :: s in m2 ==> |s| == 16;
    ensures  m1 == m2;
{
    if |m1| == 0 || |m2| == 0 {
        return;
    }

    assert m1[0] == m2[0];
    lemma_ConcatenateSeqsOfSize16Unique(m1[1..], m2[1..]);
}

lemma lemma_IdenticalMsYieldIdenticalWsOneStep(z1:SHA256Trace, z2:SHA256Trace, blk:int, t:int)
    requires IsCompleteSHA256Trace(z1);
    requires SHA256TraceIsCorrect(z1);
    requires IsCompleteSHA256Trace(z2);
    requires SHA256TraceIsCorrect(z2);
    requires z1.M == z2.M;
    requires 0 <= blk < |z1.M|;
    requires 0 <= t <= 63;
    ensures  z1.W[blk][t] == z2.W[blk][t];
{
    assert TStep(t);

    if 0 <= t <= 15 {
        assert z1.W[blk][t] == z1.M[blk][t];
        assert z2.W[blk][t] == z2.M[blk][t];
        return;
    }

    assert z1.W[blk][t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(z1.W[blk][t-2]), z1.W[blk][t-7]), SSIG0(z1.W[blk][t-15])),
                                                      z1.W[blk][t-16]);
    assert z2.W[blk][t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(z2.W[blk][t-2]), z2.W[blk][t-7]), SSIG0(z2.W[blk][t-15])),
                                                      z2.W[blk][t-16]);

    lemma_IdenticalMsYieldIdenticalWsOneStep(z1, z2, blk, t-2);
    lemma_IdenticalMsYieldIdenticalWsOneStep(z1, z2, blk, t-7);
    lemma_IdenticalMsYieldIdenticalWsOneStep(z1, z2, blk, t-15);
    lemma_IdenticalMsYieldIdenticalWsOneStep(z1, z2, blk, t-16);
}

lemma lemma_IdenticalMsYieldIdenticalWs(z1:SHA256Trace, z2:SHA256Trace)
    requires IsCompleteSHA256Trace(z1);
    requires SHA256TraceIsCorrect(z1);
    requires IsCompleteSHA256Trace(z2);
    requires SHA256TraceIsCorrect(z2);
    requires z1.M == z2.M;
    ensures  z1.W == z2.W;
{
    forall blk | 0 <= blk < |z1.M|
        ensures z1.W[blk] == z2.W[blk];
    {
        forall t:uint32 | 0 <= t <= 63
            ensures z1.W[blk][t] == z2.W[blk][t];
        {
            lemma_IdenticalMsYieldIdenticalWsOneStep(z1, z2, blk, t);
        }
    }
}

lemma lemma_IdenticalMsYieldIdenticalatohsOneStep(z1:SHA256Trace, z2:SHA256Trace, blk:int, t:int)
    requires IsCompleteSHA256Trace(z1);
    requires SHA256TraceIsCorrect(z1);
    requires IsCompleteSHA256Trace(z2);
    requires SHA256TraceIsCorrect(z2);
    requires z1.M == z2.M;
    requires z1.W == z2.W;
    requires 0 <= blk < |z1.atoh|;
    requires 0 <= t < |z1.atoh[blk]|;
    ensures  z1.atoh[blk][t] == z2.atoh[blk][t];
    decreases blk, t+1;
{
    if t == 0 {
        lemma_IdenticalMsYieldIdenticalHsOneBlock(z1, z2, blk);
        lemma_ConvertAtoHToSeqInjective(z1.atoh[blk][0], z2.atoh[blk][0]);
        return;
    }

    assert TStep(t-1) && 0 <= t-1 <= 63;
    lemma_IdenticalMsYieldIdenticalatohsOneStep(z1, z2, blk, t-1);
}

lemma lemma_IdenticalMsYieldIdenticalatohs(z1:SHA256Trace, z2:SHA256Trace)
    requires IsCompleteSHA256Trace(z1);
    requires SHA256TraceIsCorrect(z1);
    requires IsCompleteSHA256Trace(z2);
    requires SHA256TraceIsCorrect(z2);
    requires z1.M == z2.M;
    requires z1.W == z2.W;
    ensures  z1.atoh == z2.atoh;
{
    forall blk | 0 <= blk < |z1.atoh|
        ensures z1.atoh[blk] == z2.atoh[blk]
    {
        forall t | 0 <= t < |z1.atoh[blk]|
            ensures z1.atoh[blk][t] == z2.atoh[blk][t];
        {
            lemma_IdenticalMsYieldIdenticalatohsOneStep(z1, z2, blk, t);
        }
    }
}

lemma lemma_IdenticalMsYieldIdenticalHsOneBlock(z1:SHA256Trace, z2:SHA256Trace, blk:int)
    requires IsCompleteSHA256Trace(z1);
    requires SHA256TraceIsCorrect(z1);
    requires IsCompleteSHA256Trace(z2);
    requires SHA256TraceIsCorrect(z2);
    requires z1.M == z2.M;
    requires z1.W == z2.W;
    requires 0 <= blk < |z1.H|;
    ensures  z1.H[blk] == z2.H[blk];
    decreases blk, 0;
{
    if blk == 0 {
        return;
    }

    forall j | 0 <= j < 8
        ensures z1.H[blk][j] == z2.H[blk][j];
    {
        assert TBlk(blk-1);
        assert z1.H[blk-1+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z1.atoh[blk-1][64])[j], z1.H[blk-1][j]);
        assert z2.H[blk-1+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z2.atoh[blk-1][64])[j], z2.H[blk-1][j]);
        lemma_IdenticalMsYieldIdenticalHsOneBlock(z1, z2, blk-1);
        lemma_IdenticalMsYieldIdenticalatohsOneStep(z1, z2, blk-1, 64);
    }
}

lemma lemma_IdenticalMsYieldIdenticalHs(z1:SHA256Trace, z2:SHA256Trace)
    requires IsCompleteSHA256Trace(z1);
    requires SHA256TraceIsCorrect(z1);
    requires IsCompleteSHA256Trace(z2);
    requires SHA256TraceIsCorrect(z2);
    requires z1.M == z2.M;
    requires z1.W == z2.W;
    ensures  z1.H == z2.H;
{
    forall blk | 0 <= blk < |z1.H|
        ensures z1.H[blk] == z2.H[blk]
    {
        lemma_IdenticalMsYieldIdenticalHsOneBlock(z1, z2, blk);
    }
}

lemma lemma_SHA256IsAFunction(message:seq<uint8>, hash:seq<uint32>)
    requires |message| <= MaxBytesForSHA();
    requires IsSHA256(message, hash);
    ensures  SHA256(message) == hash;
{
    var z :| DoesTraceDemonstrateSHA256(z, message, hash);
    var z' :| DoesTraceDemonstrateSHA256(z', message, SHA256(message));
    lemma_WordSeqIsProperlySHAPaddedByteSeqUnique(ConcatenateSeqs(z.M), ConcatenateSeqs(z'.M), message);
    lemma_ConcatenateSeqsOfSize16Unique(z.M, z'.M);
    lemma_IdenticalMsYieldIdenticalWs(z, z');
    lemma_IdenticalMsYieldIdenticalHs(z, z');
    lemma_IdenticalMsYieldIdenticalatohs(z, z');
    assert z == z';
}

} // end module sha256_unique
