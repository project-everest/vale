include "../../lib/math/mod_auto.i.dfy"
include "sha256.i.dfy"
include "../../lib/util/types.i.dfy"
include "../../lib/util/words_and_bytes.i.dfy"
include "../../lib/collections/Seqs.s.dfy"

module sha256_helpers_i {

import opened Math__mod_auto_i
import opened types_i
import opened words_and_bytes_i
import opened sha256_i

///////////////////////////////////
// GENERAL ROUTINES
///////////////////////////////////

ghost method {:fuel BEByteSeqToInt, 5} ExtractWordFromByteSeq(bytes:seq<uint8>, offset:int) returns (word:uint32)
    requires 0 <= offset <= |bytes| - 4;
    ensures  WordToBytes(word) == bytes[offset..offset+4];
{
    word := (bytes[offset] as uint32) * 0x1000000 + (bytes[offset + 1] as uint32) * 0x10000 + (bytes[offset + 2] as uint32) * 0x100 + (bytes[offset + 3] as uint32);

    ghost var selection := [bytes[offset], bytes[offset + 1], bytes[offset + 2], bytes[offset + 3]];
    ghost var word' := BEByteSeqToInt(selection) as int;
    assert word as int == word';
    lemma_BEByteSeqToInt_bound(selection);
    assert 0 <= word' < 0x1_0000_0000;
    forall ensures word' == BytesToWord(bytes[offset], bytes[offset + 1], bytes[offset + 2], bytes[offset + 3]) as int
    {
        lemma_2toX();
        reveal_BytesToWord();
    }
    lemma_BytesToWord_WordToBytes_inverses(bytes[offset], bytes[offset + 1], bytes[offset + 2], bytes[offset + 3]);
}

ghost method DafnyCastByteSeqToWordSeq(bytes:seq<uint8>, offset:int, num_words:int) returns (words:seq<uint32>)
    requires 0 <= offset && 0 <= num_words;
    requires offset + num_words * 4 <= |bytes|;
    ensures  |words| == num_words;
    ensures  WordSeqToBytes(words[..]) == bytes[offset..offset+num_words*4];
{
    words := [];
    var j := 0;
    while j < num_words 
        invariant 0 <= j <= num_words;
        invariant |words| == j;
        invariant WordSeqToBytes(words[..]) == bytes[offset..offset+j*4];
    {
        var i := offset + j*4;
        var word := ExtractWordFromByteSeq(bytes, i);
        var old_words := words;
        var old_j := j;
        words := words + [word];
        j := j + 1;

        calc {
            WordSeqToBytes(words);
            WordSeqToBytes(old_words + [word]);
              { lemma_WordSeqToBytes_Adds(old_words, [word]); }
            WordSeqToBytes(old_words) + WordSeqToBytes([word]);
            bytes[offset..offset+old_j*4] + bytes[offset + old_j*4..offset + old_j*4 + 4];
            bytes[offset..offset+old_j*4] + bytes[offset + old_j*4..offset + j*4];
            bytes[offset..offset + j*4];
        }
    }
}

///////////////////////////////////
// GENERAL LEMMAS
///////////////////////////////////

function all_but_last<T>(s:seq<T>) : seq<T>
    requires |s| > 0;
{
    s[..|s|-1]
}

lemma lemma_SeqConcatenationIsAssociative<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>)
    ensures (s1 + s2) + s3 == s1 + (s2 + s3);
{
}

lemma lemma_WordSeqToBytesDistributesOverSeqConcatenation(ws1:seq<uint32>, ws2:seq<uint32>)
    ensures WordSeqToBytes(ws1) + WordSeqToBytes(ws2) == WordSeqToBytes(ws1 + ws2);
{
    if |ws1| == 0 {
        return;
    }

    calc {
        WordSeqToBytes(ws1 + ws2);
        WordToBytes(ws1[0]) + WordSeqToBytes((ws1 + ws2)[1..]);
           { assert (ws1 + ws2)[1..] == ws1[1..] + ws2; }
        WordToBytes(ws1[0]) + WordSeqToBytes(ws1[1..] + ws2);
           { lemma_WordSeqToBytesDistributesOverSeqConcatenation(ws1[1..], ws2); }
        WordToBytes(ws1[0]) + (WordSeqToBytes(ws1[1..]) + WordSeqToBytes(ws2));
           { lemma_SeqConcatenationIsAssociative(WordToBytes(ws1[0]), WordSeqToBytes(ws1[1..]), WordSeqToBytes(ws2)); }
        (WordToBytes(ws1[0]) + WordSeqToBytes(ws1[1..])) + WordSeqToBytes(ws2);
        WordSeqToBytes(ws1) + WordSeqToBytes(ws2);
    }
}

lemma lemma_ReverseConcatenateSeqs<T>(ss:seq<seq<T>>)
    requires |ss| > 0;
    ensures  ConcatenateSeqs(ss) == ConcatenateSeqs(all_but_last(ss)) + last(ss);
{
    var ss' := ss[1..];
    if |ss'| == 0 {
        return;
    }

    calc {
        ConcatenateSeqs(ss);
        ss[0] + ConcatenateSeqs(ss[1..]);
        ss[0] + ConcatenateSeqs(ss');
            { lemma_ReverseConcatenateSeqs(ss'); }
        ss[0] + (ConcatenateSeqs(all_but_last(ss')) + last(ss'));
            { lemma_SeqConcatenationIsAssociative(ss[0], ConcatenateSeqs(all_but_last(ss')), last(ss')); }
        (ss[0] + ConcatenateSeqs(all_but_last(ss'))) + last(ss');
            { assert all_but_last(ss)[0] == ss[0]; assert all_but_last(ss)[1..] == all_but_last(ss'); }
        ConcatenateSeqs(all_but_last(ss)) + last(ss');
        ConcatenateSeqs(all_but_last(ss)) + last(ss);
    }
}

lemma lemma_EffectOfAddingBytesOnWordSeqToBytesOfConcatenateSeqs(
    word_seqs:seq<seq<uint32>>,
    bytes:seq<uint8>,
    words:seq<uint32>,
    bytes':seq<uint8>
    )
    requires WordSeqToBytes(ConcatenateSeqs(word_seqs)) == bytes;
    requires bytes' == bytes + WordSeqToBytes(words);
    ensures  WordSeqToBytes(ConcatenateSeqs(word_seqs + [words])) == bytes';
{
    var word_seqs' := word_seqs + [words];

    calc {
        WordSeqToBytes(ConcatenateSeqs(word_seqs + [words]));
            { lemma_ReverseConcatenateSeqs(word_seqs'); }
        WordSeqToBytes(ConcatenateSeqs(word_seqs) + words);
            { lemma_WordSeqToBytesDistributesOverSeqConcatenation(ConcatenateSeqs(word_seqs), words); }
        WordSeqToBytes(ConcatenateSeqs(word_seqs)) + WordSeqToBytes(words);
        bytes + WordSeqToBytes(words);
        bytes';
    }
}

lemma lemma_AddingMultipleOfNDoesntChangeModN(x:int, y:int, n:int)
    requires n > 0;
    requires x % n == 0;
    ensures  (x+y) % n == y % n;
{
    lemma_mod_auto_induction(n, y, imap i :: (x+i) % n == i % n);
}

///////////////////////////////////
// METHOD-SPECIFIC LEMMAS
///////////////////////////////////

lemma lemma_SHA256DigestOneBlockHelper1(
    z:SHA256Trace,
    W:seq<uint32>,
    atoh:atoh_Type,
    M:seq<uint32>
    ) returns (
    z':SHA256Trace
    )
    requires IsCompleteSHA256Trace(z);
    requires SHA256TraceIsCorrect(z);
    requires |W| == 64;
    requires |M| == 16;
    requires forall t:uint32 {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == M[t];
    requires forall t:uint32 {:trigger TStep(t)} :: TStep(t) && 16 <= t <= 63 ==> W[t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(W[t-2]), W[t-7]), SSIG0(W[t-15])), W[t-16]);
    requires atoh == atoh_c(last(z.H)[0], last(z.H)[1], last(z.H)[2], last(z.H)[3], 
                            last(z.H)[4], last(z.H)[5], last(z.H)[6], last(z.H)[7]);
    ensures  z' == z.(M := z.M + [M], W := z.W + [W], atoh := z.atoh + [[atoh]]);
    ensures  IsSHA256TraceReadyForStep(z', 0);
{
    z' := z.(M := z.M + [M], W := z.W + [W[..]], atoh := z.atoh + [[atoh]]);

    forall blk {:trigger CorrectlyAccumulatedHsForBlock(z', blk)} | 0 <= blk < |z'.H|-1
        ensures |z'.atoh[blk]| == 65;
        ensures CorrectlyAccumulatedHsForBlock(z', blk);
    {
        assert TBlk(blk);
    }
    assert CorrectlyAccumulatedHsForAllBlocks(z');

    forall blk:int {:trigger TBlk(blk)} | 0 <= blk < |z'.atoh|
        ensures |z'.atoh[blk]| <= 65;
        ensures |z'.W[blk]| == 64;
        ensures (|z'.atoh[blk]| > 0 ==> |z'.H[blk]| == 8 && ConvertAtoHToSeq(z'.atoh[blk][0]) == z'.H[blk]);
    {
    }
    assert PartialSHA256TraceHasCorrectatohsWf(z');

    forall blk {:trigger z'.W[blk]} {:trigger z'.M[blk]} | 0 <= blk < |z'.W|
        ensures |z'.W[blk]| == 64;
        ensures |z'.M[blk]| == 16;
        ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 64 ==>
                     (0 <= t <= 15 ==> z'.W[blk][t] == z'.M[blk][t])
                     && (16 <= t <= 63 ==> z'.W[blk][t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(z'.W[blk][t-2]), z'.W[blk][t-7]), SSIG0(z'.W[blk][t-15])), z'.W[blk][t-16]));
    {
        assert TBlk(blk);
    }
    assert PartialSHA256TraceHasCorrectWs(z');

    reveal_PartialSHA256TraceHasCorrectatohsOpaque();

    assert IsSHA256TraceReadyForStep(z', 0);
}

lemma lemma_SHA256DigestOneBlockHelper2(
    z:SHA256Trace,
    old_H:seq<uint32>,
    H:seq<uint32>
    ) returns (
    z':SHA256Trace//,
    //processed_bytes':seq<uint8>
    )
    requires |H| == |old_H| == 8;
    requires |z.M| == |z.H| > 0;
    requires last(z.H) == old_H;
    requires IsSHA256TraceReadyForStep(z, 64);
    requires H[0] == BitwiseAdd32(last(last(z.atoh)).a, old_H[0]);
    requires H[1] == BitwiseAdd32(last(last(z.atoh)).b, old_H[1]);
    requires H[2] == BitwiseAdd32(last(last(z.atoh)).c, old_H[2]);
    requires H[3] == BitwiseAdd32(last(last(z.atoh)).d, old_H[3]);
    requires H[4] == BitwiseAdd32(last(last(z.atoh)).e, old_H[4]);
    requires H[5] == BitwiseAdd32(last(last(z.atoh)).f, old_H[5]);
    requires H[6] == BitwiseAdd32(last(last(z.atoh)).g, old_H[6]);
    requires H[7] == BitwiseAdd32(last(last(z.atoh)).h, old_H[7]);
    ensures  z' == z.(H := z.H + [H]);
    ensures  IsCompleteSHA256Trace(z');
    ensures  SHA256TraceIsCorrect(z');
{
    z' := z.(H := z.H + [H]);
    var atoh := last(last(z.atoh));

    forall blk:int {:trigger TBlk(blk)} | TBlk(blk)
        ensures forall j :: 0 <= blk < |z'.M| && 0 <= j < 8 ==> z'.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z'.atoh[blk][64])[j], z'.H[blk][j]);
    {
        if 0 <= blk < |z.H|-1 {
            assert PartialSHA256TraceIsCorrect(z);
            assert CorrectlyAccumulatedHsForBlock(z, blk);
            forall j | 0 <= j < 8
                ensures z.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z.atoh[blk][64])[j], z.H[blk][j]);
            {
                assert TStep(j);
            }
        }
        else if blk == |z.H|-1 {
            forall j | 0 <= j < 8
                ensures z'.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z'.atoh[blk][64])[j], z'.H[blk][j]);
            {
                assert z'.atoh[blk][64] == atoh;
                assert z'.H[blk][j] == old_H[j];
                assert z'.H[blk+1][j] == H[j] as uint32;
                ghost var atoh_seq := ConvertAtoHToSeq(atoh);
                     if j == 0 { assert H[0] == BitwiseAdd32(atoh.a, old_H[0]); }
                else if j == 1 { assert H[1] == BitwiseAdd32(atoh.b, old_H[1]); }
                else if j == 2 { assert H[2] == BitwiseAdd32(atoh.c, old_H[2]); }
                else if j == 3 { assert H[3] == BitwiseAdd32(atoh.d, old_H[3]); }
                else if j == 4 { assert H[4] == BitwiseAdd32(atoh.e, old_H[4]); }
                else if j == 5 { assert H[5] == BitwiseAdd32(atoh.f, old_H[5]); }
                else if j == 6 { assert H[6] == BitwiseAdd32(atoh.g, old_H[6]); }
                else if j == 7 { assert H[7] == BitwiseAdd32(atoh.h, old_H[7]); }
            }
        }
    }

    forall blk | 0 <= blk < |z'.M|
        ensures ConvertAtoHToSeq(z'.atoh[blk][0]) == z'.H[blk];
        ensures forall t:uint32 {:trigger TStep(t)} :: TStep(t) && 0 <= t <= 63 ==>
            (var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z'.atoh[blk][t].h, BSIG1(z'.atoh[blk][t].e)),
                                      Ch(z'.atoh[blk][t].e, z'.atoh[blk][t].f, z'.atoh[blk][t].g)), K_SHA256(t)),
                              z'.W[blk][t]);
            var T2 := BitwiseAdd32(BSIG0(z'.atoh[blk][t].a), Maj(z'.atoh[blk][t].a, z'.atoh[blk][t].b, z'.atoh[blk][t].c));
            z'.atoh[blk][t+1].h == z'.atoh[blk][t].g &&
            z'.atoh[blk][t+1].g == z'.atoh[blk][t].f &&
            z'.atoh[blk][t+1].f == z'.atoh[blk][t].e &&
            z'.atoh[blk][t+1].e == BitwiseAdd32(z'.atoh[blk][t].d, T1) &&
            z'.atoh[blk][t+1].d == z'.atoh[blk][t].c &&
            z'.atoh[blk][t+1].c == z'.atoh[blk][t].b &&
            z'.atoh[blk][t+1].b == z'.atoh[blk][t].a &&
            z'.atoh[blk][t+1].a == BitwiseAdd32(T1, T2))
    {
        forall t:uint32 {:trigger TStep(t)}
            ensures TStep(t) && 0 <= t <= 63 ==>
                (var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z'.atoh[blk][t].h, BSIG1(z'.atoh[blk][t].e)),
                                          Ch(z'.atoh[blk][t].e, z'.atoh[blk][t].f, z'.atoh[blk][t].g)), K_SHA256(t)),
                                  z'.W[blk][t]);
                var T2 := BitwiseAdd32(BSIG0(z'.atoh[blk][t].a), Maj(z'.atoh[blk][t].a, z'.atoh[blk][t].b, z'.atoh[blk][t].c));
                z'.atoh[blk][t+1].h == z'.atoh[blk][t].g &&
                z'.atoh[blk][t+1].g == z'.atoh[blk][t].f &&
                z'.atoh[blk][t+1].f == z'.atoh[blk][t].e &&
                z'.atoh[blk][t+1].e == BitwiseAdd32(z'.atoh[blk][t].d, T1) &&
                z'.atoh[blk][t+1].d == z'.atoh[blk][t].c &&
                z'.atoh[blk][t+1].c == z'.atoh[blk][t].b &&
                z'.atoh[blk][t+1].b == z'.atoh[blk][t].a &&
                z'.atoh[blk][t+1].a == BitwiseAdd32(T1, T2));
        {
            assert PartialSHA256TraceIsCorrect(z);
            assert TBlk(blk);
            assert z'.atoh[blk] == z.atoh[blk];
            reveal_PartialSHA256TraceHasCorrectatohsOpaque();
        }

        assert PartialSHA256TraceIsCorrect(z);
        assert PartialSHA256TraceHasCorrectatohsWf(z);
        assert TBlk(blk);
        assert |z.atoh[blk]| > 0;
        assert ConvertAtoHToSeq(z.atoh[blk][0]) == z.H[blk];
        assert ConvertAtoHToSeq(z'.atoh[blk][0]) == z'.H[blk];
    }
}

lemma lemma_WordSeqToBytesHelper(bytes:seq<uint8>, offset:int, num_words:int, M:seq<uint32>, W:seq<uint32>)
    requires 0 <= offset && 0 <= num_words && offset + num_words*4 <= |bytes|;
    requires |W| >= 16;
    requires num_words == 16;
    requires WordSeqToBytes(M) == bytes[offset..offset+num_words*4];
    requires forall t:uint32 :: TStep(t) && 0 <= t < 16 ==> WordToBytes(W[t]) == bytes[offset+4*t..offset + 4*t+4];
    ensures  forall t :: 0 <= t < 16 ==> M[t] == W[t];
{
   forall t | 0 <= t < 16
       ensures M[t] == W[t];
   {
        calc {
            WordToBytes(M[t]);
                { lemma_WordSeqToBytes_indexed(M); }
            WordSeqToBytes(M)[t*4..(t+1)*4];
            bytes[offset..offset+num_words*4][t*4..(t+1)*4];
            bytes[offset..offset+num_words*4][t*4..4*t+4];
                { lemma_SeqSliceOfSlice(bytes, offset, offset+num_words*4, t*4, 4*t+4); }
            bytes[offset+4*t..offset + 4*t+4];
            WordToBytes(W[t]);
        }
        lemma_WordToBytes_injective(M[t], W[t]);
   }
}

}
