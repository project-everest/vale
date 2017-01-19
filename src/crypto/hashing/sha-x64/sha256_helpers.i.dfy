include "../../../lib/math/mod_auto.i.dfy"
include "../sha256.i.dfy"
include "../sha256_context.i.dfy"
include "../../../lib/util/words_and_bytes.i.dfy"
include "../../../lib/collections/Seqs.s.dfy"

import opened Math__mod_auto_i_temp = Math__mod_auto_i
import opened words_and_bytes_i_temp = words_and_bytes_i

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

method DafnyMemcpy(dst:array<byte>, dst_offset:ulong, src:array<byte>, src_offset:ulong, len:ulong)
    requires allocated(dst);
    requires dst != null;
    requires allocated(src);
    requires src != null;
    requires dst != src;
    requires len >= 0;
    requires 0 <= dst_offset as int <= dst.Length - (len as int);
    requires 0 <= src_offset as int <= src.Length - (len as int);
    requires (dst_offset as int) + (len as int) <= 0x1_0000_0000_0000_0000;
    requires (src_offset as int) + (len as int) <= 0x1_0000_0000_0000_0000;
    modifies dst;
    ensures  dst[..] == old(dst[..(dst_offset as int)]) + src[(src_offset as int)..(src_offset as int)+(len as int)] + old(dst[(dst_offset as int)+(len as int)..]);
{
    ghost var old_dst := dst[..];

    var pos:ulong := 0;
    while pos < len
        invariant 0 <= pos <= len;
        invariant forall i :: 0 <= i < (pos as int) ==> dst[(dst_offset as int) + i] == src[(src_offset as int) + i];
        invariant forall i :: 0 <= i < (dst_offset as int) ==> dst[i] == old_dst[i];
        invariant forall i :: (dst_offset as int) + (len as int) <= i < dst.Length ==> dst[i] == old_dst[i];
        invariant dst[..] == old_dst[..(dst_offset as int)] + src[(src_offset as int)..(src_offset as int)+(pos as int)] + old_dst[(dst_offset as int)+(pos as int)..];
    {
        dst[dst_offset + pos] := src[src_offset + pos];
        pos := pos + 1;
    }
}

method DafnyBzero(ptr:array<byte>, offset:uint, len:uint)
    requires allocated(ptr);
    requires ptr != null;
    requires (offset as int) + (len as int) <= ptr.Length;
    requires (offset as int) + (len as int) <= 0x1_0000_0000;
    ensures  ToSeqUint8(ptr[offset..(offset as int)+(len as int)]) == RepeatByte(0, (len as int));
    ensures  forall i :: (offset as int) <= i < (offset as int) + (len as int) ==> ptr[i] == 0;
    ensures  forall i :: 0 <= i < (offset as int) ==> ptr[i] == old(ptr[i]);
    ensures  forall i :: (offset as int) + (len as int) <= i < ptr.Length ==> ptr[i] == old(ptr[i]);
    modifies ptr;
{
    ghost var old_ptr := ptr[..];

    var pos:uint := 0;
    while pos < len
        invariant 0 <= pos <= len;
        invariant ToSeqUint8(ptr[offset..(offset as int)+(pos as int)]) == RepeatByte(0, (pos as int));
        invariant forall i :: 0 <= i < (offset as int) ==> ptr[i] == old_ptr[i];
        invariant forall i :: (offset as int) <= i < (offset as int) + (pos as int) ==> ptr[i] == 0;
        invariant forall i :: (offset as int) + (pos as int) <= i < (ptr.Length as int) ==> ptr[i] == old_ptr[i];
    {
        ptr[offset + pos] := 0;
        pos := pos + 1;
    }
}

method {:timeLimitMultiplier 2} CopyUint64ToByteArray(a:array<byte>, offset:ulong, u:ulong)
    requires allocated(a);
    requires a != null;
    requires (offset as int)+8 <= a.Length;
    requires (offset as int)+8 <= 0x1_0000_0000_0000_0000;
    ensures  forall i :: 0 <= i < (offset as int) ==> a[i] == old(a[i]);
    ensures  ToSeqUint8(a[(offset as int)..(offset as int)+8]) == Uint64ToBytes(u as uint64);
    ensures  forall i :: (offset as int)+8 <= i < a.Length ==> a[i] == old(a[i]);
    modifies a;
{
    a[offset]   := ( u/ 0x100000000000000) as byte;
    a[offset+1] := ((u/   0x1000000000000) % 0x100) as byte;
    a[offset+2] := ((u/     0x10000000000) % 0x100) as byte;
    a[offset+3] := ((u/       0x100000000) % 0x100) as byte;
    a[offset+4] := ((u/         0x1000000) % 0x100) as byte;
    a[offset+5] := ((u/           0x10000) % 0x100) as byte;
    a[offset+6] := ((u/             0x100) % 0x100) as byte;
    a[offset+7] := ((u                   ) % 0x100) as byte;
    reveal_Uint64ToBytes();
}

method CopyUint32Array(dst:array<uint>, src:array<uint>, len:ulong)
    requires allocated(src);
    requires src != null;
    requires allocated(dst);
    requires dst != null;
    requires dst != src;
    requires (len as int) == dst.Length == src.Length;
    ensures  dst[..] == src[..];
    modifies dst;
{
    var pos:ulong := 0;

    while pos < len
        invariant 0 <= pos <= len;
        invariant forall i :: 0 <= i < pos ==> dst[i] == src[i];
    {
        dst[pos] := src[pos];
        pos := pos + 1;
    }
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
    ctx:SHA256Context,
    W:seq<uint32>,
    ptr:seq<uint8>,
    offset:uint64,
    atoh:atoh_Type,
    M:seq<uint32>
    ) returns (
    z':SHA256Trace
    )
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.Valid();
    requires |ctx.processed_bytes| % 64 == 0;
    requires IsCompleteSHA256Trace(ctx.z);
    requires SHA256TraceIsCorrect(ctx.z);
    requires WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
    requires ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
    requires |W| == 64;
    requires offset + 64 <= |ptr|;
    requires offset + 64 <= 0x1_0000_0000_0000_0000;
//    requires |ctx.z.M| == |ctx.z.H|-1;
    requires |M| == 16;
    requires WordSeqToBytes(M) == ptr[offset..offset+64];
    requires forall t:uint32 {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == M[t];
    requires forall t:uint32 {:trigger TStep(t)} :: TStep(t) && 16 <= t <= 63 ==> W[t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(W[t-2]), W[t-7]), SSIG0(W[t-15])), W[t-16]);
    requires atoh == atoh_c(ctx.H[0] as uint32, ctx.H[1] as uint32, ctx.H[2] as uint32, ctx.H[3] as uint32, ctx.H[4] as uint32, ctx.H[5] as uint32, ctx.H[6] as uint32, ctx.H[7] as uint32);
    ensures  z' == ctx.z.(M := ctx.z.M + [M], W := ctx.z.W + [W[..]], atoh := ctx.z.atoh + [[atoh]]);
    ensures  IsSHA256ReadyForStep(z', SHA256_state_c(ToSeqUint32(ctx.H[..]), W, atoh), 0);
{
    z' := ctx.z.(M := ctx.z.M + [M], W := ctx.z.W + [W[..]], atoh := ctx.z.atoh + [[atoh]]);

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

    assert IsSHA256ReadyForStep(z', SHA256_state_c(ToSeqUint32(ctx.H[..]), W, atoh), 0);
}

lemma lemma_SHA256DigestOneBlockHelper2(
    ctx:SHA256Context,
    W:seq<uint32>,
    atoh:atoh_Type,
    M:seq<uint32>,
    old_H:seq<uint32>
    ) returns (
    z':SHA256Trace,
    processed_bytes':seq<uint8>
    )
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.Valid();
    requires |W| == 64;
    requires |M| == 16;
    requires |ctx.z.M| == |ctx.z.H| > 0;
    requires last(ctx.z.M) == M;
    requires |ctx.processed_bytes| % 64 == 0;
    requires IsSHA256ReadyForStep(ctx.z, SHA256_state_c(old_H, W[..], atoh), 64);
    requires ctx.H[0] as uint32 == BitwiseAdd32(atoh.a, old_H[0]);
    requires ctx.H[1] as uint32 == BitwiseAdd32(atoh.b, old_H[1]);
    requires ctx.H[2] as uint32 == BitwiseAdd32(atoh.c, old_H[2]);
    requires ctx.H[3] as uint32 == BitwiseAdd32(atoh.d, old_H[3]);
    requires ctx.H[4] as uint32 == BitwiseAdd32(atoh.e, old_H[4]);
    requires ctx.H[5] as uint32 == BitwiseAdd32(atoh.f, old_H[5]);
    requires ctx.H[6] as uint32 == BitwiseAdd32(atoh.g, old_H[6]);
    requires ctx.H[7] as uint32 == BitwiseAdd32(atoh.h, old_H[7]);
    requires WordSeqToBytes(ConcatenateSeqs(ctx.z.M[..|ctx.z.H|-1])) == ctx.processed_bytes;
    ensures  z' == ctx.z.(H := ctx.z.H + [ToSeqUint32(ctx.H[..])]);
    ensures  IsCompleteSHA256Trace(z');
    ensures  SHA256TraceIsCorrect(z');
    ensures  WordSeqToBytes(ConcatenateSeqs(z'.M)) == processed_bytes';
    ensures  processed_bytes' == ctx.processed_bytes + WordSeqToBytes(M);
    ensures  |processed_bytes'| == |ctx.processed_bytes| + 64;
    ensures  |processed_bytes'| % 64 == 0;
    ensures  ToSeqUint32(ctx.H[..]) == last(z'.H);
{
    z' := ctx.z.(H := ctx.z.H + [ToSeqUint32(ctx.H[..])]);

    forall blk:int {:trigger TBlk(blk)} | TBlk(blk)
        ensures forall j :: 0 <= blk < |z'.M| && 0 <= j < 8 ==> z'.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z'.atoh[blk][64])[j], z'.H[blk][j]);
    {
        if 0 <= blk < |ctx.z.H|-1 {
            assert PartialSHA256TraceIsCorrect(ctx.z);
            assert CorrectlyAccumulatedHsForBlock(ctx.z, blk);
            forall j | 0 <= j < 8
                ensures ctx.z.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(ctx.z.atoh[blk][64])[j], ctx.z.H[blk][j]);
            {
                assert TStep(j);
            }
        }
        else if blk == |ctx.z.H|-1 {
            forall j | 0 <= j < 8
                ensures z'.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z'.atoh[blk][64])[j], z'.H[blk][j]);
            {
                assert z'.atoh[blk][64] == atoh;
                assert z'.H[blk][j] == old_H[j];
                assert z'.H[blk+1][j] == ctx.H[j] as uint32;
                ghost var atoh_seq := ConvertAtoHToSeq(atoh);
                if j == 0 { assert ctx.H[0] as uint32 == BitwiseAdd32(atoh.a, old_H[0]); }
                else if j == 1 { assert ctx.H[1] as uint32 == BitwiseAdd32(atoh.b, old_H[1]); }
                else if j == 2 { assert ctx.H[2] as uint32 == BitwiseAdd32(atoh.c, old_H[2]); }
                else if j == 3 { assert ctx.H[3] as uint32 == BitwiseAdd32(atoh.d, old_H[3]); }
                else if j == 4 { assert ctx.H[4] as uint32 == BitwiseAdd32(atoh.e, old_H[4]); }
                else if j == 5 { assert ctx.H[5] as uint32 == BitwiseAdd32(atoh.f, old_H[5]); }
                else if j == 6 { assert ctx.H[6] as uint32 == BitwiseAdd32(atoh.g, old_H[6]); }
                else if j == 7 { assert ctx.H[7] as uint32 == BitwiseAdd32(atoh.h, old_H[7]); }
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
            assert PartialSHA256TraceIsCorrect(ctx.z);
            assert TBlk(blk);
            assert z'.atoh[blk] == ctx.z.atoh[blk];
            reveal_PartialSHA256TraceHasCorrectatohsOpaque();
        }

        assert PartialSHA256TraceIsCorrect(ctx.z);
        assert PartialSHA256TraceHasCorrectatohsWf(ctx.z);
        assert TBlk(blk);
        assert |ctx.z.atoh[blk]| > 0;
        assert ConvertAtoHToSeq(ctx.z.atoh[blk][0]) == ctx.z.H[blk];
        assert ConvertAtoHToSeq(z'.atoh[blk][0]) == z'.H[blk];
    }

    processed_bytes' := ctx.processed_bytes + WordSeqToBytes(M);
    lemma_EffectOfAddingBytesOnWordSeqToBytesOfConcatenateSeqs(ctx.z.M[..|ctx.z.H|-1], ctx.processed_bytes, M, processed_bytes');
    assert ctx.z.M[..|ctx.z.H|-1] + [M] == z'.M;
    lemma_AddingMultipleOfNDoesntChangeModN(|WordSeqToBytes(M)|, |ctx.processed_bytes|, 64);
}

///////////////////////////////////
// METHOD-SPECIFIC ROUTINES
///////////////////////////////////

method {:axiom} SHA256_Compute64Steps(
    H:array<uint>,
    W:array<uint>,
    extra1:uint,
    extra2:uint,
    s1:uint,
    s2:uint,
    s3:uint,
    s4:uint,
    s5:uint,
    s6:uint,
    s7:uint,
    s8:uint,
    s9:uint,
    s10:uint,
    s11:uint,
    s12:uint,
    s13:uint,
    s14:uint,
    ghost z:SHA256Trace,
    ghost current_state:SHA256_state
    ) returns (
    ghost z':SHA256Trace,
    ghost current_state':SHA256_state
    )
    requires allocated(H);
    requires H != null;
    requires H.Length == 8;
    requires allocated(W);
    requires W != null;
    requires W.Length == 64;
    //requires current_state.W == W[..];
    requires current_state.atoh == atoh_c(H[0] as uint32, H[1] as uint32, H[2] as uint32, H[3] as uint32, H[4] as uint32, H[5] as uint32, H[6] as uint32, H[7] as uint32);
    requires IsSHA256ReadyForStep(z, current_state, 0);
    //ensures  current_state'.atoh == atoh_c(H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]);
    ensures  IsSHA256ReadyForStep(z', current_state', 64);
    ensures  current_state'.W == current_state.W;
    ensures  current_state'.H == current_state.H;
    ensures  H[0] as uint32 == BitwiseAdd32(current_state'.atoh.a, old(H[0] as uint32));
    ensures  H[1] as uint32 == BitwiseAdd32(current_state'.atoh.b, old(H[1] as uint32));
    ensures  H[2] as uint32 == BitwiseAdd32(current_state'.atoh.c, old(H[2] as uint32));
    ensures  H[3] as uint32 == BitwiseAdd32(current_state'.atoh.d, old(H[3] as uint32));
    ensures  H[4] as uint32 == BitwiseAdd32(current_state'.atoh.e, old(H[4] as uint32));
    ensures  H[5] as uint32 == BitwiseAdd32(current_state'.atoh.f, old(H[5] as uint32));
    ensures  H[6] as uint32 == BitwiseAdd32(current_state'.atoh.g, old(H[6] as uint32));
    ensures  H[7] as uint32 == BitwiseAdd32(current_state'.atoh.h, old(H[7] as uint32));
    ensures  |z'.H| == |z.H|;
    ensures  z'.M == z.M;
    modifies H; 

method {:axiom} SHA256_ComputeInitialWs(ptr:array<byte>, ptr_offset:uint, W:array<uint>, u0:uint, u1:uint, u2:uint, u3:uint)
    requires allocated(ptr);
    requires ptr != null;
    requires 0 <= ptr_offset && ptr_offset as int + 64 <= ptr.Length;
    requires allocated(W);
    requires W != null;
    requires W.Length == 64;
    ensures forall t:uint32 {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> WordToBytes(W[t] as uint32) == ToSeqUint8(ptr[(ptr_offset as int)+4*(t as int)..(ptr_offset as int) + 4*(t as int)+4]);
    ensures forall t:uint32 {:trigger TStep(t)} :: TStep(t) && 16 <= t <= 63 ==> W[t] as uint32 == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(W[t-2] as uint32), W[t-7] as uint32), SSIG0(W[t-15] as uint32)), W[t-16] as uint32);

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

method {:timeLimitMultiplier 8} SHA256_DigestOneBlock(ctx:SHA256Context, W:array<uint>, ptr:array<byte>, offset:ulong)
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.Valid();
    requires |ctx.processed_bytes| % 64 == 0;
    requires IsCompleteSHA256Trace(ctx.z);
    requires SHA256TraceIsCorrect(ctx.z);
    requires WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
    requires ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
    requires allocated(ptr);
    requires ptr != null;
    requires allocated(W);
    requires W != null;
    requires W.Length == 64;
    requires W != ctx.H;
    requires (offset as int) + 64 <= ptr.Length;
    //requires (offset as int) + 64 <= 0x1_0000_0000_0000_0000;
    requires (offset as int) + 64 <= 0x1_0000_0000;         // TODO: We need this restriction when using 32-bit Vale code
    ensures  ctx.Valid();
    ensures  IsCompleteSHA256Trace(ctx.z);
    ensures  SHA256TraceIsCorrect(ctx.z);
    ensures  ctx.H == old(ctx.H);
    ensures  ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
    ensures  ctx.unprocessed_bytes == old(ctx.unprocessed_bytes);          // UNCHANGED
    ensures  ctx.num_unprocessed_bytes == old(ctx.num_unprocessed_bytes);  // UNCHANGED
    ensures  ctx.num_total_bytes == old(ctx.num_total_bytes);              // UNCHANGED
    ensures  WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
    ensures  ctx.processed_bytes == old(ctx.processed_bytes) + ToSeqUint8(ptr[(offset as int)..(offset as int)+64]);
    ensures  |ctx.processed_bytes| == old(|ctx.processed_bytes|) + 64;
    ensures  |ctx.processed_bytes| % 64 == 0;
    modifies ctx, ctx.H, W;
{
    ghost var old_H := ToSeqUint32(ctx.H[..]);
    assert old_H == last(ctx.z.H);

    ghost var M := DafnyCastByteSeqToWordSeq(ToSeqUint8(ptr[..]), offset as int, 16);
    assert WordSeqToBytes(M[..]) == ToSeqUint8(ptr[(offset as int)..(offset as int)+64]);
    SHA256_ComputeInitialWs(ptr, offset as uint, W, 0, 1, 2, 3);
    ghost var atoh := atoh_c(ctx.H[0] as uint32, ctx.H[1] as uint32, ctx.H[2] as uint32, ctx.H[3] as uint32, ctx.H[4] as uint32, ctx.H[5] as uint32, ctx.H[6] as uint32, ctx.H[7] as uint32);
    lemma_WordSeqToBytesHelper(ToSeqUint8(ptr[..]), offset as int, 16, M, ToSeqUint32(W[..]));

    ctx.z := lemma_SHA256DigestOneBlockHelper1(ctx, ToSeqUint32(W[..]), ToSeqUint8(ptr[..]), offset as uint64, atoh, M);

    ghost var current_state';
    ctx.z, current_state' := SHA256_Compute64Steps(ctx.H, W, 
    100,101,1,2,3,4,5,6,7,8,9,10,11,12,13,14,
    ctx.z, SHA256_state_c(ToSeqUint32(ctx.H[..]), ToSeqUint32(W[..]), atoh));
    //atoh := atoh_c(ctx.H[0], ctx.H[1], ctx.H[2], ctx.H[3], ctx.H[4], ctx.H[5], ctx.H[6], ctx.H[7]);

//    atoh, ctx.z := SHA256_Compute64Steps(ctx.H[1], ctx.H[2], ctx.H[3], ctx.H[4], ctx.H[5], ctx.H[6], ctx.H[7],
//                                         ctx.H[0], W, ctx.z, SHA256_state_c(ctx.H[..], W[..], atoh));
//
//    assert IsSHA256ReadyForStep(ctx.z, SHA256_state_c(ctx.H[..], W[..], atoh), 64);
//
//    ctx.H[0], ctx.H[1], ctx.H[2], ctx.H[3], ctx.H[4], ctx.H[5], ctx.H[6], ctx.H[7] :=
//        BitwiseAdd32(atoh.a, ctx.H[0]), BitwiseAdd32(atoh.b, ctx.H[1]), BitwiseAdd32(atoh.c, ctx.H[2]),
//        BitwiseAdd32(atoh.d, ctx.H[3]), BitwiseAdd32(atoh.e, ctx.H[4]), BitwiseAdd32(atoh.f, ctx.H[5]),
//        BitwiseAdd32(atoh.g, ctx.H[6]), BitwiseAdd32(atoh.h, ctx.H[7]);

    ctx.z, ctx.processed_bytes := lemma_SHA256DigestOneBlockHelper2(ctx, ToSeqUint32(W[..]), current_state'.atoh, M, old_H);
}

method {:timeLimitMultiplier 3} SHA256_BlockDataOrder(ctx:SHA256Context, ptr:array<byte>, offset:ulong, len:ulong)
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.Valid();
    requires |ctx.processed_bytes| % 64 == 0;
    requires IsCompleteSHA256Trace(ctx.z);
    requires SHA256TraceIsCorrect(ctx.z);
    requires WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
    requires ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
    requires allocated(ptr);
    requires ptr != null;
    requires len % 64 == 0;
    requires (offset as int) + (len as int) <= ptr.Length;
    //requires (offset as int) + (len as int) <= 0x1_0000_0000_0000_0000;
    requires (offset as int) + (len as int) <= 0x1_0000_0000;  // TODO: We need this restriction when using 32-bit Vale code
    ensures  ctx.Valid();
    ensures  IsCompleteSHA256Trace(ctx.z);
    ensures  SHA256TraceIsCorrect(ctx.z);
    ensures  ctx.H == old(ctx.H);
    ensures  ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
    ensures  ctx.unprocessed_bytes == old(ctx.unprocessed_bytes);          // UNCHANGED
    ensures  ctx.num_unprocessed_bytes == old(ctx.num_unprocessed_bytes);  // UNCHANGED
    ensures  ctx.num_total_bytes == old(ctx.num_total_bytes);              // UNCHANGED
    ensures  WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
    ensures  ctx.processed_bytes == old(ctx.processed_bytes) + ToSeqUint8(ptr[(offset as int)..(offset as int)+(len as int)]);
    ensures  |ctx.processed_bytes| == old(|ctx.processed_bytes|) + (len as int);
    ensures  |ctx.processed_bytes| % 64 == 0;
    modifies ctx, ctx.H;
{
    var pos:ulong := 0;
    var W := new uint[64];

    while pos < len
        invariant 0 <= pos <= len;
        invariant allocated(W);
        invariant W != null;
        invariant W.Length == 64;
        invariant pos % 64 == 0;
        invariant (offset as int) + (pos as int) <= ptr.Length;
        invariant ctx.Valid();
        invariant ctx.processed_bytes == old(ctx.processed_bytes) + ToSeqUint8(ptr[(offset as int)..(offset as int)+(pos as int)]);
        invariant |ctx.processed_bytes| % 64 == 0;
        invariant IsCompleteSHA256Trace(ctx.z);
        invariant SHA256TraceIsCorrect(ctx.z);
        invariant WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
        invariant ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
        invariant ctx.H == old(ctx.H);
        invariant ctx.unprocessed_bytes == old(ctx.unprocessed_bytes);
        invariant ctx.num_unprocessed_bytes == old(ctx.num_unprocessed_bytes);
        invariant ctx.num_total_bytes == old(ctx.num_total_bytes);
    {
        ghost var old_pos := pos;
        ghost var old_processed_bytes := ctx.processed_bytes;

        SHA256_DigestOneBlock(ctx, W, ptr, offset + pos);
        pos := pos + 64;

        calc {
            ctx.processed_bytes;
            old_processed_bytes + ToSeqUint8(ptr[(offset + old_pos) as int..(offset + old_pos) as int + 64]);
            old(ctx.processed_bytes) + ToSeqUint8(ptr[(offset as int)..(offset as int)+(old_pos as int)]) + ToSeqUint8(ptr[(offset + old_pos) as int..(offset + old_pos) as int + 64]);
            old(ctx.processed_bytes) + ToSeqUint8(ptr[(offset as int)..(offset as int)+(old_pos as int)]) + ToSeqUint8(ptr[(offset + old_pos) as int..(offset + pos) as int]);
                { lemma_ToSeqUint8DistributesOverConcatenation(ptr[(offset as int)..(offset as int)+(old_pos as int)], ptr[(offset + old_pos) as int..(offset + pos) as int]); }
            old(ctx.processed_bytes) + ToSeqUint8(ptr[(offset as int)..(offset + pos) as int]);
        }
    }
}
