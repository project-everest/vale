include "../../lib/util/types.s.dfy"
include "sha256.i.dfy"
include "sha256_context.i.dfy"
include "sha256_helpers.i.dfy"
include "sha256_unique.i.dfy"
include "../../lib/math/mod_auto.i.dfy"
include "../../lib/math/div_nonlinear.i.dfy"
include "../../lib/math/mul.i.dfy"
include "../../lib/math/power2.i.dfy"

import opened types_s_temp = types_s
import opened Math__div_nonlinear_i_temp = Math__div_nonlinear_i
import opened Math__mul_i_temp = Math__mul_i
import opened Math__power2_i_temp = Math__power2_i
import opened sha256_unique_temp = sha256_unique

///////////////////////////////////
// GENERAL LEMMAS
///////////////////////////////////

lemma lemma_ArrayOffsetConcatenation<T>(a:seq<T>, i:int, j:int, k:int)
    requires 0 <= i <= j <= k <= |a|;
    ensures  a[i..j] + a[j..k] == a[i..k];
{
}

lemma lemma_ElementOfArraySlice<T>(a:array<T>, i:int, j:int, k:int)
    requires allocated(a);
    requires a != null;
    requires 0 <= i <= j <= a.Length;
    requires 0 <= k;
    requires i + k < j;
    ensures  a[i..j][k] == a[i+k];
{
}

lemma lemma_RepeatByteConcatenation(b:uint8, x:int, y:int)
    requires x >= 0;
    requires y >= 0;
    ensures  RepeatByte(b, x) + RepeatByte(b, y) == RepeatByte(b, x + y);
{
    if y == 0 {
        return;
    }

    lemma_RepeatByteConcatenation(b, x, y-1);
}

lemma lemma_MultiplyingByNModNIsZero(x:int, n:int)
    requires n > 0;
    ensures (x*n) % n == 0;
    ensures (n*x) % n == 0;
    decreases if x > 0 then x else -x;
{
    lemma_mod_auto(n);
    lemma_mul_is_commutative(n, x);

    if x > 0 {
        calc {
            x*n;
            (x-1+1)*n;
                { lemma_mul_is_distributive_add_other_way(n, x-1, 1); }
            (x-1)*n + 1*n;
            (x-1)*n + n;
        }
        lemma_MultiplyingByNModNIsZero(x-1, n);
    }

    if x < 0 {
        calc {
            x*n;
            (x+1-1)*n;
                { lemma_mul_is_distributive_add_other_way(n, x+1, -1); }
            (x+1)*n + (-1)*n;
            (x+1)*n - n;
        }
        lemma_MultiplyingByNModNIsZero(x+1, n);
    }
}

///////////////////////////////////
// METHOD HELPER LEMMAS
///////////////////////////////////

lemma lemma_SHA256UpdateWhenNoUnprocessedBytesHelper(
    ctx:SHA256Context,
    bytes:seq<uint8>,
    offset:uint64,
    len:uint64,
    old_bytes_included:seq<uint8>,
    num_blocks:uint64,
    num_leftover_bytes:uint32,
    num_block_bytes:uint64,
    intermediate_bytes_included:seq<uint8>
    )
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.ExportedInvariant();
    requires offset + len <= |bytes|;
    requires offset + len <= 0x1_0000_0000;   // TODO: Switch back to 2^64 when not using 32-bit Vale code
    requires num_blocks == len / 64;
    requires num_leftover_bytes == (len % 64) as int;
    requires num_block_bytes == 64 * num_blocks;
    requires intermediate_bytes_included == old_bytes_included + bytes[offset..offset+num_block_bytes];
    requires ctx.BytesIncluded() == intermediate_bytes_included + ToSeqUint8(ctx.unprocessed_bytes[..num_leftover_bytes]);
    requires ToSeqUint8(ctx.unprocessed_bytes[0..num_leftover_bytes]) == bytes[offset + num_block_bytes..offset + num_block_bytes + num_leftover_bytes];
    ensures  ctx.BytesIncluded() == old_bytes_included + bytes[offset..offset+len];
{
    lemma_fundamental_div_mod(len, 64);

    calc {
        ctx.BytesIncluded();
        intermediate_bytes_included + ToSeqUint8(ctx.unprocessed_bytes[..num_leftover_bytes]);
        intermediate_bytes_included + bytes[offset+num_block_bytes .. offset+num_block_bytes+num_leftover_bytes];
        old_bytes_included + bytes[offset..offset+num_block_bytes] + bytes[offset+num_block_bytes..offset+num_block_bytes+num_leftover_bytes];
            { lemma_SeqConcatenationIsAssociative(old_bytes_included, bytes[offset..offset+num_block_bytes], bytes[offset+num_block_bytes..offset+num_block_bytes+num_leftover_bytes]); }

        old_bytes_included + (bytes[offset..offset+num_block_bytes] + bytes[offset+num_block_bytes..offset+num_block_bytes+num_leftover_bytes]);
            { lemma_ArrayOffsetConcatenation(bytes, offset, offset+num_block_bytes, offset+num_block_bytes+num_leftover_bytes);
              assert bytes[offset..offset+num_block_bytes] + bytes[offset+num_block_bytes..offset+num_block_bytes+num_leftover_bytes] == bytes[offset..offset+num_block_bytes+num_leftover_bytes]; }
        old_bytes_included + bytes[offset..offset+num_block_bytes+num_leftover_bytes];
        old_bytes_included + bytes[offset..offset+len];
    }
}

lemma lemma_SHA256UpdateHelper(
    ctx:SHA256Context,
    bytes:seq<uint8>,
    offset:uint64,
    len:uint64,
    old_bytes:seq<uint8>,
    old_bytes_included:seq<uint8>,
    remaining_room:uint64,
    intermediate_bytes_included:seq<uint8>,
    new_offset:uint64,
    new_len:uint64
    )
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.ExportedInvariant();
    requires offset + len <= |bytes|;
    requires offset + len <= 0x1_0000_0000;   // TODO: Switch back to 2^64 when not using 32-bit Vale code
    requires 0 < remaining_room < 64;
    requires len > remaining_room;
    requires new_offset == offset + remaining_room;
    requires new_len == len - remaining_room;
    requires intermediate_bytes_included == old_bytes_included + bytes[offset..offset+remaining_room];
    requires ctx.BytesIncluded() == intermediate_bytes_included + bytes[new_offset..new_offset+new_len];
    ensures  ctx.BytesIncluded() == old_bytes_included + bytes[offset..offset+len];
{
    calc {
        ctx.BytesIncluded();
        intermediate_bytes_included + bytes[new_offset..new_offset+new_len];
        old_bytes_included + bytes[offset..offset+remaining_room] + bytes[new_offset..new_offset+new_len];
        old_bytes_included + bytes[offset..new_offset] + bytes[new_offset..new_offset+new_len];
            { lemma_SeqConcatenationIsAssociative(old_bytes_included, bytes[offset..new_offset], bytes[new_offset..new_offset+new_len]); }
        old_bytes_included + (bytes[offset..new_offset] + bytes[new_offset..new_offset+new_len]);
            { lemma_ArrayOffsetConcatenation(bytes, offset, new_offset, new_offset+new_len); }
        old_bytes_included + bytes[offset..new_offset+new_len];
            { assert new_offset + new_len == offset + len; }
        old_bytes_included + bytes[offset..offset+len];
    }
}

lemma lemma_SHA256FinalHelper1(
    ctx:SHA256Context,
    message:seq<uint8>,
    old_processed_bytes:seq<uint8>,
    old_num_unprocessed_bytes:uint32,
    old_num_total_bytes:uint64,
    message_bits:uint64
    )
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.Valid();
    requires |ctx.processed_bytes| % 64 == 0;
    requires IsCompleteSHA256Trace(ctx.z);
    requires SHA256TraceIsCorrect(ctx.z);
    requires WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
    requires ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
    requires old_num_unprocessed_bytes <= 55;
    requires ctx.processed_bytes == old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..64]);
    requires ctx.unprocessed_bytes[old_num_unprocessed_bytes] == 0x80;
    requires ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes+1..56]) == RepeatByte(0, 55 - old_num_unprocessed_bytes);
    requires ToSeqUint8(ctx.unprocessed_bytes[56..64]) == Uint64ToBytes(message_bits);
    requires message == old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[..old_num_unprocessed_bytes]);
    requires old_num_total_bytes == |old_processed_bytes| + old_num_unprocessed_bytes;
    requires |message| == old_num_total_bytes <= MaxBytesForSHA();
    requires message_bits == old_num_total_bytes * 8;
    ensures  WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == 
             message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes((|message| as uint64) * 8);
{
    calc {
        |message| % 64;
        old_num_total_bytes % 64;
        (|old_processed_bytes| + old_num_unprocessed_bytes) % 64;
            { lemma_AddingMultipleOfNDoesntChangeModN(|old_processed_bytes|, old_num_unprocessed_bytes, 64); }
        old_num_unprocessed_bytes % 64;
        old_num_unprocessed_bytes;
    }

    calc {
        55 - old_num_unprocessed_bytes;
        55 - (|message| % 64);
        (55 - (|message| % 64)) % 64;
        (119 - (|message| % 64)) % 64;
    }

    calc {
        WordSeqToBytes(ConcatenateSeqs(ctx.z.M));
        ctx.processed_bytes;
        old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..64]);
            { lemma_ArrayOffsetConcatenation(ctx.unprocessed_bytes[..], 0, old_num_unprocessed_bytes, 64); }
        old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..old_num_unprocessed_bytes]) + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes..64]);
        old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[..old_num_unprocessed_bytes]) + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes..64]);
        message + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes..64]);
            { lemma_ArrayOffsetConcatenation(ctx.unprocessed_bytes[..], old_num_unprocessed_bytes, old_num_unprocessed_bytes+1, 64); }
        message + ([0x80] + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes+1..64]));
            { lemma_SeqConcatenationIsAssociative(message, [0x80], ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes+1..64])); }
        message + [0x80] + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes+1..64]);
            { lemma_ArrayOffsetConcatenation(ctx.unprocessed_bytes[..], old_num_unprocessed_bytes+1, 56, 64); }
        message + [0x80] + (RepeatByte(0, 55 - old_num_unprocessed_bytes) + ToSeqUint8(ctx.unprocessed_bytes[56..64]));
            { lemma_SeqConcatenationIsAssociative(message + [0x80], RepeatByte(0, 55 - old_num_unprocessed_bytes), ToSeqUint8(ctx.unprocessed_bytes[56..64])); }
        message + [0x80] + RepeatByte(0, 55 - old_num_unprocessed_bytes) + ToSeqUint8(ctx.unprocessed_bytes[56..64]);
        message + [0x80] + RepeatByte(0, 55 - old_num_unprocessed_bytes) + Uint64ToBytes(old_num_total_bytes * 8);
        message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes(old_num_total_bytes * 8);
        message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes((|message| as uint64) * 8);
    }
}

lemma lemma_SHA256FinalHelper2(
    ctx:SHA256Context,
    message:seq<uint8>,
    old_processed_bytes:seq<uint8>,
    old_num_unprocessed_bytes:uint32,
    old_num_total_bytes:uint64
    )
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.Valid();
    requires |ctx.processed_bytes| % 64 == 0;
    requires IsCompleteSHA256Trace(ctx.z);
    requires SHA256TraceIsCorrect(ctx.z);
    requires WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
    requires ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
    requires 56 <= old_num_unprocessed_bytes < 64;
    requires ctx.processed_bytes == old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..64]);
    requires ctx.unprocessed_bytes[old_num_unprocessed_bytes] == 0x80;
    requires ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes+1..64]) == RepeatByte(0, 63 - old_num_unprocessed_bytes);
    requires message == old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[..old_num_unprocessed_bytes]);
    requires old_num_total_bytes == |old_processed_bytes| + old_num_unprocessed_bytes;
    requires |message| == old_num_total_bytes <= MaxBytesForSHA();
    ensures  ctx.processed_bytes == message + [0x80] + RepeatByte(0, 63 - old_num_unprocessed_bytes);
{
    calc {
        ctx.processed_bytes;
        old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..64]);
            { lemma_ArrayOffsetConcatenation(ctx.unprocessed_bytes[..], 0, old_num_unprocessed_bytes, 64); }
        old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..old_num_unprocessed_bytes]) + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes..64]);
        old_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[..old_num_unprocessed_bytes]) + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes..64]);
        message + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes..64]);
            { lemma_ArrayOffsetConcatenation(ctx.unprocessed_bytes[..], old_num_unprocessed_bytes, old_num_unprocessed_bytes+1, 64); }
        message + ([0x80] + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes+1..64]));
            { lemma_SeqConcatenationIsAssociative(message, [0x80], ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes+1..64])); }
        message + [0x80] + ToSeqUint8(ctx.unprocessed_bytes[old_num_unprocessed_bytes+1..64]);
        message + [0x80] + RepeatByte(0, 63 - old_num_unprocessed_bytes);
    }
}

lemma lemma_SHA256FinalHelper3(
    ctx:SHA256Context,
    message:seq<uint8>,
    old_processed_bytes:seq<uint8>,
    old_num_unprocessed_bytes:uint32,
    old_num_total_bytes:uint64,
    message_bits:uint64,
    intermediate_processed_bytes:seq<uint8>
    )
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.Valid();
    requires |ctx.processed_bytes| % 64 == 0;
    requires IsCompleteSHA256Trace(ctx.z);
    requires SHA256TraceIsCorrect(ctx.z);
    requires WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == ctx.processed_bytes;
    requires ToSeqUint32(ctx.H[..]) == last(ctx.z.H);
    requires 56 <= old_num_unprocessed_bytes < 64;
    requires ToSeqUint8(ctx.unprocessed_bytes[0..56]) == RepeatByte(0, 56);
    requires ToSeqUint8(ctx.unprocessed_bytes[56..64]) == Uint64ToBytes(message_bits);
    requires old_num_total_bytes == |old_processed_bytes| + old_num_unprocessed_bytes;
    requires |message| == old_num_total_bytes <= MaxBytesForSHA();
    requires message_bits == old_num_total_bytes * 8;
    requires intermediate_processed_bytes == message + [0x80] + RepeatByte(0, 63 - old_num_unprocessed_bytes);
    requires ctx.processed_bytes == intermediate_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..64]);
    ensures  WordSeqToBytes(ConcatenateSeqs(ctx.z.M)) == 
             message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes((|message| as uint64) * 8);
{
    calc {
        |message| % 64;
        old_num_total_bytes % 64;
        (|old_processed_bytes| + old_num_unprocessed_bytes) % 64;
            { lemma_AddingMultipleOfNDoesntChangeModN(|old_processed_bytes|, old_num_unprocessed_bytes, 64); }
        old_num_unprocessed_bytes % 64;
        old_num_unprocessed_bytes;
    }

    calc {
        119 - old_num_unprocessed_bytes;
        (119 - old_num_unprocessed_bytes) % 64;
        (119 - (|message| % 64)) % 64;
    }

    calc {
        WordSeqToBytes(ConcatenateSeqs(ctx.z.M));
        ctx.processed_bytes;
        intermediate_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..64]);
            { lemma_ArrayOffsetConcatenation(ctx.unprocessed_bytes[..], 0, 56, 64); }
        intermediate_processed_bytes + (ToSeqUint8(ctx.unprocessed_bytes[0..56]) + ToSeqUint8(ctx.unprocessed_bytes[56..64]));
            { lemma_SeqConcatenationIsAssociative(intermediate_processed_bytes, ToSeqUint8(ctx.unprocessed_bytes[0..56]), ToSeqUint8(ctx.unprocessed_bytes[56..64])); }
        intermediate_processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[0..56]) + ToSeqUint8(ctx.unprocessed_bytes[56..64]);
        intermediate_processed_bytes + RepeatByte(0, 56) + ToSeqUint8(ctx.unprocessed_bytes[56..64]);
        intermediate_processed_bytes + RepeatByte(0, 56) + ToSeqUint8(ctx.unprocessed_bytes[56..64]);
        message + [0x80] + RepeatByte(0, 63 - old_num_unprocessed_bytes) + RepeatByte(0, 56) + ToSeqUint8(ctx.unprocessed_bytes[56..64]);
            { lemma_SeqConcatenationIsAssociative(message + [0x80], RepeatByte(0, 63 - old_num_unprocessed_bytes), RepeatByte(0, 56)); }
        message + [0x80] + (RepeatByte(0, 63 - old_num_unprocessed_bytes) + RepeatByte(0, 56)) + ToSeqUint8(ctx.unprocessed_bytes[56..64]);
            { lemma_RepeatByteConcatenation(0, 63 - old_num_unprocessed_bytes, 56); }
        message + [0x80] + RepeatByte(0, 119 - old_num_unprocessed_bytes) + ToSeqUint8(ctx.unprocessed_bytes[56..64]);
        message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + ToSeqUint8(ctx.unprocessed_bytes[56..64]);
        message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes(old_num_total_bytes * 8);
        message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes((|message| as uint64) * 8);
    }
}

///////////////////////////////////
// METHOD-SPECIFIC ROUTINES
///////////////////////////////////

method SHA256UpdateWhenNoUnprocessedBytes(
    ctx:SHA256Context,
    bytes:array<byte>,
    offset:ulong,
    len:ulong
    )
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.ExportedInvariant();
    requires (ctx.num_total_bytes as int) + (len as int) <= MaxBytesForSHA();
    requires allocated(bytes);
    requires bytes != null;
    requires (offset as int) + (len as int) <= bytes.Length;
    requires (offset as int) + (len as int) <= 0x1_0000_0000;   // TODO: Switch back to 2^64 when not using 32-bit Vale code
    requires ctx.num_unprocessed_bytes == 0;
    requires bytes != ctx.unprocessed_bytes;
    ensures  ctx.ExportedInvariant();
    ensures  ctx.H == old(ctx.H);
    ensures  ctx.unprocessed_bytes == old(ctx.unprocessed_bytes);
    ensures  ctx.BytesIncluded() == old(ctx.BytesIncluded()) + ToSeqUint8(bytes[offset..(offset as int)+(len as int)]);
    modifies ctx.Repr;
{
    ghost var old_processed_bytes := ctx.processed_bytes;
    ghost var old_bytes_included := ctx.BytesIncluded();
    assert old_processed_bytes == old_bytes_included;

    var num_blocks := len / 64;
    var num_leftover_bytes:uint := (len % 64) as uint;
    var num_block_bytes := 64 * num_blocks;

    lemma_MultiplyingByNModNIsZero(num_blocks as int, 64);

    SHA256_BlockDataOrder(ctx, bytes, offset, num_block_bytes);

    ghost var intermediate_bytes_included := ctx.BytesIncluded();

    calc {
        intermediate_bytes_included;
        ctx.processed_bytes + ToSeqUint8(ctx.unprocessed_bytes[..ctx.num_unprocessed_bytes]);
        ctx.processed_bytes + [];
        ctx.processed_bytes;
        old_processed_bytes + ToSeqUint8(bytes[(offset as uint64)..(offset as uint64)+(num_block_bytes as uint64)]);
        old_bytes_included  + ToSeqUint8(bytes[(offset as uint64)..(offset as uint64)+(num_block_bytes as uint64)]);
        old_bytes_included  + ToSeqUint8(bytes[..])[(offset as uint64)..(offset as uint64)+(num_block_bytes as uint64)];
    }

    if num_leftover_bytes == 0 {
        assert num_block_bytes == len;
        assert (offset as int) + (num_block_bytes as int) == (offset as int) + (len as int);
        ctx.num_total_bytes := ctx.num_total_bytes + num_block_bytes;
        return;
    }

    assert num_leftover_bytes < 64;
    DafnyMemcpy(ctx.unprocessed_bytes, 0, bytes, offset + num_block_bytes, num_leftover_bytes as ulong);
    ctx.num_unprocessed_bytes := num_leftover_bytes;
    ctx.num_total_bytes := ctx.num_total_bytes + num_block_bytes + (num_leftover_bytes as ulong);

    lemma_ToSeqUint8OfSlice(bytes[..], (offset as int) + (num_block_bytes as int), (offset as int) + (num_block_bytes as int) + (num_leftover_bytes as int));

    lemma_SHA256UpdateWhenNoUnprocessedBytesHelper(ctx, ToSeqUint8(bytes[..]), offset as uint64, len as uint64, old_bytes_included, num_blocks as uint64, num_leftover_bytes as uint32, num_block_bytes as uint64, intermediate_bytes_included);
}

///////////////////////////////////
// EXPORTED_METHODS
///////////////////////////////////

method {:timeLimitMultiplier 2} SHA256_Init(ctx:SHA256Context)
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.Valid();
    ensures  ctx.ExportedInvariant();
    ensures  ctx.BytesIncluded() == [];
    ensures  ctx.Repr == old(ctx.Repr);
    modifies ctx.Repr;
{
    ctx.H[0] := 1779033703;
    ctx.H[1] := 3144134277;
    ctx.H[2] := 1013904242;
    ctx.H[3] := 2773480762;
    ctx.H[4] := 1359893119;
    ctx.H[5] := 2600822924;
    ctx.H[6] :=  528734635;
    ctx.H[7] := 1541459225;

    forall j:uint32 | 0 <= j <= 7
        ensures ctx.H[j] as uint32 == InitialH_SHA256(j);
    {
        reveal_InitialH_SHA256();
    }

    ctx.num_unprocessed_bytes := 0;
    ctx.num_total_bytes := 0;
    ctx.z := SHA256Trace_c([], [ToSeqUint32(ctx.H[..])], [], []);
    ctx.processed_bytes := [];
}

method {:timeLimitMultiplier 6} SHA256_Update(ctx:SHA256Context, bytes:array<byte>, offset:ulong, len:ulong)
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.ExportedInvariant();
    requires |ctx.BytesIncluded()| + (len as int) <= MaxBytesForSHA();
    requires allocated(bytes);
    requires bytes != null;
    requires (offset as int) + (len as int) <= bytes.Length;
    requires (offset as int) + (len as int) <= 0x1_0000_0000;   // TODO: Switch back to 2^64 when not using 32-bit Vale code
    requires bytes !in ctx.Repr;
    ensures  ctx.ExportedInvariant();
    ensures  ctx.BytesIncluded() == old(ctx.BytesIncluded()) + ToSeqUint8(bytes[offset..(offset as int)+(len as int)]);
    ensures  ctx.Repr == old(ctx.Repr);
    modifies ctx.Repr;
{
    ghost var old_bytes := bytes[..];
    ghost var old_bytes_included := ctx.BytesIncluded();

    if len == 0 {
        return;
    }

    if ctx.num_unprocessed_bytes == 0 {
        SHA256UpdateWhenNoUnprocessedBytes(ctx, bytes, offset, len);
        return;
    }

    var remaining_room:ulong := (64 - ctx.num_unprocessed_bytes) as ulong;
    if len < remaining_room {
        DafnyMemcpy(ctx.unprocessed_bytes, ctx.num_unprocessed_bytes as ulong, bytes, offset, len);
        ctx.num_unprocessed_bytes := ctx.num_unprocessed_bytes + (len as uint);
        ctx.num_total_bytes := ctx.num_total_bytes + len;
        return;
    }

    DafnyMemcpy(ctx.unprocessed_bytes, ctx.num_unprocessed_bytes as ulong, bytes, offset, remaining_room);
    SHA256_BlockDataOrder(ctx, ctx.unprocessed_bytes, 0, 64);
    ctx.num_total_bytes := ctx.num_total_bytes + remaining_room;
    ctx.num_unprocessed_bytes := 0;
    assert ctx.BytesIncluded() == old_bytes_included + ToSeqUint8(bytes[offset..(offset as int)+(remaining_room as int)]);

    if len == remaining_room {
        return;
    }

    var new_offset:ulong := offset + remaining_room;
    var new_len:ulong := len - remaining_room;

    ghost var intermediate_bytes_included := ctx.BytesIncluded();

    assert intermediate_bytes_included == old_bytes_included + ToSeqUint8(old_bytes[offset..(offset as int)+(remaining_room as int)]);
    SHA256UpdateWhenNoUnprocessedBytes(ctx, bytes, new_offset, new_len);
    assert intermediate_bytes_included == old_bytes_included + ToSeqUint8(old_bytes[offset..(offset as int)+(remaining_room as int)]);

    assert old_bytes == bytes[..];
    assert old_bytes[offset..(offset as int)+(len as int)] == bytes[offset..(offset as int)+(len as int)];
    lemma_ToSeqUint8OfSlice(old_bytes, offset as int, (offset as int) + (remaining_room as int));
    lemma_ToSeqUint8OfSlice(old_bytes, new_offset as int, (new_offset as int) + (new_len as int));

    lemma_SHA256UpdateHelper(ctx, ToSeqUint8(bytes[..]), offset as uint64, len as uint64, ToSeqUint8(old_bytes), old_bytes_included, remaining_room as uint64, intermediate_bytes_included, new_offset as uint64, new_len as uint64);

    calc {
        ctx.BytesIncluded();
        old_bytes_included + ToSeqUint8(bytes[..])[offset as uint64 .. offset as uint64 + len as uint64];
            { lemma_ToSeqUint8OfSlice(bytes[..], offset as uint64, offset as uint64 + len as uint64); }
        old_bytes_included + ToSeqUint8(bytes[..][offset as uint64 .. offset as uint64 + len as uint64]);
        old_bytes_included + ToSeqUint8(bytes[offset as uint64 .. offset as uint64 + len as uint64]);
        old(ctx.BytesIncluded()) + ToSeqUint8(bytes[offset as uint64 .. offset as uint64 + len as uint64]);
    }
}

method {:timeLimitMultiplier 6} SHA256_Final(ctx:SHA256Context, digest:array<uint>)
    requires allocated(ctx);
    requires ctx != null;
    requires ctx.ExportedInvariant();
    requires digest != null;
    requires digest !in ctx.Repr;
    requires digest.Length == 8;
    ensures  ctx.Valid();
    ensures  IsSHA256(old(ctx.BytesIncluded()), ToSeqUint32(digest[..]));
    ensures  ToSeqUint32(digest[..]) == SHA256(old(ctx.BytesIncluded()));
    ensures  ctx.Repr == old(ctx.Repr);
    modifies digest;
    modifies ctx.Repr;
{
    ghost var message := ctx.BytesIncluded();
    ghost var old_processed_bytes := ctx.processed_bytes;
    ghost var old_num_unprocessed_bytes := ctx.num_unprocessed_bytes;
    ghost var old_num_total_bytes := ctx.num_total_bytes;

    assert ctx.H in ctx.Repr;
    assert digest != ctx.H;

    var message_bits := ctx.num_total_bytes * 8;
    assert |message| == (ctx.num_total_bytes as int);

    ctx.unprocessed_bytes[ctx.num_unprocessed_bytes] := 0x80;

    if ctx.num_unprocessed_bytes <= 55 {

        DafnyBzero(ctx.unprocessed_bytes, ctx.num_unprocessed_bytes + 1, 55 - ctx.num_unprocessed_bytes);
        assert ToSeqUint8(ctx.unprocessed_bytes[ctx.num_unprocessed_bytes+1 .. 56]) == RepeatByte(0, 55 - (ctx.num_unprocessed_bytes as int));

        CopyUint64ToByteArray(ctx.unprocessed_bytes, 56, message_bits);

        SHA256_BlockDataOrder(ctx, ctx.unprocessed_bytes, 0, 64);

        lemma_SHA256FinalHelper1(ctx, message, old_processed_bytes, old_num_unprocessed_bytes as uint32, old_num_total_bytes as uint64, message_bits as uint64);

    }
    else {

        DafnyBzero(ctx.unprocessed_bytes, ctx.num_unprocessed_bytes + 1, 63 - ctx.num_unprocessed_bytes);
        assert ToSeqUint8(ctx.unprocessed_bytes[ctx.num_unprocessed_bytes+1 .. 64]) == RepeatByte(0, 63 - (ctx.num_unprocessed_bytes as int));

        SHA256_BlockDataOrder(ctx, ctx.unprocessed_bytes, 0, 64);

        ghost var intermediate_processed_bytes := ctx.processed_bytes;

        lemma_SHA256FinalHelper2(ctx, message, old_processed_bytes, old_num_unprocessed_bytes as uint32, old_num_total_bytes as uint64);

        DafnyBzero(ctx.unprocessed_bytes, 0, 56);
        CopyUint64ToByteArray(ctx.unprocessed_bytes, 56, message_bits);
        assert ToSeqUint8(ctx.unprocessed_bytes[56..64]) == Uint64ToBytes(message_bits as uint64);
        SHA256_BlockDataOrder(ctx, ctx.unprocessed_bytes, 0, 64);

        assert ToSeqUint8(ctx.unprocessed_bytes[0..56]) == RepeatByte(0, 56);

        lemma_SHA256FinalHelper3(ctx, message, old_processed_bytes, old_num_unprocessed_bytes as uint32, old_num_total_bytes as uint64, message_bits as uint64, intermediate_processed_bytes);

    }

    assert WordSeqIsProperlySHAPaddedByteSeq(ConcatenateSeqs(ctx.z.M), message);
    CopyUint32Array(digest, ctx.H, 8);
    assert ToSeqUint32(digest[..]) == last(ctx.z.H[..]);
    assert DoesTraceDemonstrateSHA256(ctx.z, message, ToSeqUint32(digest[..]));
    lemma_SHA256IsAFunction(message, ToSeqUint32(digest[..]));
}

///////////////////////////////////
// HIGH-LEVEL METHOD
///////////////////////////////////

method SHA256_Complete(bytes:array<byte>, offset:ulong, len:ulong, digest:array<uint>)
    requires allocated(digest);
    requires digest != null;
    requires digest.Length == 8;
    requires allocated(bytes);
    requires bytes != null;
    requires (offset as int) + (len as int) <= bytes.Length;
    requires (offset as int) + (len as int) <= 0x1_0000_0000;   // TODO: Switch back to MaxBytesForSHA() when not using 32-bit Vale code
    ensures  IsSHA256(ToSeqUint8(bytes[(offset as int) .. (offset as int) + (len as int)]), ToSeqUint32(digest[..]));
    ensures  ToSeqUint32(digest[..]) == SHA256(ToSeqUint8(bytes[(offset as int) .. (offset as int) + (len as int)]));
    modifies digest;
{
    var ctx:SHA256Context := new SHA256Context();
    SHA256_Init(ctx);
    SHA256_Update(ctx, bytes, offset, len);
    SHA256_Final(ctx, digest);
    lemma_SHA256IsAFunction(ToSeqUint8(bytes[(offset as int) .. (offset as int) + (len as int)]), ToSeqUint32(digest[..]));
}
