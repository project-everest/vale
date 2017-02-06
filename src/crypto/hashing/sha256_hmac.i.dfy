include "../../lib/util/operations.i.dfy"
include "../../lib/math/mul_nonlinear.i.dfy"
include "sha256_main.i.dfy"

import opened operations_i_temp = operations_i
import opened Math__mul_nonlinear_i_temp = Math__mul_nonlinear_i

lemma lemma_XorKeyIntoByteArrayHelper(key:seq<uint>, bytes:seq<byte>, value:uint)
    requires |key| <= 16;
    requires |bytes| == |key| * 4;
    requires forall j :: 0 <= j < |key| ==> BEByteSeqToInt(ToSeqUint8(bytes[4*j..4*j+4])) == BitwiseXor(key[j] as uint32, value as uint32) as int;
    ensures  ToSeqUint8(bytes) == WordSeqToBytes(SeqXor(ToSeqUint32(key), RepeatValue<uint32>(value as uint32, |key|)));
{
    if |key| == 0 {
        return;
    }

    calc {
        SeqXor(ToSeqUint32(key), RepeatValue<uint32>(value as uint32, |key|))[1..];
            { reveal_SeqXor(); }
        SeqXor(ToSeqUint32(key)[1..], RepeatValue<uint32>(value as uint32, |key|)[1..]);
            { lemma_RepeatValueTail<uint32>(value as uint32, |key|); }
        SeqXor(ToSeqUint32(key)[1..], RepeatValue<uint32>(value as uint32, |key|-1));
            { lemma_ToSeqUint32OfSlice(key, 1, |key|); }
        SeqXor(ToSeqUint32(key[1..]), RepeatValue<uint32>(value as uint32, |key|-1));
    }

    var key' := key[1..];
    var bytes' := bytes[4..];
    forall j | 0 <= j < |key'|
        ensures BEByteSeqToInt(ToSeqUint8(bytes'[4*j..4*j+4])) == BitwiseXor(key'[j] as uint32, value as uint32) as int;
    {
        calc {
            bytes'[4*j..4*j+4];
                { assert(true); }
            bytes[4*j+4..4*j+8];
                { lemma_mul_is_distributive_add(4, j, 1); assert 4*(j+1) == 4*j + 4*1 == 4*j + 4; }
            bytes[4*(j+1)..4*(j+1)+4];
        }
        assert key'[j] == key[j+1];
    }

    calc {
        ToSeqUint8([bytes[0], bytes[1], bytes[2], bytes[3]]);
        [bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8];
    }

    calc {
        WordSeqToBytes(SeqXor(ToSeqUint32(key), RepeatValue<uint32>(value as uint32, |key|)));
        WordToBytes(SeqXor(ToSeqUint32(key), RepeatValue<uint32>(value as uint32, |key|))[0]) + WordSeqToBytes(SeqXor(ToSeqUint32(key), RepeatValue<uint32>(value as uint32, |key|))[1..]);
        WordToBytes(SeqXor(ToSeqUint32(key), RepeatValue<uint32>(value as uint32, |key|))[0]) + WordSeqToBytes(SeqXor(ToSeqUint32(key'), RepeatValue<uint32>(value as uint32, |key|-1)));
            { lemma_XorKeyIntoByteArrayHelper(key', bytes', value); }
        WordToBytes(SeqXor(ToSeqUint32(key), RepeatValue<uint32>(value as uint32, |key|))[0]) + ToSeqUint8(bytes');
            { reveal_SeqXor(); }
        WordToBytes(BitwiseXor(ToSeqUint32(key)[0], RepeatValue<uint32>(value as uint32, |key|)[0])) + ToSeqUint8(bytes');
        WordToBytes(BitwiseXor(key[0] as uint32, RepeatValue<uint32>(value as uint32, |key|)[0])) + ToSeqUint8(bytes');
            { assert RepeatValue<uint32>(value as uint32, |key|)[0] in RepeatValue<uint32>(value as uint32, |key|); }
        WordToBytes(BitwiseXor(key[0] as uint32, value as uint32)) + ToSeqUint8(bytes');
        WordToBytes(BEByteSeqToInt(ToSeqUint8(bytes[4*0..4*0+4]))) + ToSeqUint8(bytes');
        WordToBytes(BEByteSeqToInt(ToSeqUint8(bytes[0..4]))) + ToSeqUint8(bytes');
            { assert bytes[0..4] == [bytes[0], bytes[1], bytes[2], bytes[3]]; }
        WordToBytes(BEByteSeqToInt(ToSeqUint8([bytes[0], bytes[1], bytes[2], bytes[3]]))) + ToSeqUint8(bytes');
        WordToBytes(BEByteSeqToInt([bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8])) + ToSeqUint8(bytes');
            { reveal_BytesToWord(); }
        WordToBytes(BytesToWord(bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8)) + ToSeqUint8(bytes');
            { lemma_BytesToWord_WordToBytes_inverses(bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8); }
        [bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8] + ToSeqUint8(bytes');
        ToSeqUint8([bytes[0], bytes[1], bytes[2], bytes[3]]) + ToSeqUint8(bytes');
        ToSeqUint8(bytes);
    }
}

lemma lemma_CopyWordToByteArrayHelper(words:seq<uint>, bytes:seq<byte>)
    requires |bytes| == |words| * 4;
    requires forall j :: 0 <= j < |words| ==> BEByteSeqToInt(ToSeqUint8(bytes[4*j..4*j+4])) == words[j] as int;
    ensures  ToSeqUint8(bytes) == WordSeqToBytes(ToSeqUint32(words));
{
    if |words| == 0 {
        return;
    }

    var words' := words[1..];
    var bytes' := bytes[4..];
    forall j | 0 <= j < |words'|
        ensures BEByteSeqToInt(ToSeqUint8(bytes'[4*j..4*j+4])) == words'[j] as int;
    {
        assert bytes'[4*j..4*j+4] == bytes[4*(j+1)..4*(j+1)+4];
        assert words'[j] == words[j+1];
    }

    calc {
        ToSeqUint8([bytes[0], bytes[1], bytes[2], bytes[3]]);
        [bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8];
    }

    calc {
        WordSeqToBytes(ToSeqUint32(words));
        WordToBytes(ToSeqUint32(words)[0]) + WordSeqToBytes(ToSeqUint32(words)[1..]);
            { reveal_ToSeqUint32(); }
        WordToBytes(ToSeqUint32(words)[0]) + WordSeqToBytes(ToSeqUint32(words[1..]));
            { lemma_CopyWordToByteArrayHelper(words', bytes'); }
        WordToBytes(ToSeqUint32(words)[0]) + ToSeqUint8(bytes');
        WordToBytes(words[0] as uint32) + ToSeqUint8(bytes');
        WordToBytes(BEByteSeqToInt(ToSeqUint8(bytes[4*0..4*0+4]))) + ToSeqUint8(bytes');
        WordToBytes(BEByteSeqToInt(ToSeqUint8(bytes[0..4]))) + ToSeqUint8(bytes');
            { assert bytes[0..4] == [bytes[0], bytes[1], bytes[2], bytes[3]]; }
        WordToBytes(BEByteSeqToInt(ToSeqUint8([bytes[0], bytes[1], bytes[2], bytes[3]]))) + ToSeqUint8(bytes');
        WordToBytes(BEByteSeqToInt([bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8])) + ToSeqUint8(bytes');
            { reveal_BytesToWord(); }
        WordToBytes(BytesToWord(bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8)) + ToSeqUint8(bytes');
            { lemma_BytesToWord_WordToBytes_inverses(bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8); }
        [bytes[0] as uint8, bytes[1] as uint8, bytes[2] as uint8, bytes[3] as uint8] + ToSeqUint8(bytes');
        ToSeqUint8([bytes[0], bytes[1], bytes[2], bytes[3]]) + ToSeqUint8(bytes');
        ToSeqUint8(bytes);
    }
}

lemma {:timeLimitMultiplier 2} lemma_BreakdownOfUint(word:uint)
    ensures word as int == ((((word / 0x1000000) as int) * 256 + ((word / 0x10000) % 0x100) as int) * 256 + ((word / 0x100) % 0x100) as int) * 256 + ((word % 0x100) as int);
{
    var w := word as int;
    assert 0 <= w < 0x1_0000_0000;
    assert w == (((w / 0x1000000) * 256 + (w / 0x10000) % 0x100) * 256 + (w / 0x100) % 0x100) * 256 + (w % 0x100);
}

method {:timeLimitMultiplier 3} CopyWordToByteArray(word:uint, bytes:array<byte>, pos:uint)
    requires allocated(bytes);
    requires bytes != null;
    requires (pos as int) + 4 <= bytes.Length;
    modifies bytes;
    ensures  forall i :: 0 <= i < (pos as int) || (pos as int) + 4 <= i < bytes.Length ==> bytes[i] == old(bytes[i]);
    ensures  BEByteSeqToInt(ToSeqUint8(bytes[pos as int .. (pos as int) + 4])) == word as int;
{
    bytes[pos], bytes[pos as int+1], bytes[pos as int+2], bytes[pos as int+3] := (word / 0x1000000) as byte, ((word / 0x10000) % 0x100) as byte, ((word / 0x100) % 0x100) as byte, (word % 0x100) as byte;
    ghost var bs := bytes[pos..pos as int+4];
    ghost var u8s := ToSeqUint8(bs);
    ghost var i := pos as int;

    calc {
        u8s;
            { reveal_ToSeqUint8(); }
        [u8s[0] as uint8, u8s[1] as uint8, u8s[2] as uint8, u8s[3] as uint8];
        [bs[0] as uint8, bs[1] as uint8, bs[2] as uint8, bs[3] as uint8];
        [bytes[i] as uint8, bytes[i+1] as uint8, bytes[i+2] as uint8, bytes[i+3] as uint8];
    }
    calc {
        BEByteSeqToInt(u8s);
        BEByteSeqToInt(u8s[..3]) * 256 + (u8s[3] as int);
        (BEByteSeqToInt(u8s[..3][..2]) * 256 + u8s[..3][2] as int) * 256 + (u8s[3] as int);
        (BEByteSeqToInt(u8s[..2]) * 256 + u8s[2] as int) * 256 + (u8s[3] as int);
        ((BEByteSeqToInt(u8s[..2][..1]) * 256 + u8s[..2][1] as int) * 256 + u8s[2] as int) * 256 + (u8s[3] as int);
        ((BEByteSeqToInt(u8s[..1]) * 256 + u8s[1] as int) * 256 + u8s[2] as int) * 256 + (u8s[3] as int);
        (((BEByteSeqToInt(u8s[..1][..0]) * 256 + u8s[..1][0] as int) * 256 + u8s[1] as int) * 256 + u8s[2] as int) * 256 + (u8s[3] as int);
        (((BEByteSeqToInt([]) * 256 + u8s[0] as int) * 256 + u8s[1] as int) * 256 + u8s[2] as int) * 256 + (u8s[3] as int);
        (((u8s[0] as int) * 256 + u8s[1] as int) * 256 + u8s[2] as int) * 256 + (u8s[3] as int);
        (((bytes[i] as int) * 256 + bytes[i+1] as int) * 256 + bytes[i+2] as int) * 256 + (bytes[i+3] as int);
        ((((word / 0x1000000) as int) * 256 + ((word / 0x10000) % 0x100) as int) * 256 + ((word / 0x100) % 0x100) as int) * 256 + ((word % 0x100) as int);
            { lemma_BreakdownOfUint(word); }
        word as int;
    }
}

method XorKeyIntoByteArray(key:array<uint>, bytes:array<byte>, value:uint)
    requires allocated(key);
    requires key != null;
    requires key.Length == 16;
    requires allocated(bytes);
    requires bytes != null;
    requires bytes.Length >= 64;
    modifies bytes;
    ensures  ToSeqUint8(bytes[..64]) == WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), RepeatValue<uint32>(value as int, 16)));
{
    var pos:uint := 0;

    while pos < 16
        invariant 0 <= pos <= 16;
        invariant forall j :: 0 <= j < pos ==> BEByteSeqToInt(ToSeqUint8(bytes[4*j..4*j+4])) == BitwiseXor(key[j] as uint32, value as uint32) as int;
    {
        ghost var old_bytes := bytes[..];
        var xor_result:uint := ComputeBitwiseXor(key[pos], value);
        CopyWordToByteArray(xor_result, bytes, 4*pos);
        assert BEByteSeqToInt(ToSeqUint8(bytes[4*pos..4*pos+4])) == BitwiseXor(key[pos] as uint32, value as uint32) as int;
        forall j | 0 <= j < pos + 1
            ensures BEByteSeqToInt(ToSeqUint8(bytes[4*j..4*j+4])) == BitwiseXor(key[j] as uint32, value as uint32) as int;
        {
            if j < pos {
                assert bytes[4*j..4*j+4] == old_bytes[4*j..4*j+4];
            }
        }
        pos := pos + 1;
    }

    var bytes' := bytes[..64];
    forall j | 0 <= j < 16
        ensures BEByteSeqToInt(ToSeqUint8(bytes'[4*j..4*j+4])) == BitwiseXor(key[j] as uint32, value as uint32) as int;
    {
        assert bytes'[4*j..4*j+4] == bytes[4*j..4*j+4];
    }

    lemma_XorKeyIntoByteArrayHelper(key[..], bytes', value);
}

lemma lemma_SequenceExtensionality<T>(s1:seq<T>, s2:seq<T>)
    requires |s1| == |s2|;
    requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i];
    ensures  s1 == s2;
{
}

method CopyWordSeqIntoByteArray(
    words:array<uint>,
    words_offset:uint,
    words_len:uint,
    bytes:array<byte>,
    bytes_offset:uint,
    bytes_len:uint
    )
    requires allocated(words);
    requires words != null;
    requires words_offset as int + words_len as int <= 0x1_0000_0000;
    requires words_offset as int + words_len as int <= words.Length;
    requires allocated(bytes);
    requires bytes != null;
    requires bytes_offset as int + bytes_len as int <= 0x1_0000_0000;
    requires bytes_offset as int + bytes_len as int <= bytes.Length;
    requires bytes_len as int == (words_len as int) * 4;
    modifies bytes;
    ensures  forall j :: 0 <= j < bytes_offset as int || bytes_offset as int + bytes_len as int <= j < bytes.Length ==> bytes[j] == old(bytes[j]);
    ensures  ToSeqUint8(bytes[bytes_offset as int .. bytes_offset as int + bytes_len as int]) ==
                 WordSeqToBytes(ToSeqUint32(words[words_offset as int .. words_offset as int + words_len as int]));
{
    var pos:uint := 0;

    while pos < words_len
        invariant 0 <= pos <= words_len;
        invariant forall j :: 0 <= j < bytes_offset as int || bytes_offset as int + bytes_len as int <= j < bytes.Length ==> bytes[j] == old(bytes[j]);
        invariant forall j :: 0 <= j < pos as int ==> BEByteSeqToInt(ToSeqUint8(bytes[bytes_offset as int + 4*j .. bytes_offset as int + 4*j+4])) == words[words_offset as int + j] as int;
    {
        ghost var old_bytes := bytes[..];
        var value := words[words_offset as int + pos as int];
        CopyWordToByteArray(value, bytes, bytes_offset + 4*pos);
        assert BEByteSeqToInt(ToSeqUint8(bytes[bytes_offset as int + 4*(pos as int) .. bytes_offset as int + 4*(pos as int)+4])) == value as int;
        forall j | 0 <= j < pos as int + 1
            ensures BEByteSeqToInt(ToSeqUint8(bytes[bytes_offset as int + 4*j .. bytes_offset as int + 4*j+4])) == words[words_offset as int + j] as int;
        {
            if j < pos as int {
                assert bytes[bytes_offset as int + 4*j .. bytes_offset as int + 4*j+4] == old_bytes[bytes_offset as int + 4*j .. bytes_offset as int + 4*j+4];
            }
        }
        pos := pos + 1;
    }

    ghost var words' := words[words_offset as int .. words_offset as int + words_len as int];
    ghost var bytes' := bytes[bytes_offset as int .. bytes_offset as int + bytes_len as int];
    forall j | 0 <= j < |words'|
        ensures BEByteSeqToInt(ToSeqUint8(bytes'[4*j..4*j+4])) == words'[j] as int;
    {
        lemma_SequenceExtensionality(bytes'[4*j..4*j+4], bytes[bytes_offset as int + 4*j .. bytes_offset as int + 4*j+4]);
        assert words'[j] == words[words_offset as int + j];
    }

    lemma_CopyWordToByteArrayHelper(words[words_offset as int .. words_offset as int + words_len as int], bytes[bytes_offset as int .. bytes_offset as int + bytes_len as int]);
}

method {:timeLimitMultiplier 5} ComputeHMACSHA256(key:array<uint>, message:array<byte>, offset:uint, len:uint, digest:array<uint>)
    requires allocated(key);
    requires key != null;
    requires key.Length == 16;
    requires allocated(message);
    requires message != null;
    requires (offset as int) + (len as int) <= message.Length;
    requires (offset as int) + (len as int) <= 0x1_0000_0000;   // TODO: Switch back to MaxBytesForSHA() - 64 when not using 32-bit Vale code
    requires allocated(digest);
    requires digest != null;
    requires digest != key;
    requires digest.Length == 8;
    ensures  ToSeqUint32(digest[..]) == HMAC_SHA256(ToSeqUint32(key[..]), ToSeqUint8(message[offset as int .. offset as int + len as int]));
    modifies digest;
{
    ghost var msg := ToSeqUint8(message[offset as int .. offset as int + len as int]);
    var ctx:SHA256Context := new SHA256Context();
    SHA256_Init(ctx);

    var buf:array<byte> := new byte[96];
    XorKeyIntoByteArray(key, buf, 0x36363636);
    assert ToSeqUint8(buf[..64]) == WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Ipad(16)));
    SHA256_Update(ctx, buf, 0, 64);
    assert ctx.BytesIncluded() == ToSeqUint8(buf[..64]);
    assert ctx.BytesIncluded() == WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Ipad(16)));
    SHA256_Update(ctx, message, offset as ulong, len as ulong);
    assert ctx.BytesIncluded() == WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Ipad(16))) + msg;
    SHA256_Final(ctx, digest);
    assert ToSeqUint32(digest[..]) == SHA256(WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Ipad(16))) + msg);

    XorKeyIntoByteArray(key, buf, 0x5c5c5c5c);
    ghost var old_buf := buf[..];
    assert ToSeqUint8(old_buf[0..64]) == WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Opad(16)));
    CopyWordSeqIntoByteArray(digest, 0, 8, buf, 64, 32);
    assert forall j | 0 <= j < 64 :: buf[j] == old_buf[j];
    assert buf[0..64] == old_buf[0..64];
    assert ToSeqUint8(buf[0..64]) == WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Opad(16)));

    calc {
        ToSeqUint8(buf[64..96]);
        ToSeqUint8(buf[64..64+32]);
        WordSeqToBytes(ToSeqUint32(digest[0..8]));
            { assert digest.Length == 8; assert digest[0..8] == digest[..8] == digest[..]; }
        WordSeqToBytes(ToSeqUint32(digest[..]));
    }

    calc {
        ToSeqUint8(buf[0..96]);
        ToSeqUint8(buf[0..64] + buf[64..96]);
            { lemma_ToSeqUint8DistributesOverConcatenation(buf[0..64], buf[64..96]); }
        ToSeqUint8(buf[0..64]) + ToSeqUint8(buf[64..96]);
        ToSeqUint8(buf[0..64]) + WordSeqToBytes(ToSeqUint32(digest[..]));
        WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Opad(16))) + WordSeqToBytes(ToSeqUint32(digest[..]));
            { lemma_WordSeqToBytes_Adds(SeqXor(ToSeqUint32(key[..]), Opad(16)), ToSeqUint32(digest[..])); }
        WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Opad(16)) + ToSeqUint32(digest[..]));
        WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Opad(16)) + SHA256(WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Ipad(16))) + msg));
    }

    SHA256_Init(ctx);
    SHA256_Update(ctx, buf, 0, 96);
    calc {
        ctx.BytesIncluded();
        ToSeqUint8(buf[0..96]);
        WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Opad(16)) + SHA256(WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Ipad(16))) + msg));
    }
    SHA256_Final(ctx, digest);

    calc {
        ToSeqUint32(digest[..]);
        SHA256(WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Opad(16)) + SHA256(WordSeqToBytes(SeqXor(ToSeqUint32(key[..]), Ipad(16))) + msg)));
        HMAC_SHA256(ToSeqUint32(key[..]), msg);
        HMAC_SHA256(ToSeqUint32(key[..]), ToSeqUint8(message[offset as int .. offset as int + len as int]));
    }
}
