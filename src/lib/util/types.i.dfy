include "types.s.dfy"

module types_i {

import opened types_s

function {:opaque} ToSeqUint8(s:seq<byte>) : seq<uint8>
    ensures var s' := ToSeqUint8(s);
            |s| == |s'|
         && forall i :: 0 <= i < |s| ==> s[i] as uint8 == s'[i]
{
    if s == [] then []
    else [s[0] as uint8] + ToSeqUint8(s[1..])
}

function {:opaque} ToSeqUint32(s:seq<uint>) : seq<uint32>
    ensures var s' := ToSeqUint32(s);
            |s| == |s'|
         && forall i :: 0 <= i < |s| ==> s[i] as uint32 == s'[i]
{
    if s == [] then []
    else [s[0] as uint32] + ToSeqUint32(s[1..])
}

lemma lemma_ToSeqUint8OfSlice(s:seq<byte>, left:int, right:int)
    requires 0 <= left <= right <= |s|;
    ensures  ToSeqUint8(s[left..right]) == ToSeqUint8(s)[left..right];
{
    var s1 := ToSeqUint8(s[left..right]);
    var s2 := ToSeqUint8(s)[left..right];

    assert |s1| == right - left == |s2|;
    forall i | 0 <= i < |s1|
        ensures s1[i] == s2[i];
    {
        assert s1[i] == s[left+i] as uint8 == s2[i];
    }
}

lemma lemma_ToSeqUint32OfSlice(s:seq<uint>, left:int, right:int)
    requires 0 <= left <= right <= |s|;
    ensures  ToSeqUint32(s[left..right]) == ToSeqUint32(s)[left..right];
{
    var s1 := ToSeqUint32(s[left..right]);
    var s2 := ToSeqUint32(s)[left..right];

    assert |s1| == right - left == |s2|;
    forall i | 0 <= i < |s1|
        ensures s1[i] == s2[i];
    {
        assert s1[i] == s[left+i] as uint32 == s2[i];
    }
}

lemma lemma_ToSeqUint8DistributesOverConcatenation(s1:seq<byte>, s2:seq<byte>)
    ensures ToSeqUint8(s1 + s2) == ToSeqUint8(s1) + ToSeqUint8(s2);
{
    reveal_ToSeqUint8();
}

lemma lemma_ToSeqUint32DistributesOverConcatenation(s1:seq<uint>, s2:seq<uint>)
    ensures ToSeqUint32(s1 + s2) == ToSeqUint32(s1) + ToSeqUint32(s2);
{
    reveal_ToSeqUint32();
}

}
