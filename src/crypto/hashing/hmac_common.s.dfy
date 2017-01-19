include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"

module hmac_common_s {

import opened operations_s
import opened words_and_bytes_s

//-////////////////////////////////////////////////////////////////////////////
//- HMAC specification based on:
//- http://csrc.nist.gov/publications/fips/fips198-1/FIPS-198-1_final.pdf
//-////////////////////////////////////////////////////////////////////////////

function {:opaque} SeqXor(a:seq<uint32>, b:seq<uint32>) : seq<uint32>
    requires |a|==|b|;
    ensures  |SeqXor(a, b)| == |a|;
    ensures  forall i :: 0 <= i < |a| ==> SeqXor(a, b)[i] == BitwiseXor(a[i], b[i]);
{
    if |a| == 0 then [] else [ BitwiseXor(a[0], b[0]) ] + SeqXor(a[1..], b[1..])
}

function {:autoReq} Opad(len:int) : seq<uint32>
{
    RepeatValue<uint32>(0x5c5c5c5c as uint32, len)
}

function {:autoReq} Ipad(len:int) : seq<uint32>
{
    RepeatValue<uint32>(0x36363636 as uint32, len)
}

}
