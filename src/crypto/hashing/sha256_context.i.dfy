include "sha256.i.dfy"
include "../../lib/collections/Seqs.i.dfy"
include "../../lib/util/types.i.dfy"

import opened Collections__Seqs_i_temp = Collections__Seqs_i
import opened SHA256_i_temp = sha256_i
import opened types_i_temp = types_i

///////////////////////////////////
// FUNCTIONS
///////////////////////////////////

function ArrayToObject<T>(a:array<T>) : object
{
    a
}

///////////////////////////////////
// TYPES
///////////////////////////////////

class SHA256Context
{
    ghost var z:SHA256Trace;
    ghost var processed_bytes:seq<uint8>;
    var H:array<uint>;
    var unprocessed_bytes:array<byte>;
    var num_unprocessed_bytes:uint;
    var num_total_bytes:ulong;

    ghost var Repr:set<object>;

    function ToObject() : object
    {
        this
    }

    constructor()
        modifies this;
        ensures  fresh(this.H);
        ensures  fresh(this.unprocessed_bytes);
        ensures  Valid();
    {
        this.processed_bytes := [];
        this.H := new uint[8];
        this.unprocessed_bytes := new byte[64];
        this.num_unprocessed_bytes := 0;
        this.Repr := { ToObject(), ArrayToObject(this.H), ArrayToObject(this.unprocessed_bytes) };
    }

    predicate Valid()
        reads this;
    {
           allocated(this.H)
        && this.H != null
        && this.H.Length == 8
        && allocated(this.unprocessed_bytes)
        && this.unprocessed_bytes != null
        && this.unprocessed_bytes.Length == 64
        && this.num_unprocessed_bytes as int <= 64
        && this.Repr == { ToObject(), ArrayToObject(this.H), ArrayToObject(this.unprocessed_bytes) }
    }

    predicate ExportedInvariant()
        reads this, Repr;
    {
           Valid()
        && this.num_total_bytes as int == |this.processed_bytes| + (this.num_unprocessed_bytes as int)
        && |this.processed_bytes| % 64 == 0
        && this.num_unprocessed_bytes as int < 64
        && this.num_total_bytes as int <= MaxBytesForSHA()
        && IsCompleteSHA256Trace(this.z)
        && SHA256TraceIsCorrect(this.z)
        && WordSeqToBytes(ConcatenateSeqs(this.z.M)) == this.processed_bytes
        && ToSeqUint32(this.H[..]) == last(this.z.H) 
    }

    function BytesIncluded() : seq<uint8>
        requires Valid();
        reads    this, Repr;
    {
        this.processed_bytes + ToSeqUint8(this.unprocessed_bytes[..this.num_unprocessed_bytes])
    }
}
