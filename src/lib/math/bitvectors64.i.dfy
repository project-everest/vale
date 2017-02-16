include "../util/types.s.dfy"
include "../util/operations.s.dfy"
include "div.i.dfy"
include "bitvectors64.s.dfy"

module bitvectors64_i
{
import opened types_s
import opened operations_s
import opened bitvectors64_s
import opened Math__div_i

function u64add(x:uint64, y:uint64):uint64 { mod2_64(x + y) }
function u64sub(x:uint64, y:uint64):uint64 { mod2_64(x - y) }
function u64mul(x:uint64, y:uint64):uint64 { mod2_64(x * y) }
function u64div(x:uint64, y:uint64):uint64 requires y != 0 { lemma_div_nonincreasing(x, y); lemma_div_pos_is_pos(x, y); x / y }
function u64mod(x:uint64, y:uint64):uint64 requires y != 0 { x % y }

// HACK: work around some Dafny/Z3 triggering issues:
predicate T_BitwiseShl64(x:uint64, y:uint64) { true }
predicate T_BitwiseShr64(x:uint64, y:uint64) { true }
predicate T_u64div(x:uint64, y:uint64) { true }
predicate T_u64mod(x:uint64, y:uint64) { true }
predicate T_U64(x:bv64) { true }

lemma lemma_BitsToWord64(x:bv64)
    ensures  BitsToWord64(x) == U64(x)
{
    reveal_U64();
    reveal_BitsToWord64();
}

lemma lemma_WordToBits64(x:uint64)
    ensures  WordToBits64(x) == B64(x)
{
    reveal_B64();
    reveal_WordToBits64();
}

lemma lemma_WordToBits64_forall()
    ensures  forall x:uint64 {:trigger WordToBits64(x)} :: WordToBits64(x) == B64(x)
{
    reveal_B64();
    reveal_WordToBits64();
}

lemma lemma_BitwiseAnd64(x:uint64, y:uint64)
    ensures  BitwiseAnd64(x, y) == U64(bv64and(B64(x), B64(y)))
{
    calc
    {
        BitwiseAnd64(x, y);                                       { reveal_BitwiseAnd64_opaque(); }
        BitsToWord64(BitAnd64(WordToBits64(x), WordToBits64(y))); { lemma_WordToBits64_forall(); }
        BitsToWord64(BitAnd64(B64(x), B64(y)));                   { lemma_BitsToWord64(BitAnd64(B64(x), B64(y))); }
        U64(BitAnd64(B64(x), B64(y)));                            { reveal_BitAnd64(); }
        U64(B64(x) & B64(y));                                     { reveal_bv64and(); }
        U64(bv64and(B64(x), B64(y)));
    }
}

lemma lemma_BitwiseAnd64_forall()
    ensures  forall x:uint64, y:uint64 {:trigger BitwiseAnd64(x, y)} :: BitwiseAnd64(x, y) == U64(bv64and(B64(x), B64(y)))
{
    forall x:uint64, y:uint64
        ensures BitwiseAnd64(x, y) == U64(bv64and(B64(x), B64(y)))
    {
        lemma_BitwiseAnd64(x, y);
    }
}

lemma lemma_BitwiseShl64_helper(x:bv64, y:bv64)
    requires y < 64
    ensures  BitShl64(x, y) == bv64shl(x, y)
{
    reveal_BitShl64();
    reveal_bv64shl();
}

lemma lemma_BitwiseShl64(x:uint64, y:uint64)
    requires y < 64
    ensures  B64(y) < 64
    ensures  BitwiseShl64(x, y) == U64(bv64shl(B64(x), B64(y)))
{
    lemma_bv64le(64, y);
    assert B64(64) == 64 by { reveal_B64(); }
    assert WordToBits64(y) == B64(y) by { lemma_WordToBits64(y); }
    calc
    {
        BitwiseShl64(x, y);                                       { reveal_BitwiseShl64_opaque(); }
        BitsToWord64(BitShl64(WordToBits64(x), WordToBits64(y))); { lemma_WordToBits64_forall(); }
        BitsToWord64(BitShl64(B64(x), B64(y)));                   { lemma_BitsToWord64(BitShl64(B64(x), B64(y))); }
        U64(BitShl64(B64(x), B64(y)));                            { lemma_BitwiseShl64_helper(B64(x), B64(y)); }
        U64(bv64shl(B64(x), B64(y)));
    }
}

lemma lemma_BitwiseShl64_forall()
    ensures  forall x:uint64, y:uint64 {:trigger BitwiseShl64(x, y)}{:trigger T_BitwiseShl64(x, y)} ::
        y < 64 ==> B64(y) < 64 && BitwiseShl64(x, y) == U64(bv64shl(B64(x), B64(y)))
{
    forall y:uint64 {:trigger y < 64} | y < 64
        ensures  B64(y) < 64
    {
        lemma_BitwiseShl64(0, y);
    }
    forall x:uint64, y:uint64 | y < 64
        ensures  B64(y) < 64 && BitwiseShl64(x, y) == U64(bv64shl(B64(x), B64(y)))
    {
        lemma_BitwiseShl64(x, y);
    }
}

lemma lemma_BitwiseShr64_helper(x:bv64, y:bv64)
    requires y < 64
    ensures  BitShr64(x, y) == bv64shr(x, y)
{
    reveal_BitShr64();
    reveal_bv64shr();
}

lemma lemma_BitwiseShr64(x:uint64, y:uint64)
    requires y < 64
    ensures  B64(y) < 64
    ensures  BitwiseShr64(x, y) == U64(bv64shr(B64(x), B64(y)))
{
    lemma_bv64le(64, y);
    assert B64(64) == 64 by { reveal_B64(); }
    assert WordToBits64(y) == B64(y) by { lemma_WordToBits64(y); }
    calc
    {
        BitwiseShr64(x, y);                                       { reveal_BitwiseShr64_opaque(); }
        BitsToWord64(BitShr64(WordToBits64(x), WordToBits64(y))); { lemma_WordToBits64_forall(); }
        BitsToWord64(BitShr64(B64(x), B64(y)));                   { lemma_BitsToWord64(BitShr64(B64(x), B64(y))); }
        U64(BitShr64(B64(x), B64(y)));                            { lemma_BitwiseShr64_helper(B64(x), B64(y)); }
        U64(bv64shr(B64(x), B64(y)));
    }
}

lemma lemma_BitwiseShr64_forall()
    ensures  forall x:uint64, y:uint64 {:trigger BitwiseShr64(x, y)}{:trigger T_BitwiseShr64(x, y)} ::
        y < 64 ==> B64(y) < 64 && BitwiseShr64(x, y) == U64(bv64shr(B64(x), B64(y)))
{
    forall y:uint64 {:trigger y < 64} | y < 64
        ensures  B64(y) < 64
    {
        lemma_BitwiseShr64(0, y);
    }
    forall x:uint64, y:uint64 | y < 64
        ensures  B64(y) < 64 && BitwiseShr64(x, y) == U64(bv64shr(B64(x), B64(y)))
    {
        lemma_BitwiseShr64(x, y);
    }
}

lemma lemma_bv_add64_forall()
    ensures forall x:uint64, y:uint64 {:trigger u64add(x, y)} :: u64add(x, y) == U64(bv64add(B64(x), B64(y)))
{
    forall x:uint64, y:uint64 {:trigger u64add(x, y)}
        ensures u64add(x, y) == U64(bv64add(B64(x), B64(y)))
    {
        lemma_bv64add(x, y);
    }
}

lemma lemma_bv_sub64_forall()
    ensures forall x:uint64, y:uint64 {:trigger u64sub(x, y)} :: u64sub(x, y) == U64(bv64sub(B64(x), B64(y)))
{
    forall x:uint64, y:uint64 {:trigger u64sub(x, y)}
        ensures u64sub(x, y) == U64(bv64sub(B64(x), B64(y)))
    {
        lemma_bv64sub(x, y);
    }
}

lemma lemma_bv_mul64_forall()
    ensures forall x:uint64, y:uint64 {:trigger u64mul(x, y)} :: u64mul(x, y) == U64(bv64mul(B64(x), B64(y)))
{
    forall x:uint64, y:uint64 {:trigger u64mul(x, y)}
        ensures u64mul(x, y) == U64(bv64mul(B64(x), B64(y)))
    {
        lemma_bv64mul(x, y);
    }
}

lemma lemma_bv_div64_forall()
    ensures forall x:uint64, y:uint64 {:trigger u64div(x, y)}{:trigger T_u64div(x, y)} :: T_u64div(x, y) ==>
        y != 0 ==> B64(y) != 0 && u64div(x, y) == U64(bv64div(B64(x), B64(y)))
{
    forall x:uint64, y:uint64 {:trigger T_u64div(x, y)} | y != 0
        ensures B64(y) != 0 && u64div(x, y) == U64(bv64div(B64(x), B64(y)))
    {
        lemma_bv64div(x, y);
    }
}

lemma lemma_bv_mod64_forall()
    ensures forall x:uint64, y:uint64 {:trigger u64mod(x, y)}{:trigger T_u64mod(x, y)} :: T_u64mod(x, y) ==>
        y != 0 ==> B64(y) != 0 && u64mod(x, y) == U64(bv64mod(B64(x), B64(y)))
{
    forall x:uint64, y:uint64 {:trigger T_u64mod(x, y)} | y != 0
        ensures B64(y) != 0 && u64mod(x, y) == U64(bv64mod(B64(x), B64(y)))
    {
        lemma_bv64mod(x, y);
    }
}

lemma lemma_B64_forall()
    ensures forall b:bv64 {:trigger B64(U64(b))}{:trigger T_U64(b)} :: T_U64(b) ==> B64(U64(b)) == b
{
    forall b:bv64 {:trigger T_U64(b)} ensures B64(U64(b)) == b { lemma_B64(b); }
}

lemma lemma_bv64_helpers()
    ensures forall b:bv64 {:trigger B64(U64(b))} :: T_U64(b) ==> B64(U64(b)) == b
    ensures forall x:uint64, y:uint64 {:trigger u64add(x, y)} ::
        u64add(x, y) == U64(bv64add(B64(x), B64(y)))
    ensures forall x:uint64, y:uint64 {:trigger u64sub(x, y)} ::
        u64sub(x, y) == U64(bv64sub(B64(x), B64(y)))
    ensures forall x:uint64, y:uint64 {:trigger u64mul(x, y)} ::
        u64mul(x, y) == U64(bv64mul(B64(x), B64(y)))
    ensures forall x:uint64, y:uint64 {:trigger u64div(x, y)} :: T_u64div(x, y) ==>
        y != 0 ==> B64(y) != 0 && u64div(x, y) == U64(bv64div(B64(x), B64(y)))
    ensures forall x:uint64, y:uint64 {:trigger u64mod(x, y)} :: T_u64mod(x, y) ==>
        y != 0 ==> B64(y) != 0 && u64mod(x, y) == U64(bv64mod(B64(x), B64(y)))
    ensures forall x:uint64, y:uint64 {:trigger BitwiseAnd64(x, y)} ::
        BitwiseAnd64(x, y) == U64(bv64and(B64(x), B64(y)))
    ensures forall x:uint64, y:uint64 {:trigger BitwiseShl64(x, y)} :: T_BitwiseShl64(x, y) ==>
        y < 64 ==> B64(y) < 64 && BitwiseShl64(x, y) == U64(bv64shl(B64(x), B64(y)))
    ensures forall x:uint64, y:uint64 {:trigger BitwiseShr64(x, y)} :: T_BitwiseShr64(x, y) ==>
        y < 64 ==> B64(y) < 64 && BitwiseShr64(x, y) == U64(bv64shr(B64(x), B64(y)))
    ensures  B64(0) == 0
    ensures  B64(1) == 1
    ensures  B64(2) == 2
    ensures  B64(3) == 3
    ensures  B64(4) == 4
    ensures  B64(8) == 8
    ensures  B64(16) == 16
    ensures  U64(0) == 0
    ensures  U64(1) == 1
    ensures  U64(2) == 2
    ensures  U64(3) == 3
    ensures  U64(4) == 4
    ensures  U64(8) == 8
    ensures  U64(16) == 16
{
    lemma_B64_forall();
    lemma_bv_add64_forall();
    lemma_bv_sub64_forall();
    lemma_bv_mul64_forall();
    lemma_bv_div64_forall();
    lemma_bv_mod64_forall();
    lemma_BitwiseAnd64_forall();
    lemma_BitwiseShl64_forall();
    lemma_BitwiseShr64_forall();
    assert B64(0) == 0 by { reveal_B64(); }
    assert B64(1) == 1 by { reveal_B64(); }
    assert B64(2) == 2 by { reveal_B64(); }
    assert B64(3) == 3 by { reveal_B64(); }
    assert B64(4) == 4 by { reveal_B64(); }
    assert B64(8) == 8 by { reveal_B64(); }
    assert B64(16) == 16 by { reveal_B64(); }
    assert U64(0) == 0 by { reveal_U64(); }
    assert U64(1) == 1 by { reveal_U64(); }
    assert U64(2) == 2 by { reveal_U64(); }
    assert U64(3) == 3 by { reveal_U64(); }
    assert U64(4) == 4 by { reveal_U64(); }
    assert U64(8) == 8 by { reveal_U64(); }
    assert U64(16) == 16 by { reveal_U64(); }
}

} // end module
