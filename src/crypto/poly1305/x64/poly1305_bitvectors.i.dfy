include "../../../lib/math/bitvectors64.i.dfy"

module x64__Poly1305_bitvectors_i
{
import opened bitvectors64_s
import opened bitvectors64_i

lemma lemma_shr2_bv(x:bv64)
    ensures  bv64shr(x, 2) == bv64div(x, 4)
{
    reveal_bv64shr();
    reveal_bv64div();
}

lemma lemma_shr2(x:uint64)
    ensures BitwiseShr64(x, 2) == u64div(x, 4)
{
    lemma_bv64_helpers();
    lemma_shr2_bv(B64(x));
}

lemma lemma_shr4_bv(x:bv64)
    ensures  bv64shr(x, 4) == bv64div(x, 16)
{
    reveal_bv64shr();
    reveal_bv64div();
}

lemma lemma_shr4(x:uint64)
    ensures BitwiseShr64(x, 4) == u64div(x, 16)
{
    lemma_bv64_helpers();
    lemma_shr4_bv(B64(x));
}

lemma lemma_and_mod4_bv(x:bv64)
    ensures  bv64and(x, 3) == bv64mod(x, 4)
{
    reveal_bv64and();
    reveal_bv64mod();
}

lemma lemma_and_mod4(x:uint64)
    ensures BitwiseAnd64(x, 3) == u64mod(x, 4)
{
    lemma_bv64_helpers();
    lemma_and_mod4_bv(B64(x));
}

lemma lemma_clear_lower2_bv(x:bv64)
    ensures  bv64and(x, 0xffff_ffff_ffff_fffc) == bv64mul(bv64div(x, 4), 4)
{
    reveal_bv64and();
    reveal_bv64mul();
    reveal_bv64div();
}

lemma lemma_clear_lower2(x:uint64)
    ensures  BitwiseAnd64(x, 0xffff_ffff_ffff_fffc) == (x / 4) * 4
{
    lemma_bv64_helpers();
    assert B64(0xffff_ffff_ffff_fffc) == 0xffff_ffff_ffff_fffc by { reveal_B64(); }
    calc
    {
        BitwiseAnd64(x, 0xffff_ffff_ffff_fffc); { lemma_clear_lower2_bv(B64(x)); }
        u64mul(u64div(x, 4), 4);                { reveal_mod2_64(); }
        (x / 4) * 4;
    }
}

lemma lemma_and_commutes_bv(x:bv64, y:bv64)
    ensures bv64and(x, y) == bv64and(y, x)
{
    reveal_bv64and();
}

lemma lemma_and_commutes(x:uint64, y:uint64)
    ensures BitwiseAnd64(x, y) == BitwiseAnd64(y, x)
{
    lemma_bv64_helpers();
    lemma_and_commutes_bv(B64(x), B64(y));
}

lemma lemma_poly_bits64()
    ensures forall x:uint64 {:trigger BitwiseShr64(x, 2)} :: BitwiseShr64(x, 2) == x / 4
    ensures forall x:uint64 {:trigger BitwiseShr64(x, 4)} :: BitwiseShr64(x, 4) == x / 16
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 3)} :: BitwiseAnd64(x, 3) == x % 4
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 0xffff_ffff_ffff_fffc)} ::
        BitwiseAnd64(x, 0xffff_ffff_ffff_fffc) == (x / 4) * 4
    ensures forall x:uint64, y:uint64 :: BitwiseAnd64(x, y) == BitwiseAnd64(y, x)
{
    forall x:uint64
        ensures BitwiseShr64(x, 2) == x / 4
        ensures BitwiseShr64(x, 4) == x / 16
        ensures BitwiseAnd64(x, 3) == x % 4
        ensures BitwiseAnd64(x, 0xffff_ffff_ffff_fffc) == (x / 4) * 4
    {
        lemma_shr2(x);
        lemma_shr4(x);
        lemma_and_mod4(x);
        lemma_clear_lower2(x);
    }
    forall x:uint64, y:uint64
        ensures BitwiseAnd64(x, y) == BitwiseAnd64(y, x);
    {
        lemma_and_commutes(x, y);
    }
}

} // end module
