include "../../../lib/math/bitvectors64.i.dfy"
include "../../../lib/math/bitvectors128.i.dfy"
include "poly1305.s.dfy"

module x64__Poly1305_bitvectors_i
{
import opened bitvectors64_s
import opened bitvectors64_i
import opened bitvectors128_s
import opened bitvectors128_i
import opened x64__Poly1305_s

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

lemma lemma_and_mod_n_bv(x:bv64)
    ensures  bv64and(x, 3) == bv64mod(x, 4)
    ensures  bv64and(x, 15) == bv64mod(x, 16)
{
    reveal_bv64and();
    reveal_bv64mod();
}

lemma lemma_and_mod_n(x:uint64)
    ensures BitwiseAnd64(x, 3) == u64mod(x, 4)
    ensures BitwiseAnd64(x, 15) == u64mod(x, 16)
{
    lemma_bv64_helpers();
    lemma_and_mod_n_bv(B64(x));
    assert B64(15) == 15 by { reveal_B64(); }
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

lemma lemma_and_constants_bv(x:bv64)
    ensures  bv64and(x, 0) == 0
    ensures  bv64and(x, 0xffff_ffff_ffff_ffff) == x
{
    reveal_bv64and();
}

lemma lemma_and_constants(x:uint64)
    ensures  BitwiseAnd64(x, 0) == 0
    ensures  BitwiseAnd64(x, 0xffff_ffff_ffff_ffff) == x
{
    lemma_bv64_helpers();
    lemma_and_constants_bv(B64(x));
    assert B64(0xffff_ffff_ffff_ffff) == 0xffff_ffff_ffff_ffff by { reveal_B64(); }
    lemma_U64(x);
}

lemma lemma_poly_constants_bv(x:bv64)
    ensures  bv64and(x, 0x0fff_fffc_0fff_ffff) < 0x1000_0000_0000_0000
    ensures  bv64and(x, 0x0fff_fffc_0fff_fffc) < 0x1000_0000_0000_0000
    ensures  bv64mod(bv64and(x, 0x0fff_fffc_0fff_fffc), 4) == 0
{
    reveal_bv64and();
    reveal_bv64mod();
}

lemma lemma_poly_constants(x:uint64)
    ensures  BitwiseAnd64(x, 0x0fff_fffc_0fff_ffff) < 0x1000_0000_0000_0000
    ensures  BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc) < 0x1000_0000_0000_0000
    ensures  u64mod(BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc), 4) == 0
{
    lemma_bv64_helpers();
    lemma_poly_constants_bv(B64(x));
    lemma_bv64le(0x1000_0000_0000_0000, BitwiseAnd64(x, 0x0fff_fffc_0fff_ffff));
    lemma_bv64le(0x1000_0000_0000_0000, BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc));
    assert B64(0x0fff_fffc_0fff_ffff) == 0x0fff_fffc_0fff_ffff by { reveal_B64(); }
    assert B64(0x0fff_fffc_0fff_fffc) == 0x0fff_fffc_0fff_fffc by { reveal_B64(); }
    assert B64(0x1000_0000_0000_0000) == 0x1000_0000_0000_0000 by { reveal_B64(); }
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
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 15)} :: BitwiseAnd64(x, 15) == x % 16
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 0)} ::
        BitwiseAnd64(x, 0) == 0
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 0xffff_ffff_ffff_ffff)} ::
        BitwiseAnd64(x, 0xffff_ffff_ffff_ffff) == x
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 0xffff_ffff_ffff_fffc)} ::
        BitwiseAnd64(x, 0xffff_ffff_ffff_fffc) == (x / 4) * 4
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 0x0fff_fffc_0fff_ffff)} ::
        BitwiseAnd64(x, 0x0fff_fffc_0fff_ffff) < 0x1_0000_0000_0000_0000 / 16
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc)} ::
        BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc) < 0x1_0000_0000_0000_0000 / 16
    ensures forall x:uint64 {:trigger BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc)} ::
        BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc) % 4 == 0
    ensures forall x:uint64, y:uint64 :: BitwiseAnd64(x, y) == BitwiseAnd64(y, x)
{
    forall x:uint64
        ensures BitwiseShr64(x, 2) == x / 4
        ensures BitwiseShr64(x, 4) == x / 16
        ensures BitwiseAnd64(x, 3) == x % 4
        ensures BitwiseAnd64(x, 15) == x % 16
        ensures BitwiseAnd64(x, 0) == 0
        ensures BitwiseAnd64(x, 0xffff_ffff_ffff_ffff) == x
        ensures BitwiseAnd64(x, 0xffff_ffff_ffff_fffc) == (x / 4) * 4
        ensures BitwiseAnd64(x, 0x0fff_fffc_0fff_ffff) < 0x1_0000_0000_0000_0000 / 16
        ensures BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc) < 0x1_0000_0000_0000_0000 / 16
        ensures BitwiseAnd64(x, 0x0fff_fffc_0fff_fffc) % 4 == 0
    {
        lemma_shr2(x);
        lemma_shr4(x);
        lemma_and_mod_n(x);
        lemma_clear_lower2(x);
        lemma_and_constants(x);
        lemma_poly_constants(x);
    }
    forall x:uint64, y:uint64
        ensures BitwiseAnd64(x, y) == BitwiseAnd64(y, x);
    {
        lemma_and_commutes(x, y);
    }
}

lemma lemma_bv128_64_64_and_helper(x:bv128, x0:bv64, x1:bv64, y:bv128, y0:bv64, y1:bv64, z:bv128, z0:bv64, z1:bv64)
    requires z0 == bv64and(x0, y0)
    requires z1 == bv64and(x1, y1)
    requires x == bv128or(bv128shl(x1 as bv128, 64), x0 as bv128)
    requires y == bv128or(bv128shl(y1 as bv128, 64), y0 as bv128)
    requires z == bv128or(bv128shl(z1 as bv128, 64), z0 as bv128)
    ensures  z == bv128and(x, y)
{
    reveal_bv128_64();
    reveal_bv64and();
    reveal_bv128and();
    reveal_bv128or();
    reveal_bv128shl();
}

lemma lemma_bv128_64_64_and(x:bv128, x0:bv64, x1:bv64, y:bv128, y0:bv64, y1:bv64, z:bv128, z0:bv64, z1:bv64)
    requires z0 == bv64and(x0, y0)
    requires z1 == bv64and(x1, y1)
    requires x == bv128_64_64(x1, x0)
    requires y == bv128_64_64(y1, y0)
    requires z == bv128_64_64(z1, z0)
    ensures  z == bv128and(x, y)
{
    assert bv128_64(x0) == x0 as bv128 by { reveal_bv128_64(); }
    assert bv128_64(x1) == x1 as bv128 by { reveal_bv128_64(); }
    assert bv128_64(y0) == y0 as bv128 by { reveal_bv128_64(); }
    assert bv128_64(y1) == y1 as bv128 by { reveal_bv128_64(); }
    assert bv128_64(z0) == z0 as bv128 by { reveal_bv128_64(); }
    assert bv128_64(z1) == z1 as bv128 by { reveal_bv128_64(); }
    reveal_bv128_64_64();
    lemma_bv128_64_64_and_helper(x, x0, x1, y, y0, y1, z, z0, z1);
}

lemma lemma_lowerUpper128_and(x:uint128, x0:uint64, x1:uint64, y:uint128, y0:uint64, y1:uint64, z:uint128, z0:uint64, z1:uint64)
    requires z0 == BitwiseAnd64(x0, y0)
    requires z1 == BitwiseAnd64(x1, y1)
    requires x == lowerUpper128(x0, x1)
    requires y == lowerUpper128(y0, y1)
    requires z == lowerUpper128(z0, z1)
    ensures  z == and128(x, y)
{
    calc
    {
        and128(x, y); { reveal_and128_opaque(); }
        U128(bv128and(B128(x), B128(y)));
        {
            lemma_bv128_lowerUpper_B128(x0, x1);
            lemma_bv128_lowerUpper_B128(y0, y1);
            lemma_bv128_lowerUpper_B128(z0, z1);
            assert B64(z0) == bv64and(B64(x0), B64(y0)) by { lemma_U64(z0); lemma_bv64_helpers(); }
            assert B64(z1) == bv64and(B64(x1), B64(y1)) by { lemma_U64(z1); lemma_bv64_helpers(); }
            lemma_bv128_64_64_and(B128(x), B64(x0), B64(x1), B128(y), B64(y0), B64(y1), B128(z), B64(z0), B64(z1));
        }
        U128(B128(z)); { lemma_U128(z); }
        lowerUpper128(z0, z1);
    }
}

lemma lemma_bytes_shift_constants()
    ensures  bv64shl(0, 3) == 0
    ensures  bv64shl(1, 3) == 8
    ensures  bv64shl(2, 3) == 16
    ensures  bv64shl(3, 3) == 24
    ensures  bv64shl(4, 3) == 32
    ensures  bv64shl(5, 3) == 40
    ensures  bv64shl(6, 3) == 48
    ensures  bv64shl(7, 3) == 56
    ensures  bv64shl(1, bv64shl(0, 3)) == 0x1
    ensures  bv64shl(1, bv64shl(1, 3)) == 0x1_00
    ensures  bv64shl(1, bv64shl(2, 3)) == 0x1_0000
    ensures  bv64shl(1, bv64shl(3, 3)) == 0x1_0000_00
    ensures  bv64shl(1, bv64shl(4, 3)) == 0x1_0000_0000
    ensures  bv64shl(1, bv64shl(5, 3)) == 0x1_0000_0000_00
    ensures  bv64shl(1, bv64shl(6, 3)) == 0x1_0000_0000_0000
    ensures  bv64shl(1, bv64shl(7, 3)) == 0x1_0000_0000_0000_00
{
    reveal_bv64shl();
}

lemma lemma_bytes_and_mod0(x:bv64) ensures bv64and(x, 0x1                   - 1) == bv64mod(x, 0x1                  ) { reveal_bv64and(); reveal_bv64mod(); }
lemma lemma_bytes_and_mod1(x:bv64) ensures bv64and(x, 0x1_00                - 1) == bv64mod(x, 0x1_00               ) { reveal_bv64and(); reveal_bv64mod(); }
lemma lemma_bytes_and_mod2(x:bv64) ensures bv64and(x, 0x1_0000              - 1) == bv64mod(x, 0x1_0000             ) { reveal_bv64and(); reveal_bv64mod(); }
lemma lemma_bytes_and_mod3(x:bv64) ensures bv64and(x, 0x1_0000_00           - 1) == bv64mod(x, 0x1_0000_00          ) { reveal_bv64and(); reveal_bv64mod(); }
lemma lemma_bytes_and_mod4(x:bv64) ensures bv64and(x, 0x1_0000_0000         - 1) == bv64mod(x, 0x1_0000_0000        ) { reveal_bv64and(); reveal_bv64mod(); }
lemma lemma_bytes_and_mod5(x:bv64) ensures bv64and(x, 0x1_0000_0000_00      - 1) == bv64mod(x, 0x1_0000_0000_00     ) { reveal_bv64and(); reveal_bv64mod(); }
lemma lemma_bytes_and_mod6(x:bv64) ensures bv64and(x, 0x1_0000_0000_0000    - 1) == bv64mod(x, 0x1_0000_0000_0000   ) { reveal_bv64and(); reveal_bv64mod(); }
lemma lemma_bytes_and_mod7(x:bv64) ensures bv64and(x, 0x1_0000_0000_0000_00 - 1) == bv64mod(x, 0x1_0000_0000_0000_00) { reveal_bv64and(); reveal_bv64mod(); }

lemma lemma_bytes_and_mod(x:bv64, y:bv64, z:bv64)
    requires 0 <= y < 8
    requires 0 <= bv64shl(y, 3) < 64 ==> z == bv64shl(1, bv64shl(y, 3))
    ensures  0 <= bv64shl(y, 3) < 64
    ensures  z != 0
    ensures  bv64and(x, bv64sub(z, 1)) == bv64mod(x, z)
{
    reveal_bv64sub();
    lemma_bytes_shift_constants();
    lemma_bytes_and_mod0(x);
    lemma_bytes_and_mod1(x);
    lemma_bytes_and_mod2(x);
    lemma_bytes_and_mod3(x);
    lemma_bytes_and_mod4(x);
    lemma_bytes_and_mod5(x);
    lemma_bytes_and_mod6(x);
    lemma_bytes_and_mod7(x);
}

lemma{:fuel power2, 10} lemma_bytes_power2()
    ensures power2(0) == 0x1
    ensures power2(8) == 0x1_00
    ensures power2(16) == 0x1_0000
    ensures power2(24) == 0x1_0000_00
    ensures power2(32) == 0x1_0000_0000
    ensures power2(40) == 0x1_0000_0000_00
    ensures power2(48) == 0x1_0000_0000_0000
    ensures power2(56) == 0x1_0000_0000_0000_00
{
}

lemma lemma_bytes_shift_power2(y:bv64)
    requires 0 <= y < 8
    ensures  0 <= bv64shl(y, 3) < 64
    ensures  power2(U64(bv64shl(y, 3))) == U64(bv64shl(1, bv64shl(y, 3)))
{
    lemma_bytes_shift_constants();
    lemma_bytes_power2();
    reveal_U64();
}


} // end module
