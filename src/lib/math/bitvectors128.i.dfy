include "../util/types.s.dfy"
include "../util/operations.s.dfy"
include "bitvectors64.s.dfy"
include "bitvectors128.s.dfy"

module bitvectors128_i
{
import opened types_s
import opened operations_s
import opened bitvectors64_s
import opened bitvectors128_s

// zero-extend
function{:opaque} bv128_64(x:bv64):bv128 { x as bv128 }

// concatenate (REVIEW: it would be nice to use Boogie's built-in bitvector concatenation operator)
function{:opaque} bv128_64_64(x1:bv64, x0:bv64):bv128
{
    bv128or(bv128shl(bv128_64(x1), 64), bv128_64(x0))
}

function{:opaque} lowerUpper128(l:uint64, u:uint64):uint128 { l + 0x1_0000_0000_0000_0000 * u }

lemma lemma_bv128_64_shl_mul(x:bv64)
    ensures  bv128shl(bv128_64(x), 64) == bv128mul(bv128_64(x), 0x1_0000_0000_0000_0000)
{
    reveal_bv128_64();
    reveal_bv128shl();
    reveal_bv128mul();
}

lemma lemma_bv128_64_64_add_shl(x0:bv64, x1:bv64)
    ensures  bv128_64_64(x1, x0) == bv128add(bv128shl(bv128_64(x1), 64), bv128_64(x0))
{
    reveal_bv128_64();
    reveal_bv128shl();
    reveal_bv128add();
    reveal_bv128or();
    reveal_bv128_64_64();
}

lemma lemma_bv128_64_64_add_mul(x0:bv64, x1:bv64)
    ensures  bv128_64_64(x1, x0) == bv128add(bv128mul(bv128_64(x1), 0x1_0000_0000_0000_0000), bv128_64(x0))
{
    lemma_bv128_64_shl_mul(x1);
    lemma_bv128_64_64_add_shl(x0, x1);
}

lemma lemma_B128_B64(x:uint64)
    ensures  B128(x) == bv128_64(B64(x))
{
    assert B64(x) as uint64 == (B64(x) as bv128) as uint128;
    calc ==>
    {
        B64(x) as uint64 == (B64(x) as bv128) as uint128; { reveal_U64(); reveal_bv128_64(); reveal_U128(); }
        U64(B64(x)) == U128(bv128_64(B64(x)));            { lemma_U64(x); }
        x == U128(bv128_64(B64(x)));                      { lemma_B128(bv128_64(B64(x))); }
        B128(x) == bv128_64(B64(x));
    }
}

lemma lemma_bv128_lowerUpper_helper1(x1:uint64)
    ensures  mod2_128(x1 * 0x1_0000_0000_0000_0000) == x1 * 0x1_0000_0000_0000_0000
{
    reveal_mod2_128();
}

lemma lemma_bv128_lowerUpper_helper(x0:uint64, x1:uint64)
    ensures  lowerUpper128(x0, x1) == mod2_128(mod2_128(x1 * 0x1_0000_0000_0000_0000) + x0)
{
    calc
    {
        mod2_128(mod2_128(x1 * 0x1_0000_0000_0000_0000) + x0); { lemma_bv128_lowerUpper_helper1(x1); }
        mod2_128(x1 * 0x1_0000_0000_0000_0000 + x0);           { reveal_mod2_128(); }
        x1 * 0x1_0000_0000_0000_0000 + x0;                     { reveal_lowerUpper128(); }
        lowerUpper128(x0, x1);
    }
}

lemma lemma_bv128_lowerUpper(x0:uint64, x1:uint64)
    ensures  lowerUpper128(x0, x1) == U128(bv128_64_64(B64(x1), B64(x0)))
{
    calc
    {
        bv128mul(bv128_64(B64(x1)), 0x1_0000_0000_0000_0000); { reveal_B128(); }
        bv128mul(bv128_64(B64(x1)), B128(0x1_0000_0000_0000_0000)); { lemma_B128_B64(x1); }
        bv128mul(B128(x1), B128(0x1_0000_0000_0000_0000));
            { lemma_B128(bv128mul(B128(x1), B128(0x1_0000_0000_0000_0000))); }
            { lemma_bv128mul(x1, 0x1_0000_0000_0000_0000); }
        B128(mod2_128(x1 * 0x1_0000_0000_0000_0000));
    }
    calc
    {
        U128(bv128_64_64(B64(x1), B64(x0))); { lemma_bv128_64_64_add_mul(B64(x0), B64(x1)); }
        U128(bv128add(bv128mul(bv128_64(B64(x1)), 0x1_0000_0000_0000_0000), bv128_64(B64(x0))));
        U128(bv128add(B128(mod2_128(x1 * 0x1_0000_0000_0000_0000)), bv128_64(B64(x0)))); { lemma_B128_B64(x0); }
        U128(bv128add(B128(mod2_128(x1 * 0x1_0000_0000_0000_0000)), B128(x0)));
            { lemma_bv128add(mod2_128(x1 * 0x1_0000_0000_0000_0000), x0); }
        mod2_128(mod2_128(x1 * 0x1_0000_0000_0000_0000) + x0); { lemma_bv128_lowerUpper_helper(x0, x1); }
        lowerUpper128(x0, x1);
    }
}

lemma lemma_bv128_lowerUpper_B128(x0:uint64, x1:uint64)
    ensures  B128(lowerUpper128(x0, x1)) == bv128_64_64(B64(x1), B64(x0))
{
    lemma_bv128_lowerUpper(x0, x1);
    lemma_B128(bv128_64_64(B64(x1), B64(x0)));
}

} // end module
