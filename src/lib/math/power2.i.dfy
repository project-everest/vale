include "power2.s.dfy"
include "power.i.dfy"
include "div.i.dfy"

module Math__power2_i {
import opened Math__power2_s
import opened Math__power_i
import opened Math__div_i

lemma lemma_power2_is_power_2_general()
    ensures forall x:nat :: power2(x) == power(2,x);
{
    forall x:nat
        ensures power2(x) == power(2,x);
    {
        lemma_power2_is_power_2(x);
    }
}

lemma lemma_power2_is_power_2(x:nat)
    ensures power2(x) == power(2, x);
{
    reveal_power();
    reveal_power2();
    if (x != 0) {
        lemma_power2_is_power_2(x - 1);
    }
}

lemma lemma_power2_auto()
    ensures  power2(0) == 1;
    ensures  power2(1) == 2;
    ensures  forall x:nat, y:nat {:trigger power2(x + y)} :: power2(x + y) == power2(x) * power2(y);
    ensures  forall x:nat, y:nat {:trigger power2(x - y)} :: x >= y ==> power2(x - y) * power2(y) == power2(x);
    ensures  forall x:nat, y:nat {:trigger x * y} :: y == 2 ==> x * y == x + x;
{
    lemma_power2_is_power_2_general();
    lemma_power_auto();
}

//////////////////////////////////////////////////////////////////////////////

lemma lemma_power2_strictly_increases(e1: int, e2: int)
    requires 0 <= e1 < e2;
    ensures power2(e1) < power2(e2);
{
    lemma_power2_auto();
    lemma_mul_auto_induction(e2 - e1, imap e :: 0 < e ==> power2(e1) < power2(e1 + e));
}

lemma lemma_power2_increases(e1: int, e2: int)
    requires 0 <= e1 <= e2;
    ensures power2(e1) <= power2(e2);
{
    lemma_power2_auto();
    lemma_mul_auto_induction(e2 - e1, imap e :: 0 <= e ==> power2(e1) <= power2(e1 + e));
}

lemma lemma_power2_positive()
    ensures forall e:nat :: 0 < power2(e);
{
    lemma_power2_auto();
    lemma_mul_auto_induction_forall(imap e :: 0 <= e ==> 0 < power2(e));
}

lemma lemma_power2_nonzero_bigger_than_one()
    ensures forall e:nat :: 0<e ==> 1 < power2(e);
{
    lemma_power2_auto();
    var f := imap e :: (0 < e ==> 1 < power2(e));
    lemma_mul_auto_induction_forall(f);
    assert forall e :: f[e] <==> (0 < e ==> 1 < power2(e));
}

lemma lemma_power2_strictly_increases_converse(e1: int, e2: int)
    requires 0 <= e1;
    requires 0 < e2;
    requires power2(e1) < power2(e2);
    ensures e1 < e2;
{
    if (e1 >= e2)
    {
        lemma_power2_increases(e2, e1);
        assert false;
    }
}

lemma lemma_power2_increases_converse(e1: int, e2: int)
    requires 0 < e1;
    requires 0 < e2;
    requires power2(e1) <= power2(e2);
    ensures e1 <= e2;
{
    if (e1 > e2) {
        lemma_power2_strictly_increases(e2, e1);
        assert false;
    }
}

lemma lemma_power2_adds(e1:nat, e2:nat)
    decreases e2;
    ensures power2(e1 + e2) == power2(e1) * power2(e2);
{
    lemma_power2_auto();
}

lemma lemma_power2_div_is_sub(x:int, y:int)
    requires 0 <= x <= y;
    ensures power2(y - x) == power2(y) / power2(x) >= 0;
{
    calc {
        power2(y) / power2(x);
        { lemma_power2_adds(y-x, x); }
        (power2(y-x)*power2(x)) / power2(x);
        { lemma_div_by_multiple(power2(y-x), power2(x)); }
        power2(y-x);
    }
}

lemma lemma_2toX32()
    ensures power2(0) == 0x1;
    ensures power2(1) == 0x2;
    ensures power2(2) == 0x4;
    ensures power2(3) == 0x8;
    ensures power2(4) == 0x10;
    ensures power2(5) == 0x20;
    ensures power2(6) == 0x40;
    ensures power2(7) == 0x80;
    ensures power2(8) == 0x100;
    ensures power2(9) == 0x200;
    ensures power2(10) == 0x400;
    ensures power2(11) == 0x800;
    ensures power2(12) == 0x1000;
    ensures power2(13) == 0x2000;
    ensures power2(14) == 0x4000;
    ensures power2(15) == 0x8000;
    ensures power2(16) == 0x10000;
    ensures power2(17) == 0x20000;
    ensures power2(18) == 0x40000;
    ensures power2(19) == 0x80000;
    ensures power2(20) == 0x100000;
    ensures power2(21) == 0x200000;
    ensures power2(22) == 0x400000;
    ensures power2(23) == 0x800000;
    ensures power2(24) == 0x1000000;
    ensures power2(25) == 0x2000000;
    ensures power2(26) == 0x4000000;
    ensures power2(27) == 0x8000000;
    ensures power2(28) == 0x10000000;
    ensures power2(29) == 0x20000000;
    ensures power2(30) == 0x40000000;
    ensures power2(31) == 0x80000000;
    ensures power2(32) == 0x100000000;
{
    reveal_power2();
}

lemma lemma_2toX()
    ensures power2(64) == 18446744073709551616;
    ensures power2(60) == 1152921504606846976;
    ensures power2(32) == 4294967296;
    ensures power2(24) == 16777216;
    ensures power2(19) == 524288;
    ensures power2(16) == 65536;
    ensures power2(8) ==  256;
{
    lemma_2to32();
    lemma_2to64();
}

lemma lemma_power2_add8(n:int)
    requires n >= 0;
    ensures power2(n + 1) == 2 * power2(n);
    ensures power2(n + 2) == 4 * power2(n);
    ensures power2(n + 3) == 8 * power2(n);
    ensures power2(n + 4) == 16 * power2(n);
    ensures power2(n + 5) == 32 * power2(n);
    ensures power2(n + 6) == 64 * power2(n);
    ensures power2(n + 7) == 128 * power2(n);
    ensures power2(n + 8) == 256 * power2(n);
{
    reveal_power2();
}

lemma lemma_2to32()
    ensures power2(32) == 4294967296;
    ensures power2(24) == 16777216;
    ensures power2(19) == 524288;
    ensures power2(16) == 65536;
    ensures power2(8)  == 256;
    ensures power2(0) == 1;
{
    lemma_2toX32();
}

lemma lemma_2to64()
    ensures power2(64) == 18446744073709551616;
    ensures power2(60) == 1152921504606846976;
{
    lemma_2to32();
    lemma_power2_add8(32);
    lemma_power2_add8(40);
    lemma_power2_add8(48);
    lemma_power2_add8(56);
}

lemma lemma_power2_0_is_1()
    ensures power2(0) == 1;
{
    reveal_power2();
}

lemma lemma_power2_1_is_2()
    ensures power2(1) == 2;
{
    reveal_power2();
}

lemma lemma_bit_count_is_unique(x:int, a:int, b:int)
    requires 0<a;
    requires 0<b;
    requires power2(a-1) <= x < power2(a);
    requires power2(b-1) <= x < power2(b);
    ensures a==b;
{
    if (a<b)
    {
        lemma_power2_increases(a,b-1);
        assert false;
    }
    if (b<a)
    {
        lemma_power2_increases(b,a-1);
        assert false;
    }
}

//-
//-////////////////////////////////////////////////////////////////////////////

/*
lemma lemma_word_to_bytes_unique_specific_power2_helper1(a:int, b:int)
    requires a % 256 == b % 256;
    requires (a / power2(8)) % 256 == (b / power2(8)) % 256;
    requires 0 <= a;
    requires 0 <= b;
    ensures  a % 65536 == b % 65536;
{
    var d := 256;
    var c := 256;
    assert d*c == 65536;
    lemma_2toX();

    calc {
      a % 65536;
      a % (d*c);
          { lemma_mod_breakdown(a,d,c); }
      d * ((a/d)%c) + a%d;
      d * ((b/d)%c) + b%d;
          { lemma_mod_breakdown(b,d,c); }
      b % (d*c);
      b % 65536;
    }
}

lemma lemma_word_to_bytes_unique_specific_power2_helper2(a:int, b:int)
    requires (a / power2(16)) % 256 == (b / power2(16)) % 256;
    requires a / power2(24) == b / power2(24);
    requires 0 <= a;
    requires 0 <= b;
    ensures  a / power2(16) == b / power2(16);
{
    var ap := a/power2(16);
    var bp := b/power2(16);
    var d := power2(8);

    lemma_2toX();
    lemma_mul_strictly_positive_forall();

    calc {
        ap/d;
            { lemma_div_denominator(a,power2(16),power2(8)); }
        a/(power2(16)*power2(8));
            { lemma_power2_adds(16,8); }
        a/power2(24);
        b/power2(24);
            { lemma_power2_adds(16,8); }
        b/(power2(16)*power2(8));
            { lemma_div_denominator(b,power2(16),power2(8)); }
        bp/d;
    }
    calc {
        a/power2(16);
        ap;
            { lemma_fundamental_div_mod(ap,d); }
        d*(ap/d)+ap%d;
        d*(bp/d)+bp%d;
            { lemma_fundamental_div_mod(bp,d); }
        bp;
        b/power2(16);
    }
}

lemma lemma_word_to_bytes_unique_specific_power2_helper3(a:int, b:int)
    requires a % 65536 == b % 65536;
    requires a / power2(16) == b / power2(16);
    requires 0 <= a;
    requires 0 <= b;
    ensures  a == b;
{
    lemma_2toX();
    lemma_fundamental_div_mod(a,65536);
    lemma_fundamental_div_mod(b,65536);
}

lemma lemma_word_to_bytes_unique_specific_power2(a:int, b:int)
    requires a % 256 == b % 256;
    requires (a / power2(8)) % 256 == (b / power2(8)) % 256;
    requires (a / power2(16)) % 256 == (b / power2(16)) % 256;
    requires a / power2(24) == b / power2(24);
    requires 0 <= a;
    requires 0 <= b;
    ensures  a == b;
{
    lemma_word_to_bytes_unique_specific_power2_helper1(a, b);
    lemma_word_to_bytes_unique_specific_power2_helper2(a, b);
    lemma_word_to_bytes_unique_specific_power2_helper3(a, b);
}
*/

lemma lemma_pull_out_powers_of_2(x:nat, y:nat, z:nat)
    ensures 0<=x*y;
    ensures 0<=y*z;
    ensures power(power2(x*y), z) == power(power2(x), y*z);
{
    lemma_mul_nonnegative(x,y);
    lemma_mul_nonnegative(y,z);
    lemma_power_positive(2,x);
    calc {
        power(power2(x*y), z);
            { lemma_power2_is_power_2(x*y); }
        power(power(2,x*y), z);
            { lemma_power_multiplies(2, x, y); }
        power(power(power(2,x),y), z);
            { lemma_power_multiplies(power(2,x), y, z); }
        power(power(2,x), y*z);
            { lemma_power2_is_power_2(x); }
        power(power2(x), y*z);
    }
}

lemma lemma_rebase_powers_of_2()
    ensures forall n:nat, e:nat {:trigger power(power2(n), e)} :: 0 <= n * e && power(power2(n), e) == power2(n * e);
{
    forall n:nat, e:nat
        ensures 0 <= n * e && power(power2(n), e) == power2(n * e);
    {
        lemma_pull_out_powers_of_2(1, n, e);
        lemma_power2_auto();
        lemma_power2_is_power_2_general();
    }
}

lemma lemma_mask_div_2(c:nat)
    requires 0<c;
    ensures (power2(c)-1)/2 == power2(c-1)-1;
{
    lemma_power2_auto();
    lemma_mul_auto_induction(c, imap u :: 0 < u ==> (power2(u)-1)/2 == power2(u-1)-1);
}

lemma lemma_power2_division_inequality(x:nat, p:nat, s:nat)
    requires s<=p;
    requires x<power2(p);
    ensures x/power2(s) < power2(p-s);
{
    calc ==> {
        x/power2(s) >= power2(p-s);
            { lemma_mul_inequality(power2(p-s), x/power2(s), power2(s)); }
        (x/power2(s))*power2(s) >= power2(p-s)*power2(s);
            { lemma_fundamental_div_mod(x, power2(s));
              lemma_mul_is_commutative_forall(); }
        x - x%power2(s) >= power2(p-s)*power2(s);
            { lemma_power2_adds(p-s, s); }
        x - x%power2(s) >= power2(p);
            { lemma_mod_properties(); }
        x >= power2(p);
        false;
    }
}

lemma lemma_power2_unfolding(a:nat, b:nat)
    ensures 0<=a*b;
    ensures power(power2(a), b) == power2(a*b);
{
    lemma_mul_nonnegative(a,b);
    lemma_power2_is_power_2(a);
    lemma_power_multiplies(2,a,b);
    lemma_power2_is_power_2(a*b);
}

function{:opaque} NatNumBits(n:nat):nat
    ensures NatNumBits(n) >= 0;
{
    if n == 0 then 0 else 1 + NatNumBits(n / 2)
}

lemma lemma_Power2BoundIsNatNumBits(c:nat, n:nat)
    ensures (((c>0) ==> (power2(c-1) <= n)) && (n < power2(c))) <==> c == NatNumBits(n);
{
    reveal_NatNumBits();
    reveal_power2();
    if (c > 0)
    {
        lemma_Power2BoundIsNatNumBits(c - 1, n / 2);
    }
    assert NatNumBits(n / 2) >= 0;
}



} 
