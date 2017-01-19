include "power.s.dfy"
include "mul.i.dfy"

module Math__power_i {
import opened Math__power_s
import opened Math__mul_i

//-lemma lemma_mul_passes_harmlessly_through_mod(
//-    ensures mul(x,y) % m == mul(x

lemma lemma_power_0(b:int)
    ensures power(b,0) == 1;
{
    reveal_power();
}

lemma lemma_power_1(b:int)
    ensures power(b,1) == b;
{
    calc {
        power(b,1);
            { reveal_power(); }
        b*power(b,0);
            { lemma_power_0(b); }
        b*1;
            { lemma_mul_basics_forall(); }
        b;
    }
}

lemma lemma_0_power(e:nat)
    requires e > 0;
    ensures power(0,e) == 0;
{
    reveal_power();
    lemma_mul_basics_forall();
    if (e != 1)
    {
        lemma_0_power(e - 1);
    }
}

lemma lemma_1_power(e:nat)
    ensures power(1,e) == 1;
{
    reveal_power();
    lemma_mul_basics_forall();
    if (e != 0)
    {
        lemma_1_power(e - 1);
    }
}

lemma lemma_power_adds(b:int, e1:nat, e2:nat)
    decreases e1;
    ensures power(b,e1)*power(b,e2) == power(b,e1+e2);
{
    if (e1==0)
    {
        calc {
            power(b,e1)*power(b,e2);
                { lemma_power_0(b); }
            1*power(b,e2);
                { lemma_mul_basics_forall(); }
            power(b,0+e2);
        }
    }
    else
    {
        calc {
            power(b,e1)*power(b,e2);
                { reveal_power(); }
            (b*power(b,e1-1))*power(b,e2);
                { lemma_mul_is_associative_forall(); }
            b*(power(b,e1-1)*power(b,e2));
                { lemma_power_adds(b, e1-1, e2); }
            b*power(b,e1-1+e2);
                { reveal_power(); }
            power(b,e1+e2);
        }
    }
}

lemma lemma_power_multiplies(a:int,b:nat,c:nat)
    decreases c;
    ensures 0<=b*c;
    ensures power(a,b*c) == power(power(a,b),c);
{
    lemma_mul_nonnegative(b,c);
    if (0==c)
    {
        lemma_mul_basics_forall();
        calc {
            power(a,b*c);
                { lemma_power_0(a); }
            1;
                { lemma_power_0(power(a,b)); }
            power(power(a,b),c);
        }
    }
    else
    {
        calc {
            b*c - b;
                { lemma_mul_basics_forall(); }
            b*c - mul(b,1);
                { lemma_mul_is_distributive_forall(); }
            b*(c-1);
        }
        lemma_mul_nonnegative(b,c-1);
        assert 0 <= b*c-b;

        calc {
            power(a,b*c);
            power(a,b+b*c-b);
                { lemma_power_adds(a,b,b*c-b); }
            power(a,b)*power(a,b*c-b);
            power(a,b)*power(a,b*(c-1));
                { lemma_power_multiplies(a,b,c-1); }
            power(a,b)*power(power(a,b),c-1);
                { reveal_power(); }
            power(power(a,b),c);
        }
    }
}

lemma lemma_power_distributes(a:int, b:int, e:nat)
    decreases e;
    ensures power(a*b, e) == power(a, e) * power(b, e);
{
    reveal_power();
    lemma_mul_basics_forall();
    if (e > 0)
    {
        calc {
            power(a*b, e);
            (a*b) * power(a*b, e - 1);
            { lemma_power_distributes(a, b, e - 1); }
            (a*b) * (power(a, e - 1) * power(b, e - 1));
            { lemma_mul_is_associative_forall(); lemma_mul_is_commutative_forall(); }
            (a*power(a, e - 1)) * (b*power(b, e - 1));
            power(a,e) * power(b,e);
        }
        lemma_mul_is_distributive_forall();
    }
}

lemma lemma_power_auto()
    ensures  forall x:int {:trigger power(x, 0)} :: power(x, 0) == 1;
    ensures  forall x:int {:trigger power(x, 1)} :: power(x, 1) == x;
    ensures  forall x:int, y:int {:trigger power(x, y)} :: y == 0 ==> power(x, y) == 1;
    ensures  forall x:int, y:int {:trigger power(x, y)} :: y == 1 ==> power(x, y) == x;
    ensures  forall x:int, y:int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y;
    ensures  forall x:int, y:int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y;
    ensures  forall x:int, y:nat, z:nat {:trigger power(x, y + z)} :: power(x, y + z) == power(x, y) * power(x, z);
    ensures  forall x:int, y:nat, z:nat {:trigger power(x, y - z)} :: y >= z ==> power(x, y - z) * power(x, z) == power(x, y);
    ensures  forall x:int, y:int, z:nat {:trigger power(x * y, z)} :: power(x * y, z) == power(x, z) * power(y, z);
{
    forall x:int
        ensures power(x, 0) == 1;
        ensures power(x, 1) == x;
    {
        lemma_power_0(x);
        lemma_power_1(x);
    }
    forall x:int, y:int, z:nat
        ensures power(x * y, z) == power(x, z) * power(y, z);
    {
        lemma_power_distributes(x, y, z);
    }
    forall x:int, y:nat, z:nat
        ensures power(x, y + z) == power(x, y) * power(x, z);
    {
        lemma_power_adds(x, y, z);
    }
    forall x:int, y:nat, z:nat {:trigger power(x, y-z)} | y >= z
        ensures power(x, y-z) * power(x, z) == power(x, y);
    {
        lemma_power_adds(x, y-z, z);
    }
    lemma_mul_auto();
    lemma_mul_increases_forall();
    lemma_mul_strictly_increases_forall();
}

lemma lemma_power_positive(b:int, e:nat)
    requires 0<b;
    ensures 0<power(b,e);
{
    lemma_power_auto();
    lemma_mul_auto_induction(e, imap u :: 0 <= u ==> 0 < power(b, u));
}

lemma lemma_power_increases(b:nat,e1:nat,e2:nat)
    requires 0<b;
    requires e1 <= e2;
    ensures power(b,e1) <= power(b,e2);
{
    if e2 == e1 {
        return;
    }
    else {
        lemma_power_increases(b, e1, e2-1);
        calc {
            power(b, e2);
              { reveal_power(); }
            b * power(b, e2 - 1);
            >= { lemma_power_positive(b, e1); lemma_power_positive(b, e2-1); lemma_mul_upper_bound(b, b, power(b, e1), power(b, e2-1)); }
            b * power(b, e1);
            >= { lemma_power_positive(b, e1); lemma_mul_nonnegative(b, power(b, e1)); lemma_mul_ordering(b, power(b, e1)); }
            power(b, e1);
        }
    }
}

lemma lemma_power_strictly_increases(b:nat,e1:nat,e2:nat)
    requires 1<b;
    requires e1 < e2;
    ensures power(b,e1) < power(b,e2);
{
    lemma_power_increases(b, e1, e2-1);
    reveal_power();
    calc {
        power(b, e2);
          { reveal_power(); }
        b * power(b, e2 - 1);
        >= { lemma_power_positive(b, e1); lemma_power_positive(b, e2-1); lemma_mul_upper_bound(b, b, power(b, e1), power(b, e2-1)); }
        b * power(b, e1);
        > { lemma_power_positive(b, e1); lemma_mul_strict_inequality_forall(); }
        1 * power(b, e1);
        power(b, e1);
    }
}

lemma lemma_square_is_power_2(x:nat)
    ensures power(x,2) == x*x;
{
    reveal_power();
}

} 
