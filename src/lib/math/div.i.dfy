include "power.i.dfy"
include "mul.i.dfy"
include "div_def.i.dfy"
include "div_boogie.i.dfy"
include "div_nonlinear.i.dfy"
include "div_auto.i.dfy"
include "mod_auto.i.dfy"
include "mul_auto.i.dfy"
include "mul_nonlinear.i.dfy"

module Math__div_i {
import opened Math__power_i
import opened Math__mul_i
import opened Math__div_def_i
import opened Math__div_boogie_i
import opened Math__div_nonlinear_i
import opened Math__div_auto_i
import opened Math__mod_auto_i
import opened Math__mul_auto_i
import opened Math__power_s
import opened Math__mul_nonlinear_i

//-////////////////////////////////////////////////////////////////////////////
//-
//- Core div lemmas, with named arguments.
//-
//-////////////////////////////////////////////////////////////////////////////

lemma lemma_div_by_one_is_identity(x:int) {}

lemma lemma_div_basics(x:int)
    ensures x != 0 ==> 0 / x == 0;
    ensures x / 1 == x;
    ensures x!=0 ==> x / x == 1;
{
    if (x != 0) {
        lemma_div_by_self(x);
        lemma_div_of_0(x);
    }
}


lemma lemma_small_div_converse()
    ensures forall x, d {:trigger x/d} :: 0<=x && 0<d && x/d==0 ==> x < d;
{
    forall x, d | 0<=x && 0<d && x/d==0 ensures x < d;
    {
        lemma_div_auto_induction(d, x, imap u :: 0<=u && 0<d && u/d==0 ==> u < d);
    }
}


lemma lemma_div_is_ordered_by_denominator(x:int, y:int, z:int)
    requires x >= 0;
    requires 1 <= y <= z;
    ensures x / y >= x / z;
    decreases x;
{
    lemma_div_is_div_recursive_forall();
    assert forall u:int, d:int {:trigger u / d}{:trigger my_div_recursive(u, d)} :: d > 0 ==> my_div_recursive(u, d) == u / d;

    if (x < z)
    {
        lemma_div_is_ordered(0, x, y);
    }
    else
    {
        lemma_div_is_ordered(x-z, x-y, y);
        lemma_div_is_ordered_by_denominator(x-z, y, z);
    }
}

lemma lemma_div_is_strictly_ordered_by_denominator(x:int, d:int)
    requires 0 < x;
    requires 1 < d;
    ensures x/d < x;
    decreases x;
{
    lemma_div_auto_induction(d, x, imap u :: 0 < u ==> u / d < u);
}

lemma lemma_dividing_sums(a:int, b:int, d:int, R:int)
    requires 0<d;
    requires R == a%d + b%d - (a+b)%d;
    ensures d*((a+b)/d) - R == d*(a/d) + d*(b/d);
{
    calc ==> {
        a%d + b%d == R + (a+b)%d;
        (a+b)-(a+b)%d - R == a-(a%d) + b - (b%d);
            {
                lemma_fundamental_div_mod(a+b,d);
                lemma_fundamental_div_mod(a,d);
                lemma_fundamental_div_mod(b,d);
            }
        d*((a+b)/d) - R == d*(a/d) + d*(b/d);
    }
}


//-static lemma lemma_negative_divisor(x:int, d:int)
//-    requires d < 0;
//-    ensures x / (-1*d) == -1*(x / d); 
//-{
//-    var q := x / (-1*d);
//-    var r := x % (-1*d);
//-
//-    calc {
//-        x;
//-            { lemma_fundamental_div_mod(x, -1*d); }
//-        q * (-1*d) + r;
//-            { lemma_mul_is_associative(q, -1, d); }
//-        (q*-1)*d + r;
//-            { lemma_mul_is_commutative(q, -1); }
//-        (-q) * d + r;
//-    }
//-    lemma_mod_range(x, -1*d);
//-    lemma_fundamental_div_mod_converse(x, d, -q, r);
//-    assert x / d == -q;
//-    assert -1*(x/d) == q;
//-}


lemma lemma_div_pos_is_pos(x:int, divisor:int)
    requires 0 <= x;
    requires 0 < divisor;
    ensures x / divisor >= 0;
{
    lemma_div_auto_induction(divisor, x, imap u :: 0 <= u ==> u / divisor >= 0);
}
//-////////////////////////////////////////////////////////////////////////////
//-
//- Forall lemmas: these restate the core lemmas with foralls,
//- so callers needn't name the specific expressions to manipulate.
//-
//- These are all boilerplate transformations of args/requires/ensures
//- into forall args :: requires ==> ensures, with a correpsonding
//- mechanically generated forall proof that invokes the core lemma.
//-
//-////////////////////////////////////////////////////////////////////////////

lemma lemma_div_basics_forall()
    ensures forall x {:trigger 0 / x} :: x != 0 ==> 0 / x == 0;
    ensures forall x {:trigger x / 1} :: x / 1 == x;
    ensures forall x, y {:trigger x/y} :: x >= 0 && y > 0 ==> x/y >= 0;
    ensures forall x, y {:trigger x/y} :: x >= 0 && y > 0 ==> x/y <= x;
{
    forall (x:int)
        ensures x != 0 ==> 0 / x == 0;
        ensures x / 1 == x;
    {
        lemma_div_basics(x);
    }
    forall x:int, y:int | x >= 0 && y > 0
        ensures x / y >= 0;
        ensures x / y <= x;
    {
        lemma_div_pos_is_pos(x, y);
        lemma_div_is_ordered_by_denominator(x, 1, y);
    }
}

//////////////////////////////////////////////////////////////////////////////
//





lemma lemma_div_neg_neg(x:int, d:int)
    requires d > 0;
    ensures x/d == -((-x+d-1)/d);
{
    lemma_div_auto(d);
}


//-
//-////////////////////////////////////////////////////////////////////////////


/*******************************
 *  Useful lemmas about mod    *
 *******************************/

lemma lemma_mod_basics()
    ensures forall m:int {:trigger m % m} :: m > 0 ==> m % m == 0;
    ensures forall x:int, m:int {:trigger (x%m) % m} :: m > 0 ==> (x%m) % m == x%m;
{
    forall m:int | m > 0
        ensures m % m == 0;
    {
        lemma_mod_auto(m);
    }
    forall x:int, m:int | m > 0
        ensures (x % m) % m == x % m;
    {
        lemma_mod_auto(m);
    }
}

lemma lemma_mul_mod_noop_left(x:int, y:int, m:int)
    requires 0 < m;
    ensures (x % m)*y % m == x*y % m;
{
    lemma_mod_auto(m);
    lemma_mul_auto_induction(y, imap u :: ((x % m)*u) % m == (x*u) % m);
}


lemma lemma_mod_properties()
    ensures forall m:int {:trigger m % m} :: m > 0 ==> m % m == 0;
    ensures forall x:int, m:int {:trigger (x%m) % m} :: m > 0 ==> (x%m) % m == x%m;
    ensures forall x:int, m:int {:trigger x%m} :: m > 0 ==> 0 <= x%m < m;
{
    lemma_mod_basics();

    forall x:int, m:int | m > 0
        ensures m > 0 ==> 0 <= x%m < m;
    {
        lemma_mod_auto(m);
    }
}

lemma lemma_mod_decreases(x:nat, d:nat)
    requires 0<d;
    ensures x%d <= x;
{
    lemma_mod_auto(d);
}

lemma lemma_mod_add_multiples_vanish(b:int, m:int)
    requires 0 < m;
    ensures (m + b) % m == b % m;
{
    lemma_mod_auto(m);
}

lemma lemma_mod_sub_multiples_vanish(b:int, m:int)
    requires 0 < m;
    ensures (-m + b) % m == b % m;
{
    lemma_mod_auto(m);
}

lemma lemma_mod_multiples_vanish(a:int, b:int, m:int)
    decreases if a>0 then a else -a;
    requires 0 < m;
    ensures (m*a + b) % m == b % m;
{
    lemma_mod_auto(m);
    lemma_mul_auto_induction(a, imap u :: (m*u + b) % m == b % m);
}

lemma lemma_add_mod_noop(x:int, y:int, m:int)
    requires 0 < m;
    ensures ((x % m) + (y % m)) % m == (x+y) % m;
{
    lemma_mod_auto(m);
}

lemma lemma_add_mod_noop_right(x:int, y:int, m:int)
    requires 0 < m;
    ensures (x + (y % m)) % m == (x+y) % m;
{
    lemma_mod_auto(m);
}

lemma lemma_mod_equivalence(x:int, y:int, m:int)
    requires 0 < m;
    ensures x % m == y % m <==> (x - y) % m == 0;
{
    lemma_mod_auto(m);
}

lemma lemma_sub_mod_noop(x:int, y:int, m:int)
    requires 0 < m;
    ensures ((x % m) - (y % m)) % m == (x-y) % m;
{
    lemma_mod_auto(m);
}

lemma lemma_sub_mod_noop_right(x:int, y:int, m:int)
    requires 0 < m;
    ensures (x - (y % m)) % m == (x-y) % m;
{
    lemma_mod_auto(m);
}

lemma lemma_mod_adds(a:int, b:int, d:int)
    requires 0<d;
    ensures a%d + b%d == (a+b)%d + d*((a%d + b%d)/d);
    ensures (a%d + b%d) < d ==> a%d + b%d == (a+b)%d;
{
    lemma_mul_auto();
    lemma_div_auto(d);
}

lemma {:timeLimitMultiplier 2} lemma_mod_neg_neg(x:int, d:int)
    requires d > 0;
    ensures x%d == (x*(1-d))%d;
{
    forall ensures (x - x * d) % d == x % d;
    {
        lemma_mod_auto(d);
        var f := imap i :: (x - i * d) % d == x % d;
        assert  MulAuto() ==> f[0]
                        && (forall i {:trigger TMulAutoLe(0, i)} :: TMulAutoLe(0, i) && f[i] ==> f[i + 1])
                        && (forall i {:trigger TMulAutoLe(i, 0)} :: TMulAutoLe(i, 0) && f[i] ==> f[i - 1]);
        lemma_mul_auto_induction(x, imap i :: (x - i * d) % d == x % d);
    }
    lemma_mul_auto();
}

lemma lemma_fundamental_div_mod_converse(x:int, d:int, q:int, r:int)
    requires d != 0;
    requires 0 <= r < d;
    requires x == q * d + r;
    ensures q == x/d;
    ensures r == x%d;
{
    lemma_div_auto(d);
    lemma_mul_auto_induction(q, imap u :: u == (u * d + r) / d);
    lemma_mul_auto_induction(q, imap u :: r == (u * d + r) % d);
}

lemma lemma_mod_pos_bound(x:int, m:int)
    decreases x;
    requires 0 <= x;
    requires 0 < m;
    ensures  0 <= x%m < m;
{
    lemma_mod_auto(m);
}

lemma lemma_mul_mod_noop_right(x:int, y:int, m:int)
    requires 0 < m;
    ensures x*(y % m) % m == (x*y) % m;
{
    lemma_mod_auto(m);
    lemma_mul_auto_induction(x, imap u :: u*(y % m) % m == (u*y) % m);
}

lemma lemma_mul_mod_noop_general(x:int, y:int, m:int)
    requires 0 < m;
    ensures ((x % m) * y      ) % m == (x * y) % m;
    ensures ( x      * (y % m)) % m == (x * y) % m;
    ensures ((x % m) * (y % m)) % m == (x * y) % m;
{
    lemma_mod_properties();
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
}


lemma lemma_mul_mod_noop(x:int, y:int, m:int)
    requires 0 < m;
    ensures (x % m) * (y % m) % m == (x*y) % m;
{
    lemma_mul_mod_noop_general(x, y, m);
}

lemma lemma_power_mod_noop(b:int, e:nat, m:int)
    decreases e;
    requires 0 < m;
    ensures power(b % m, e) % m == power(b, e) % m;
{
    reveal_power();
    lemma_mod_properties();
    if (e > 0)
    {
        calc {
            power(b % m, e) % m;
            ((b % m) * power(b % m, e - 1)) % m;
            { lemma_mul_mod_noop_general(b, power(b % m, e - 1), m); }
            ((b % m) * (power(b % m, e - 1) % m) % m) % m;
            { lemma_power_mod_noop(b, e - 1, m); }
            ((b % m) * (power(b, e - 1) % m) % m) % m;
            { lemma_mul_mod_noop_general(b, power(b, e - 1), m); }
            (b * (power(b, e - 1)) % m) % m;
            (b * (power(b, e - 1))) % m;
            power(b, e) % m;
        }
    }
}

lemma lemma_mod_subtraction(x:nat, s:nat, d:nat)
    requires 0<d;
    requires 0<=s<=x%d;
    ensures x%d - s%d == (x-s)%d;
{
    lemma_mod_auto(d);
}

lemma lemma_mod_ordering(x:nat, k:nat, d:nat)
    requires 1<d;
    requires 0<k;
    ensures 0<d*k;
    ensures x%d <= x%(d*k);
{
    lemma_mul_strictly_increases(d,k);
    calc {
        x%d + d*(x/d);
            { lemma_fundamental_div_mod(x,d); }
        x;
            { lemma_fundamental_div_mod(x,d*k); }
        x%(d*k) + (d*k)*(x/(d*k));
            { lemma_mul_is_associative_forall(); }
        x%(d*k) + d*(k*(x/(d*k)));
    }
    calc {
        x%d;
            { lemma_mod_properties(); }
        (x%d) % d;
            { lemma_mod_multiples_vanish(x/d - k*(x/(d*k)), x%d, d); }
        (x%d + d*(x/d - k*(x/(d*k)))) % d;
            { lemma_mul_is_distributive_sub_forall(); }
        (x%d + d*(x/d) - d*(k*(x/(d*k)))) % d;
        (x%(d*k)) % d;
        <= {
            lemma_mod_properties();
            lemma_mod_decreases(x%(d*k), d); }
        x%(d*k);
    }
}

lemma lemma_mod_multiples_basic(x:int, m:int)
    requires m > 0;
    ensures  (x * m) % m == 0;
{
    lemma_mod_auto(m);
    lemma_mul_auto_induction(x, imap u :: (u * m) % m == 0);
}

//-
//-////////////////////////////////////////////////////////////////////////////


/************************************************************
 *  Lemmas that depend on properties of both div and mod    *
 ************************************************************/

//-/////////////////////////////////////////////////////
//- Proof that div is recursive div
//-/////////////////////////////////////////////////////
lemma lemma_div_plus_one(x:int, d:int)
    requires d > 0;
    //-requires x >= 0;
    ensures 1 + x / d == (d + x) / d;
{
    lemma_div_auto(d);
}

lemma lemma_div_minus_one(x:int, d:int)
    requires d > 0;
    ensures -1 + x / d == (-d + x) / d;
{
    lemma_div_auto(d);
}

lemma lemma_mod_mod(x:int, a:int, b:int)
    requires 0<a;
    requires 0<b;
    ensures 0<a*b;
    ensures (x%(a*b))%a == x%a;
{
    lemma_mul_strictly_positive_forall();
    calc {
        x;
            { lemma_fundamental_div_mod(x, a*b); }
        (a*b)*(x/(a*b)) + x % (a*b);
            { lemma_mul_is_associative_forall(); }
        a*(b*(x/(a*b))) + x % (a*b);
            { lemma_fundamental_div_mod(x%(a*b), a); }
        a*(b*(x/(a*b))) + a*(x%(a*b)/a) + (x%(a*b))%a;
            { lemma_mul_is_distributive_forall(); }
        a*(b*(x/(a*b)) + x%(a*b)/a) + (x%(a*b))%a;
    }
    lemma_mod_properties();
    lemma_mul_is_commutative_forall();
    lemma_fundamental_div_mod_converse(x, a, b*(x/(a*b)) + x%(a*b)/a, (x%(a*b))%a);
}

lemma lemma_div_is_div_recursive(x:int, d:int)
    requires d > 0;
    ensures my_div_recursive(x, d) == x / d;
{
    lemma_div_auto_induction(d, x, imap u :: my_div_recursive(u, d) == u / d);
}

lemma lemma_div_is_div_recursive_forall()
    ensures forall x:int, d:int :: d > 0 ==> my_div_recursive(x, d) == x / d;
{
    forall x:int, d:int | d > 0
        ensures my_div_recursive(x, d) == x / d;
    {
        lemma_div_is_div_recursive(x, d);
    }
}

//-/////////////////////////////////////////////////////

//-/////////////////////////////////////////////////////
//- Proof that mod is recursive mod
//-/////////////////////////////////////////////////////

lemma lemma_mod_is_mod_recursive(x:int, m:int)
    requires m > 0;
    ensures my_mod_recursive(x, m) == x % m;
    decreases if x < 0 then -x + m else x;
{

    if x < 0 { 
        calc { 
            my_mod_recursive(x, m);
            my_mod_recursive(x + m, m);
                { lemma_mod_is_mod_recursive(x + m, m); }
            (x + m) % m;
                { lemma_add_mod_noop(x, m, m); } 
            ((x % m) + (m % m)) % m;
                { lemma_mod_basics(); }
            (x % m) % m;
                { lemma_mod_basics(); }
            x % m;
        }
    } else if x < m { 
        lemma_small_mod(x, m);
    } else {
        calc { 
            my_mod_recursive(x, m);
            my_mod_recursive(x - m, m);
                { lemma_mod_is_mod_recursive(x - m, m); }
            (x - m) % m;
                { lemma_sub_mod_noop(x, m, m); } 
            ((x % m) - (m % m)) % m;
                { lemma_mod_basics(); }
            (x % m) % m;
                { lemma_mod_basics(); }
            x % m;
        }
    }
}

lemma lemma_mod_is_mod_recursive_forall()
    ensures forall x:int, d:int :: d > 0 ==> my_mod_recursive(x, d) == x % d;
{
    forall x:int, d:int | d > 0
        ensures my_mod_recursive(x, d) == x % d;
    {
        lemma_mod_is_mod_recursive(x, d);
    }
}

//-/////////////////////////////////////////////////////


lemma lemma_basic_div(d:int)
    requires d > 0;
    ensures forall x {:trigger x / d} :: 0 <= x < d ==> x / d == 0;
{
    lemma_div_auto(d);
}

lemma lemma_div_is_ordered(x:int, y:int, z:int)
    requires x <= y;
    requires z > 0;
    ensures x / z <= y / z;
{
    lemma_div_auto_induction(z, x - y, imap xy :: xy <= 0 ==> (xy + y) / z <= y / z);
}

lemma lemma_div_decreases(x:int, d:int)
    requires 0<x;
    requires 1<d;
    ensures x/d < x;
{
    lemma_div_auto_induction(d, x, imap u :: 0<u ==> u/d < u);
}

lemma lemma_div_nonincreasing(x:int, d:int)
    requires 0<=x;
    requires 0<d;
    ensures x/d <= x;
{
    lemma_div_auto_induction(d, x, imap u :: 0<=u ==> u/d <= u);
}

lemma lemma_breakdown(a:int, b:int, c:int)
    requires 0<=a;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures a%(b*c) == b * ((a/b)%c) + a%b;
{
    lemma_mul_strictly_positive_forall();
    lemma_div_pos_is_pos(a,b);
    assert 0<=a/b;

//-    lemma_mod_properties();
//-    assert a%b < b;
//-    assert 1<c;
//-    calc {
//-        b;
//-        <    { lemma_mul_strictly_increases(c,b); }
//-        c*b;
//-            { lemma_mul_is_commutative_forall(); }
//-        b*c;
//-    }
//-    lemma_mod_properties();
//-    assert (a%b)%(b*c) < b;

    calc {
        (b*(a/b)) % (b*c) + (a%b) % (b*c);
        <=    { lemma_part_bound1(a, b, c); }
        b*(c-1) + (a%b) % (b*c);
        <    { lemma_part_bound2(a, b, c); }
        b*(c-1) + b;
            { lemma_mul_basics_forall(); }
        b*(c-1) + mul(b,1);
            { lemma_mul_is_distributive_forall(); }
        b*(c-1+1);
        b*c;
    }

    calc {
        a % (b*c);
            { lemma_fundamental_div_mod(a,b); }
        (b*(a/b)+a%b) % (b*c);
            {
                lemma_mod_properties();
                assert 0<=a%b;
                lemma_mul_nonnegative(b,a/b);
                assert (b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c;
                lemma_mod_adds(b*(a/b), a%b, b*c);
            }
        (b*(a/b)) % (b*c) + (a%b) % (b*c);
            {
                lemma_mod_properties();
                lemma_mul_increases(c,b);
                lemma_mul_is_commutative_forall();
                assert a%b<b<=b*c;
                lemma_small_mod(a%b,b*c);
                assert (a%b) % (b*c) == a%b;
            }
        (b*(a/b)) % (b*c) + a%b;
            { lemma_truncate_middle(a/b,b,c); }
        b * ((a/b)%c) + a%b;
    }
}

lemma lemma_remainder_upper(x:int, divisor:int)
    requires 0 <= x;
    requires 0 < divisor;
    ensures   x - divisor < x / divisor * divisor;
{
    lemma_mul_auto();
    lemma_div_auto_induction(divisor, x, imap u :: 0 <= u ==> u - divisor < u / divisor * divisor);
}

lemma lemma_remainder_lower(x:int, divisor:int)
    requires 0 <= x;
    requires 0 < divisor;
    ensures  x >= x / divisor * divisor;
{
    lemma_mul_auto();
    lemma_div_auto_induction(divisor, x, imap u :: 0 <= u ==> u >= u / divisor * divisor);
}

lemma lemma_remainder(x:int, divisor:int)
    requires 0 <= x;
    requires 0 < divisor;
    ensures  0 <= x - x / divisor * divisor < divisor;
{
    lemma_mul_auto();
    lemma_div_auto_induction(divisor, x, imap u :: 0 <= u - u / divisor * divisor < divisor);
}


lemma lemma_div_denominator(x:int,c:nat,d:nat)
    requires 0 <= x;
    requires 0<c;
    requires 0<d;
    ensures c * d != 0;
    ensures (x/c)/d == x / (c*d);
{
    lemma_mul_strictly_positive_forall();
    //-assert 0 < c*d;
    var R := x % (c*d);
    lemma_mod_properties();
    //-assert 0<=R;

    lemma_div_pos_is_pos(R,c);
    //-assert 0 <= R/c;
    if (R/c >= d) {
        lemma_fundamental_div_mod(R, c);
//-        assert R >= c*(R/c);
        lemma_mul_inequality(d, R/c, c);
        lemma_mul_is_commutative_forall();
//-        assert c*(R/c) >= c*d;
//-        assert R >= c*d;
        assert false;
    }
    assert R/c < d;

    lemma_mul_basics_forall();
    lemma_fundamental_div_mod_converse(R/c, d, 0, R/c);
    assert (R/c) % d == R/c;

    lemma_fundamental_div_mod(R, c);
    assert c*(R/c) + R%c == R;

    assert c*((R/c) % d) + R%c == R;

    var k := x/(c*d);
    lemma_fundamental_div_mod(x, c*d);
    assert x == (c*d)*(x/(c*d)) + x % (c*d);
    assert R == x - (c*d)*(x/(c*d));
    assert R == x - (c*d)*k;

    calc {
        c*((x/c)%d) + x%c;
            { lemma_mod_multiples_vanish(-k, x/c, d); lemma_mul_is_commutative_forall(); }
        c*((x/c+(-k)*d) % d) + x%c;
            { lemma_hoist_over_denominator(x, (-k)*d, c); }
        c*(((x+(((-k)*d)*c))/c) % d) + x%c;
            { lemma_mul_is_associative(-k,d,c); }
        c*(((x+((-k)*(d*c)))/c) % d) + x%c;
            { lemma_mul_unary_negation(k,d*c); }
        c*(((x+(-(k*(d*c))))/c) % d) + x%c;
            { lemma_mul_is_associative(k,d,c); }
        c*(((x+(-(k*d*c)))/c) % d) + x%c;
        c*(((x-k*d*c)/c) % d) + x%c;
            {
                lemma_mul_is_associative_forall();
                lemma_mul_is_commutative_forall();
            }
        c*((R/c) % d) + x%c;
        c*(R/c) + x%c;
            { lemma_fundamental_div_mod(R,c);
                assert R == c*(R/c) + R % c;
                lemma_mod_mod(x,c,d);
                assert R%c == x%c;
            }
        R;
            { lemma_mod_is_mod_recursive_forall(); }
        R%(c*d);
        (x-(c*d)*k) % (c*d);
            { lemma_mul_unary_negation(c*d,k); }
        (x+(c*d)*(-k)) % (c*d);
            { lemma_mod_multiples_vanish(-k, x, c*d); }
        x % (c*d);
    }
    calc ==> {
        c*(x/c) + x%c - R == c*(x/c) - c*((x/c)%d);
            { lemma_fundamental_div_mod(x,c); }
        x - R == c*(x/c) - c*((x/c)%d);
    }
    calc ==> {
        true;
            { lemma_fundamental_div_mod(x/c,d); }
        d*((x/c)/d) == x/c - ((x/c)%d);
        c*(d*((x/c)/d)) == c*(x/c - ((x/c)%d));
            { lemma_mul_is_associative_forall(); }
        (c*d)*((x/c)/d) == c*(x/c - ((x/c)%d));
            { lemma_mul_is_distributive_forall(); }
        (c*d)*((x/c)/d) == c*(x/c) - c*((x/c)%d);
        (c*d)*((x/c)/d) == x - R;
            { lemma_fundamental_div_mod(x, c*d); }
        (c*d)*((x/c)/d) == (c*d)*(x/(c*d)) + x%(c*d) - R;
        (c*d)*((x/c)/d) == (c*d)*(x/(c*d));
            { lemma_mul_one_to_one(c*d, (x/c)/d, x/(c*d)); }
        (x/c)/d == x/(c*d);
    }
}

lemma lemma_mul_hoist_inequality(x:int, y:int, z:int)
    requires 0 <= x;
    requires 0 < z;
    ensures x*(y/z) <= (x*y)/z;
{
    calc {
        (x*y)/z;
            { lemma_fundamental_div_mod(y, z); }
        (x*(z*(y/z)+y%z))/z;
            { lemma_mul_is_distributive_forall(); }
        (x*(z*(y/z))+x*(y%z))/z;
        >=  {
            lemma_mod_properties();
            lemma_mul_nonnegative(x, y%z);
            lemma_div_is_ordered(x*(z*(y/z)), x*(z*(y/z))+x*(y%z), z); }
        (x*(z*(y/z)))/z;
            { lemma_mul_is_associative_forall();
              lemma_mul_is_commutative_forall(); }
        (z*(x*(y/z)))/z;
            { lemma_div_multiples_vanish(x*(y/z), z); }
        x*(y/z);
    }
}

lemma lemma_indistinguishable_quotients(a:int, b:int, d:int)
    requires 0<d;
    requires 0 <= a - a%d <= b < a + d - a%d;
    ensures a/d == b/d;
{
    lemma_div_auto_induction(d, a - b, imap ab :: var u := ab + b; 0 <= u - u%d <= b < u + d - u%d ==> u/d == b/d);
}

lemma lemma_truncate_middle(x:int, b:int, c:int)
    requires 0<=x;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures (b*x)%(b*c) == b*(x%c);
{
    lemma_mul_strictly_positive_forall();
    lemma_mul_nonnegative_forall();
    calc {
        b*x;
            { lemma_fundamental_div_mod(b*x,b*c); }
        (b*c)*((b*x)/(b*c)) + (b*x)%(b*c);
            { lemma_div_denominator(b*x,b,c); }
        (b*c)*(((b*x)/b)/c) + (b*x)%(b*c);
            { lemma_mul_is_commutative_forall(); lemma_div_by_multiple(x,b); }
        (b*c)*(x/c) + (b*x)%(b*c);
    }
    calc ==> {
        true;
            { lemma_fundamental_div_mod(x,c); }
        x == c*(x/c) + x%c;
        b*x == b*(c*(x/c) + x%c);
            { lemma_mul_is_distributive_forall(); }
        b*x == b*(c*(x/c)) + b*(x%c);
            { lemma_mul_is_associative_forall(); }
        b*x == (b*c)*(x/c) + b*(x%c);
    }
}

lemma lemma_div_multiples_vanish_quotient(x:int, a:int, d:int)
    requires 0<x;
    requires 0<=a;
    requires 0<d;
    ensures 0 < x*d;
    ensures a/d == (x*a)/(x*d);
{
    lemma_mul_strictly_positive(x,d);
    calc {
        (x*a)/(x*d);
            {
                lemma_mul_nonnegative(x,a);
                lemma_div_denominator(x*a, x, d); }
        ((x*a)/x) / d;
            { lemma_div_multiples_vanish(a, x); }
        a / d;
    }
}

lemma lemma_round_down(a:int, r:int, d:int)
    requires 0<d;
    requires a%d == 0;
    requires 0<=r<d;
    ensures a==d*((a+r)/d);
{
    lemma_mul_auto();
    lemma_div_auto_induction(d, a, imap u :: u%d == 0 ==> u==d*((u+r)/d));
}


lemma lemma_div_multiples_vanish_fancy(x:int, b:int, d:int)
    requires 0<d;
    requires 0<=b<d;
    ensures (d*x + b)/d == x;
{
    lemma_div_auto(d);
    lemma_mul_auto_induction(x, imap u :: (d*u + b)/d == u);
}

lemma lemma_div_multiples_vanish(x:int, d:int)
    requires 0<d;
    ensures (d*x)/d == x;
{
    lemma_div_multiples_vanish_fancy(x, 0, d);
}

lemma lemma_div_by_multiple(b:int, d:int)
    requires 0 <= b;
    requires 0 < d;
    ensures  (b*d) / d == b;
{ 
    lemma_div_multiples_vanish(b,d);
}


lemma lemma_div_by_multiple_is_strongly_ordered(x:int, y:int, m:int, z:int)
    requires x < y;
    requires y == m * z;
    requires z > 0;
    ensures     x / z < y / z;
{
    lemma_mod_multiples_basic(m, z);
    lemma_div_auto_induction(z, y - x, imap yx :: var u := yx + x; x < u && u % z == 0 ==> x / z < u / z);
}

lemma lemma_multiply_divide_le(a:int, b:int, c:int)
    requires 0 < b;
    requires a <= b * c;
    ensures  a / b <= c;
{
    lemma_mod_multiples_basic(c, b);
    lemma_div_auto_induction(b, b * c - a, imap i :: 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b);
    lemma_div_multiples_vanish(c, b);
}

lemma lemma_multiply_divide_lt(a:int, b:int, c:int)
    requires 0 < b;
    requires a < b * c;
    ensures  a / b < c;
{
    lemma_mod_multiples_basic(c, b);
    lemma_div_auto_induction(b, b * c - a, imap i :: 0 < i && (i + a) % b == 0 ==> a / b < (i + a) / b);
    lemma_div_multiples_vanish(c, b);
}

lemma lemma_hoist_over_denominator(x:int, j:int, d:nat)
    requires 0<d;
    ensures x/d + j == (x+j*d) / d;
{
    lemma_div_auto(d);
    lemma_mul_auto_induction(j, imap u :: x/d + u == (x+u*d) / d);
}

lemma lemma_part_bound1(a:int, b:int, c:int)
    requires 0<=a;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures (b*(a/b) % (b*c)) <= b*(c-1);
{
    lemma_mul_strictly_positive_forall();
    calc {
        b*(a/b) % (b*c);
            { lemma_fundamental_div_mod(b*(a/b),b*c); }
        b*(a/b) - (b*c)*((b*(a/b))/(b*c));
            { lemma_mul_is_associative_forall(); }
        b*(a/b) - b*(c*((b*(a/b))/(b*c)));
            { lemma_mul_is_distributive_forall(); }
        b*((a/b) - (c*((b*(a/b))/(b*c))));
    }

    calc ==> {
        true;
            { lemma_mod_properties(); }
        b*(a/b) % (b*c) < b*c;
        b*((a/b) - (c*((b*(a/b))/(b*c)))) < b*c;
            { lemma_mul_is_commutative_forall(); lemma_mul_strict_inequality_converse_forall(); }
        ((a/b) - (c*((b*(a/b))/(b*c)))) < c;
        ((a/b) - (c*((b*(a/b))/(b*c)))) <= c-1;
            { lemma_mul_is_commutative_forall(); lemma_mul_inequality_forall(); }
        b*((a/b) - (c*((b*(a/b))/(b*c)))) <= b*(c-1);
        b*(a/b) % (b*c) <= b*(c-1);
    }
}

lemma lemma_part_bound2(a:int, b:int, c:int)
    requires 0<=a;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures (a%b)%(b*c) < b;
{
    lemma_mul_strictly_positive_forall();
    lemma_mod_properties();
    assert a%b < b;
    lemma_mul_increases_forall();
    lemma_mul_is_commutative_forall();
    assert b <= b * c;
    assert 0 <= a%b < b * c;
    lemma_mod_properties();
    lemma_small_mod(a%b,b*c);
    assert (a%b)%(b*c) == a%b;
}

lemma lemma_mod_breakdown(a:int, b:int, c:int)
    requires 0<=a;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures a%(b*c) == b * ((a/b)%c) + a%b;
{
    lemma_mul_strictly_positive_forall();
    lemma_div_pos_is_pos(a,b);
    assert 0<=a/b;

    calc {
        (b*(a/b)) % (b*c) + (a%b) % (b*c);
        <=    { lemma_part_bound1(a, b, c); }
        b*(c-1) + (a%b) % (b*c);
        <    { lemma_part_bound2(a, b, c); }
        b*(c-1) + b;
            { lemma_mul_basics_forall(); }
        b*(c-1) + mul(b,1);
            { lemma_mul_is_distributive_forall(); }
        b*(c-1+1);
        b*c;
    }

    calc {
        a % (b*c);
            { lemma_fundamental_div_mod(a,b); }
        (b*(a/b)+a%b) % (b*c);
            {
                lemma_mod_properties();
                assert 0<=a%b;
                lemma_mul_nonnegative(b,a/b);
                assert (b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c;
                lemma_mod_adds(b*(a/b), a%b, b*c);
            }
        (b*(a/b)) % (b*c) + (a%b) % (b*c);
            {
                lemma_mod_properties();
                lemma_mul_increases(c,b);
                lemma_mul_is_commutative_forall();
                assert a%b<b<=b*c;
                lemma_small_mod(a%b,b*c);
                assert (a%b) % (b*c) == a%b;
            }
        (b*(a/b)) % (b*c) + a%b;
            { lemma_truncate_middle(a/b,b,c); }
        b * ((a/b)%c) + a%b;
    }
}


lemma lemma_div_denominator_forall()
    ensures forall c:nat,d:nat {:trigger c * d} :: 0 < c && 0 < d ==> c * d != 0;
    ensures forall x:int,c:nat,d:nat {:trigger (x/c)/d} :: 0 <= x && 0 < c && 0 < d
        ==> (x/c)/d == x/(c*d);
{
    lemma_mul_nonzero_forall();
    forall (x:int,c:nat,d:nat | 0 <= x && 0 < c && 0 < d)
        ensures c * d != 0;
        ensures (x/c)/d == x/(c*d);
    {
        lemma_div_denominator(x,c,d);
    }
}

} 
