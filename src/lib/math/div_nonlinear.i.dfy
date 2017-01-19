//- <NuBuild AddDafnyFlag /z3opt:smt.arith.nl=true/>
//- WARNING: In general, you shouldn't need to call these directly.  Try
//- to use the ones in div.i.dfy instead.  They're more full-featured anyway.

module Math__div_nonlinear_i {

lemma lemma_div_of_0(d:int)
    requires d != 0;
    ensures 0/d == 0;
{ }

lemma lemma_div_by_self(d:int)
    requires d != 0;
    ensures d/d == 1;
{ }

lemma lemma_small_div()
    ensures forall x, d {:trigger x / d} :: 0 <= x < d && d > 0 ==> x / d == 0;
{ }

lemma lemma_mod_of_zero_is_zero(m:int)
    requires 0 < m;
    ensures 0 % m == 0;
{ }

lemma lemma_fundamental_div_mod(x:int, d:int)
    requires d != 0;
    ensures x == d * (x/d) + (x%d);
{ }

lemma lemma_0_mod_anything()
    ensures forall m:int {:trigger 0 % m} :: m > 0 ==> 0 % m == 0;
{ }

lemma lemma_mod_yourself(m:int)
    ensures m > 0 ==> m % m == 0;
{ }

lemma lemma_small_mod(x:nat, m:nat)
    requires x<m;
    requires 0<m;
    ensures x % m == x;
{ }

lemma lemma_mod_range(x:int, m:int)
    requires m > 0;
    ensures 0 <= x % m < m;
{ }

lemma lemma_real_div_gt(x:real, y:real)
    requires x > y;
    requires x >= 0.0;
    requires y > 0.0;
    ensures  x / y > (1 as real);
{ }

} 
