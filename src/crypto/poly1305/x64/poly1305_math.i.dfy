include "../../../lib/math/mul_auto.i.dfy"
include "../../../lib/math/mod_auto.i.dfy"
include "../../../lib/math/div_auto.i.dfy"
include "../../../lib/math/mul.i.dfy"
include "../../../lib/math/div.i.dfy"

module x64__Poly1305_math_i
{
import opened Math__mul_auto_i
import opened Math__mod_auto_i
import opened Math__div_auto_i
import opened Math__div_nonlinear_i
import opened Math__mul_i
import opened Math__div_i

lemma lemma_normalize()
    ensures  forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures  forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
    ensures  forall x:int, y:int, z:int {:trigger x * (y * z)} :: x * (y * z) == (x * y) * z;
{
    lemma_mul_is_distributive_forall();
    lemma_mul_is_associative_forall();
}

lemma lemma_poly_multiply(n:int, p:int, r:int, h:int, r0:int, r1:int, h0:int, h1:int, h2:int, s1:int, d0:int, d1:int, d2:int, hh:int)
    requires p > 0;
    requires 4 * (n * n) == p + 5;
    requires r == r1 * n + r0;
    requires h == h2 * (n * n) + h1 * n + h0;
    requires s1 == r1 + r1 / 4;
    requires r1 % 4 == 0;
    requires d0 == h0 * r0 + h1 * s1;
    requires d1 == h0 * r1 + h1 * r0 + h2 * s1;
    requires d2 == h2 * r0;
    requires hh == d2 * (n * n) + d1 * n + d0;
    ensures  (h * r) % p == hh % p;
{
    calc
    {
        (h * r) % p;
        ((h2 * (n * n) + h1 * n + h0) * (r1 * n + r0)) % p;
    { lemma_normalize(); }
        ((h2 * r1) * (n * n * n) +      (h2 * r0 + h1 * r1) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0) % p;
    { lemma_normalize(); }
        ((h2 * n + h1) * (n * n * 4) * (r1 / 4) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0) % p;
        ((h2 * n + h1) * (p + 5)     * (r1 / 4) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0) % p;
    { lemma_normalize(); }
        ((h2 * n + h1) * (5)         * (r1 / 4) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0 + p * ((h2 * n + h1) * (r1 / 4))) % p;
    { lemma_mod_multiples_vanish((h2 * n + h1) * (r1 / 4), 0, p); }
    { lemma_mod_auto(p); }
        ((h2 * n + h1) * (5)         * (r1 / 4) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0) % p;
    { lemma_normalize(); }
        ((h2 * r0) * (n * n) + (h0 * r1 + h1 * r0 + h2 * (5 * (r1 / 4))) * n + (h0 * r0 + h1 * (5 * (r1 / 4)))) % p;
        hh % p;
    }
}

lemma lemma_poly_reduce(n:int, p:int, h:int, h2:int, h10:int, c:int, hh:int)
    requires p > 0;
    requires 4 * (n * n) == p + 5;
    requires h2 == h / (n * n);
    requires h10 == h % (n * n);
    requires c == (h2 / 4) + (h2 / 4) * 4;
    requires hh == h10 + c + (h2 % 4) * (n * n);
    ensures  h % p == hh % p;
{
    calc
    {
        h % p;
    { lemma_fundamental_div_mod(h, n * n); }
        (h10 + h2 * (n * n)) % p;
        (h10 + (h2 / 4 * 4 + h2 % 4) * (n * n)) % p;
    { lemma_normalize(); }
        (h10 + (h2 % 4) * (n * n) + (h2 / 4) * (n * n * 4)) % p;
        (h10 + (h2 % 4) * (n * n) + (h2 / 4) * (p + 5)) % p;
    { lemma_normalize(); }
        (h10 + (h2 % 4) * (n * n) + (h2 / 4) * 5 + p * (h2 / 4)) % p;
    { lemma_mod_multiples_vanish(h2 / 4, 0, p); }
    { lemma_mod_auto(p); }
        (h10 + (h2 % 4) * (n * n) + (h2 / 4) * 5) % p;
        (h10 + (h2 % 4) * (n * n) + c) % p;
        hh % p;
    }
}

lemma lemma_poly_demod(p:int, h:int, x:int, r:int)
    requires p > 0
    ensures  ((h % p + x) * r) % p == ((h + x) * r) % p
{
    calc
    {
        ((h % p + x) * r) % p;
    { lemma_normalize(); }
        ((h % p) * r + x * r) % p;
    { lemma_mod_auto(p); }
    { lemma_mul_mod_noop_general(h, r, p); }
        ((h * r) % p + x * r) % p;
    { lemma_mod_auto(p); }
        (h * r + x * r) % p;
    { lemma_normalize(); }
        ((h + x) * r) % p;
    }
}

}
