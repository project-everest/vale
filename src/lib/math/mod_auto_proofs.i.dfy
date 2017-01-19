include "mul_auto.i.dfy"
include "mul.i.dfy"
include "div_nonlinear.i.dfy"

module Math__mod_auto_proofs_i {
import opened Math__mul_auto_i
import opened Math__mul_i
import opened Math__div_nonlinear_i

lemma lemma_mod_induction_helper(n:int, f:imap<int,bool>, x:int)
    requires n > 0;
    requires forall i :: i in f;
    requires forall i :: 0 <= i < n ==> f[i];
    requires forall i {:trigger f[i], f[i + n]} :: i >= 0 && f[i] ==> f[i + n];
    requires forall i {:trigger f[i], f[i - n]} :: i < n  && f[i] ==> f[i - n];
    ensures  f[x];
    decreases if x >= n then x else -x;
{
    if (x >= n)
    {
        lemma_mod_induction_helper(n, f, x - n);
        assert f[(x - n) + n];
    }
    else if (x < 0)
    {
        lemma_mod_induction_helper(n, f, x + n);
        assert f[(x + n) - n];
    }
}

lemma lemma_mod_induction_forall(n:int, f:imap<int,bool>)
    requires n > 0;
    requires forall i :: i in f;
    requires forall i :: 0 <= i < n ==> f[i];
    requires forall i {:trigger f[i], f[i + n]} :: i >= 0 && f[i] ==> f[i + n];
    requires forall i {:trigger f[i], f[i - n]} :: i < n  && f[i] ==> f[i - n];
    ensures  forall i :: f[i];
{
    forall i ensures f[i] { lemma_mod_induction_helper(n, f, i); }
}

lemma lemma_mod_induction_forall2(n:int, f:imap<(int,int),bool>)
    requires n > 0;
    requires forall i, j :: (i, j) in f;
    requires forall i, j :: 0 <= i < n && 0 <= j < n ==> f[(i, j)];
    requires forall i, j {:trigger f[(i, j)], f[(i + n, j)]} :: i >= 0 && f[(i, j)] ==> f[(i + n, j)];
    requires forall i, j {:trigger f[(i, j)], f[(i, j + n)]} :: j >= 0 && f[(i, j)] ==> f[(i, j + n)];
    requires forall i, j {:trigger f[(i, j)], f[(i - n, j)]} :: i < n  && f[(i, j)] ==> f[(i - n, j)];
    requires forall i, j {:trigger f[(i, j)], f[(i, j - n)]} :: j < n  && f[(i, j)] ==> f[(i, j - n)];
    ensures  forall i, j :: f[(i, j)];
{
    forall x, y ensures f[(x, y)];
    {
        forall i | 0 <= i < n ensures f[(i, y)];
        {
            var fj := imap j :: f[(i, j)];
            lemma_mod_induction_forall(n, fj);
            assert fj[y];
        }
        var fi := imap i :: f[(i, y)];
        lemma_mod_induction_forall(n, fi);
        assert fi[x];
    }
}

lemma lemma_mod_auto_basics(n:int)
    requires n > 0;
    ensures  forall x:int {:trigger (x + n) % n} :: (x + n) % n == x % n;
    ensures  forall x:int {:trigger (x - n) % n} :: (x - n) % n == x % n;
    ensures  forall x:int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1;
    ensures  forall x:int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1;
    ensures  forall x:int {:trigger x % n} :: 0 <= x < n <==> x % n == x;
{
    forall x:int
        ensures 0 <= x < n <==> x % n == x;
    {
        if (0 <= x < n) { lemma_small_mod(x, n); }
        lemma_mod_range(x, n);
    }
    forall x:int
        ensures (x + n) % n == x % n;
        ensures (x - n) % n == x % n;
        ensures (x + n) / n == x / n + 1;
        ensures (x - n) / n == x / n - 1;
    {
        lemma_fundamental_div_mod(x, n);
        lemma_fundamental_div_mod(x + n, n);
        lemma_fundamental_div_mod(x - n, n);
        lemma_mod_range(x, n);
        lemma_mod_range(x + n, n);
        lemma_mod_range(x - n, n);
        var zp := (x + n) / n - x / n - 1;
        var zm := (x - n) / n - x / n + 1;
        forall ensures 0 == n * zp + ((x + n) % n) - (x % n) { lemma_mul_auto(); }
        forall ensures 0 == n * zm + ((x - n) % n) - (x % n) { lemma_mul_auto(); }
        if (zp > 0) { lemma_mul_inequality(1, zp, n); }
        if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
        if (zm > 0) { lemma_mul_inequality(1, zm, n); }
        if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
    }
}


} 
