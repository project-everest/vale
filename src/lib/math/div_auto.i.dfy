include "mod_auto.i.dfy"
include "div_auto_proofs.i.dfy"

module Math__div_auto_i {
import opened Math__mod_auto_i
import opened Math__div_auto_proofs_i

predicate DivAuto(n:int)
    requires n > 0; // TODO: allow n < 0
{
    ModAuto(n)
 && (n / n == -((-n) / n) == 1)
 && (forall x:int {:trigger x / n} :: 0 <= x < n <==> x / n == 0)
 && (forall x:int, y:int {:trigger (x + y) / n} ::
                (var z := (x % n) + (y % n);
                    (  (0 <= z < n     && (x + y) / n == x / n + y / n)
                    || (n <= z < n + n && (x + y) / n == x / n + y / n + 1))))
 && (forall x:int, y:int {:trigger (x - y) / n} ::
                (var z := (x % n) - (y % n);
                    (   (0 <= z < n && (x - y) / n == x / n - y / n)
                    || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1))))
}

lemma lemma_div_auto(n:int)
    requires n > 0;
    ensures  DivAuto(n);
{
    lemma_mod_auto(n);
    lemma_div_auto_basics(n);
    assert (0 + n) / n == 1;
    assert (0 - n) / n == -1;
    forall x:int, y:int {:trigger (x + y) / n}
        ensures  (var z := (x % n) + (y % n);
                     (   (0 <= z < n && (x + y) / n == x / n + y / n)
                      || (n <= z < 2 * n && (x + y) / n == x / n + y / n + 1)));
    {
        var f := imap xy:(int, int) ::
                 (var z := (xy.0 % n) + (xy.1 % n);
                     (   (0 <= z < n && (xy.0 + xy.1) / n == xy.0 / n + xy.1 / n)
                      || (n <= z < 2 * n && (xy.0 + xy.1) / n == xy.0 / n + xy.1 / n + 1)));
        forall i, j
            ensures j >= 0 && f[(i, j)] ==> f[(i, j + n)];
            ensures i < n  && f[(i, j)] ==> f[(i - n, j)];
            ensures j < n  && f[(i, j)] ==> f[(i, j - n)];
            ensures i >= 0 && f[(i, j)] ==> f[(i + n, j)];
        {
            assert ((i + n) + j) / n == ((i + j) + n) / n;
            assert (i + (j + n)) / n == ((i + j) + n) / n;
            assert ((i - n) + j) / n == ((i + j) - n) / n;
            assert (i + (j - n)) / n == ((i + j) - n) / n;
        }
        forall i, j
            ensures 0 <= i < n && 0 <= j < n ==> f[(i, j)];
        {
            assert ((i + n) + j) / n == ((i + j) + n) / n;
            assert (i + (j + n)) / n == ((i + j) + n) / n;
            assert ((i - n) + j) / n == ((i + j) - n) / n;
            assert (i + (j - n)) / n == ((i + j) - n) / n;
        }
        lemma_mod_induction_forall2(n, f);
        assert f[(x, y)];
    }
    forall x:int, y:int {:trigger (x - y) / n}
        ensures  (var z := (x % n) - (y % n);
                     (   (0 <= z < n && (x - y) / n == x / n - y / n)
                     || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1)));
    {
        var f := imap xy:(int, int) ::
                 (var z := (xy.0 % n) - (xy.1 % n);
                     (   (0 <= z < n && (xy.0 - xy.1) / n == xy.0 / n - xy.1 / n)
                     || (-n <= z < 0 && (xy.0 - xy.1) / n == xy.0 / n - xy.1 / n - 1)));
        forall i, j
            ensures j >= 0 && f[(i, j)] ==> f[(i, j + n)];
            ensures i < n  && f[(i, j)] ==> f[(i - n, j)];
            ensures j < n  && f[(i, j)] ==> f[(i, j - n)];
            ensures i >= 0 && f[(i, j)] ==> f[(i + n, j)];
        {
            assert ((i + n) - j) / n == ((i - j) + n) / n;
            assert (i - (j - n)) / n == ((i - j) + n) / n;
            assert ((i - n) - j) / n == ((i - j) - n) / n;
            assert (i - (j + n)) / n == ((i - j) - n) / n;
        }
        forall i, j
            ensures 0 <= i < n && 0 <= j < n ==> f[(i, j)];
        {
            assert ((i + n) - j) / n == ((i - j) + n) / n;
            assert (i - (j - n)) / n == ((i - j) + n) / n;
            assert ((i - n) - j) / n == ((i - j) - n) / n;
            assert (i - (j + n)) / n == ((i - j) - n) / n;
        }
        lemma_mod_induction_forall2(n, f);
        assert f[(x, y)];
    }
}

predicate TDivAutoLe(x:int, y:int) { x <= y }

lemma lemma_div_auto_induction(n:int, x:int, f:imap<int,bool>)
    requires n > 0;
    requires forall i :: i in f;
    requires DivAuto(n) ==> (forall i {:trigger TDivAutoLe(0, i)} :: TDivAutoLe(0, i) && i < n ==> f[i])
                         && (forall i {:trigger TDivAutoLe(0, i)} :: TDivAutoLe(0, i) && f[i] ==> f[i + n])
                         && (forall i {:trigger TDivAutoLe(i + 1, n)} :: TDivAutoLe(i + 1, n) && f[i] ==> f[i - n]);
    ensures  DivAuto(n);
    ensures  f[x];
{
    lemma_div_auto(n);
    assert forall i :: TDivAutoLe(0, i) && i < n ==> f[i];
    assert forall i {:trigger f[i], f[i + n]} :: TDivAutoLe(0, i) && f[i] ==> f[i + n];
    assert forall i {:trigger f[i], f[i - n]} :: TDivAutoLe(i + 1, n) && f[i] ==> f[i - n];
    lemma_mod_induction_forall(n, f);
    assert f[x];
}

lemma lemma_div_auto_induction_forall(n:int, f:imap<int,bool>)
    requires n > 0;
    requires forall i :: i in f;
    requires DivAuto(n) ==> (forall i {:trigger TDivAutoLe(0, i)} :: TDivAutoLe(0, i) && i < n ==> f[i])
                         && (forall i {:trigger TDivAutoLe(0, i)} :: TDivAutoLe(0, i) && f[i] ==> f[i + n])
                         && (forall i {:trigger TDivAutoLe(i + 1, n)} :: TDivAutoLe(i + 1, n) && f[i] ==> f[i - n]);
    ensures  DivAuto(n);
    ensures  forall i {:trigger f[i]} :: f[i];
{
    lemma_div_auto(n);
    assert forall i :: TDivAutoLe(0, i) && i < n ==> f[i];
    assert forall i {:trigger f[i], f[i + n]} :: TDivAutoLe(0, i) && f[i] ==> f[i + n];
    assert forall i {:trigger f[i], f[i - n]} :: TDivAutoLe(i + 1, n) && f[i] ==> f[i - n];
    lemma_mod_induction_forall(n, f);
}

} 
