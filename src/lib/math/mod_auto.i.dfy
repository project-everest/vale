include "mod_auto_proofs.i.dfy"

module Math__mod_auto_i {
import opened Math__mod_auto_proofs_i


predicate eq_mod(x:int, y:int, n:int)
    requires n > 0;
{
    (x - y) % n == 0 // same as x % n == y % n, but easier to do induction on x - y than x and y separately
}

predicate ModAuto(n:int)
    requires n > 0;
{
    (n % n == (-n) % n == 0)
 && (forall x:int {:trigger (x % n) % n} :: (x % n) % n == x % n)
 && (forall x:int {:trigger x % n} :: 0 <= x < n <==> x % n == x)
 && (forall x:int, y:int {:trigger (x + y) % n} ::
                (var z := (x % n) + (y % n);
                    (  (0 <= z < n     && (x + y) % n == z)
                    || (n <= z < n + n && (x + y) % n == z - n))))
 && (forall x:int, y:int {:trigger (x - y) % n} ::
                (var z := (x % n) - (y % n);
                    (   (0 <= z < n && (x - y) % n == z)
                    || (-n <= z < 0 && (x - y) % n == z + n))))
}

lemma lemma_mod_auto(n:int)
    requires n > 0;
    ensures  ModAuto(n);
{
    lemma_mod_auto_basics(n);
    assert (0 + n) % n == 0;
    assert (0 - n) % n == 0;
    assert forall i, j {:trigger ((i + n) + j) % n} :: ((i + n) + j) % n == ((i + j) + n) % n;
    assert forall i, j {:trigger ((i + n) - j) % n} :: ((i + n) - j) % n == ((i - j) + n) % n;
    assert forall i, j {:trigger (i + (j + n)) % n} :: (i + (j + n)) % n == ((i + j) + n) % n;
    assert forall i, j {:trigger (i - (j - n)) % n} :: (i - (j - n)) % n == ((i - j) + n) % n;
    assert forall i, j {:trigger ((i - n) + j) % n} :: ((i - n) + j) % n == ((i + j) - n) % n;
    assert forall i, j {:trigger ((i - n) - j) % n} :: ((i - n) - j) % n == ((i - j) - n) % n;
    assert forall i, j {:trigger (i + (j - n)) % n} :: (i + (j - n)) % n == ((i + j) - n) % n;
    assert forall i, j {:trigger (i - (j + n)) % n} :: (i - (j + n)) % n == ((i - j) - n) % n;
    forall x:int, y:int {:trigger (x + y) % n}
        ensures  (var z := (x % n) + (y % n);
                     (   (0 <= z < n && (x + y) % n == z)
                      || (n <= z < 2 * n && (x + y) % n == z - n)));
    {
        var f := imap xy:(int, int) ::
                 (var z := (xy.0 % n) + (xy.1 % n);
                     (   (0 <= z < n && (xy.0 + xy.1) % n == z)
                      || (n <= z < 2 * n && (xy.0 + xy.1) % n == z - n)));

        forall i, j | 0 <= i < n && 0 <= j < n
            ensures (var z := (i % n) + (j % n);
                     (   (0 <= z < n && (i + j) % n == z)
                      || (n <= z < 2 * n && (i + j) % n == z - n)));
        {
            assert ((i + j) - n) % n == (i + j) % n;
        }

        lemma_mod_induction_forall2(n, f);
        assert f[(x, y)];
    }
    forall x:int, y:int {:trigger (x - y) % n}
        ensures  (var z := (x % n) - (y % n);
                     (   (0 <= z < n && (x - y) % n == z)
                      || (-n <= z < 0 && (x - y) % n == z + n)));
    {
        var f := imap xy:(int, int) ::
                 (var z := (xy.0 % n) - (xy.1 % n);
                     (   (0 <= z < n && (xy.0 - xy.1) % n == z)
                      || (-n <= z < 0 && (xy.0 - xy.1) % n == z + n)));

        forall i, j | 0 <= i < n && 0 <= j < n
            ensures (var z := (i % n) - (j % n);
                     (   (0 <= z < n && (i - j) % n == z)
                      || (-n <= z < 0 && (i - j) % n == z + n)));
        {
            assert ((i - j) + n) % n == (i - j) % n;
        }

        lemma_mod_induction_forall2(n, f);
        assert f[(x, y)];
    }
}

predicate TModAutoLe(x:int, y:int) { x <= y }

lemma lemma_mod_auto_induction(n:int, x:int, f:imap<int,bool>)
    requires n > 0;
    requires forall i :: i in f;
    requires ModAuto(n) ==> (forall i {:trigger TModAutoLe(0, i)} :: TModAutoLe(0, i) && i < n ==> f[i])
                         && (forall i {:trigger TModAutoLe(0, i)} :: TModAutoLe(0, i) && f[i] ==> f[i + n])
                         && (forall i {:trigger TModAutoLe(i + 1, n)} :: TModAutoLe(i + 1, n) && f[i] ==> f[i - n]);
    ensures  ModAuto(n);
    ensures  f[x];
{
    lemma_mod_auto(n);
    assert forall i :: TModAutoLe(0, i) && i < n ==> f[i];
    assert forall i {:trigger f[i], f[i + n]} :: TModAutoLe(0, i) && f[i] ==> f[i + n];
    assert forall i {:trigger f[i], f[i - n]} :: TModAutoLe(i + 1, n) && f[i] ==> f[i - n];
    lemma_mod_induction_forall(n, f);
    assert f[x];
}

lemma lemma_mod_auto_induction_forall(n:int, f:imap<int,bool>)
    requires n > 0;
    requires forall i :: i in f;
    requires ModAuto(n) ==> (forall i {:trigger TModAutoLe(0, i)} :: TModAutoLe(0, i) && i < n ==> f[i])
                         && (forall i {:trigger TModAutoLe(0, i)} :: TModAutoLe(0, i) && f[i] ==> f[i + n])
                         && (forall i {:trigger TModAutoLe(i + 1, n)} :: TModAutoLe(i + 1, n) && f[i] ==> f[i - n]);
    ensures  ModAuto(n);
    ensures  forall i {:trigger f[i]} :: f[i];
{
    lemma_mod_auto(n);
    assert forall i :: TModAutoLe(0, i) && i < n ==> f[i];
    assert forall i {:trigger f[i], f[i + n]} :: TModAutoLe(0, i) && f[i] ==> f[i + n];
    assert forall i {:trigger f[i], f[i - n]} :: TModAutoLe(i + 1, n) && f[i] ==> f[i - n];
    lemma_mod_induction_forall(n, f);
}

/* TODO: if we need these at all, they should have better triggers to protect call sites
lemma lemma_mod_auto_induction2(x:int, y:int, n:int, f:imap<(int,int),bool>)
    requires n > 0;
    requires forall i, j :: (i, j) in f;
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: 0 <= i < n && 0 <= j < n ==> f[(i, j)]);
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: i >= 0 && f[(i, j)] ==> f[(i + n, j)]);
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: j >= 0 && f[(i, j)] ==> f[(i, j + n)]);
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: i < n  && f[(i, j)] ==> f[(i - n, j)]);
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: j < n  && f[(i, j)] ==> f[(i, j - n)]);
    ensures  ModAuto(n);
    ensures  f[(x, y)];
{
    lemma_mod_auto(n);
    lemma_mod_induction_forall2(n, f);
    assert f[(x, y)];
}

lemma lemma_mod_auto_induction_forall2(n:int, f:imap<(int,int),bool>)
    requires n > 0;
    requires forall i, j :: (i, j) in f;
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: 0 <= i < n && 0 <= j < n ==> f[(i, j)]);
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: i >= 0 && f[(i, j)] ==> f[(i + n, j)]);
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: j >= 0 && f[(i, j)] ==> f[(i, j + n)]);
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: i < n  && f[(i, j)] ==> f[(i - n, j)]);
    requires ModAuto(n) ==> (forall i, j {:trigger f[(i, j)]} :: j < n  && f[(i, j)] ==> f[(i, j - n)]);
    ensures  ModAuto(n);
    ensures  forall i, j {:trigger f[(i, j)]} :: f[(i, j)];
{
    lemma_mod_auto(n);
    lemma_mod_induction_forall2(n, f);
}
*/

} 
