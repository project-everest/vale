include "mul_nonlinear.i.dfy"

module Math__mul_auto_proofs_i {
import opened Math__mul_nonlinear_i

lemma lemma_mul_induction_helper(f:imap<int,bool>, x:int)
    requires forall i :: i in f;
    requires f[0];
    requires forall i {:trigger f[i], f[i + 1]} :: i >= 0 && f[i] ==> f[i + 1];
    requires forall i {:trigger f[i], f[i - 1]} :: i <= 0 && f[i] ==> f[i - 1];
    ensures  f[x];
    decreases if x >= 0 then x else -x;
{
    if (x > 0)
    {
        lemma_mul_induction_helper(f, x - 1);
        assert f[(x - 1) + 1];
    }
    else if (x < 0)
    {
        lemma_mul_induction_helper(f, x + 1);
        assert f[(x + 1) - 1];
    }
}

lemma lemma_mul_induction_forall(f:imap<int,bool>)
    requires forall i :: i in f;
    requires f[0];
    requires forall i {:trigger f[i], f[i + 1]} :: i >= 0 && f[i] ==> f[i + 1];
    requires forall i {:trigger f[i], f[i - 1]} :: i <= 0 && f[i] ==> f[i - 1];
    ensures  forall i :: f[i];
{
    forall i ensures f[i] { lemma_mul_induction_helper(f, i); }
}

lemma lemma_mul_auto_commutes()
    ensures  forall x:int, y:int {:trigger x * y} :: x * y == y * x;
{
    forall x:int, y:int ensures x * y == y * x;
    {
        lemma_mul_induction_forall(imap i :: x * i == i * x);
    }
}

lemma lemma_mul_auto_succ()
    ensures  forall x:int, y:int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y;
    ensures  forall x:int, y:int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y;
{
    lemma_mul_auto_commutes();
    forall x:int, y:int
        ensures  (x + 1) * y == x * y + y;
        ensures  (x - 1) * y == x * y - y;
    {
        lemma_mul_is_distributive_add(y, x, 1);
        lemma_mul_is_distributive_add(y, x, -1);
    }
}

lemma lemma_mul_auto_distributes()
    ensures  forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z;
    ensures  forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z;
{
    lemma_mul_auto_succ();
    forall x:int, y:int, z:int
        ensures (x + y) * z == x * z + y * z;
        ensures (x - y) * z == x * z - y * z;
    {
        var f1 := imap i :: (x + i) * z == x * z + i * z;
        var f2 := imap i :: (x - i) * z == x * z - i * z;
        assert forall i {:trigger (x + (i + 1)) * z} :: (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z;
        assert forall i {:trigger (x + (i - 1)) * z} :: (x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z;
        assert forall i {:trigger (x - (i + 1)) * z} :: (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z;
        assert forall i {:trigger (x - (i - 1)) * z} :: (x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z;
        lemma_mul_induction_forall(f1);
        lemma_mul_induction_forall(f2);
        assert f1[y];
        assert f2[y];
    }
}

} 
