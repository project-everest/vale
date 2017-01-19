include "mod_auto.i.dfy"

module Math__div_auto_proofs_i {
import opened Math__mod_auto_i

lemma lemma_div_auto_basics(n:int)
    requires n > 0;
    ensures  (n / n == -((-n) / n) == 1)
    ensures  (forall x:int {:trigger x / n} :: 0 <= x < n <==> x / n == 0)
    ensures  forall x:int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1;
    ensures  forall x:int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1;
{
    lemma_mod_auto(n);
    lemma_mod_auto_basics(n);
    lemma_small_div();
    lemma_div_by_self(n);
    forall x:int | x / n == 0 ensures 0 <= x < n;
    {
        lemma_fundamental_div_mod(x, n);
    }
}


} 
