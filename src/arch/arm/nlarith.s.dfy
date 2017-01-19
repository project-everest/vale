module nlarith_s {
lemma {:axiom} lemma_MulModZero(a:int, b:int)
    requires b > 0
    ensures (a * b) % b == 0
/* FIXME: prove this! */

lemma lemma_DivMulLessThan(a:int, b:int)
    requires b > 0
    ensures (a / b) * b <= a
{}

lemma {:axiom} lemma_DivBounds'(a:int, b:int)
    requires a > b > 0
    ensures a / b < a
/* FIXME: this is unstable, but proves in some versions of Dafny/Z3 */

lemma lemma_AddWrapAssociates(x1:nat, x2:nat, x3:nat)
    ensures (((x1 + x2) % 0x1_0000_0000) + x3) % 0x1_0000_0000
         == (x1 + ((x2 + x3) % 0x1_0000_0000)) % 0x1_0000_0000;
{
}

lemma lemma_DivBounds(a:int, b:int)
    requires a >= 0 && b > 0
    ensures 0 <= (a / b) <= a
{
    if a < b {
        assert a / b == 0;
    } else if a == b {
        assert a / b == 1;
    } else if b == 1 {
        assert a / b == a;
    } else if a > b {
        assert 1 <= a / b;
        lemma_DivBounds'(a, b);
    }
}

lemma lemma_MulSign(a:int, b:int)
    requires a >= 0 && b >= 0
    ensures a * b >= 0
{}

}
