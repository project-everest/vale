include "div_def.i.dfy"
include "mul.i.dfy"

module Math__div_boogie_i {
import opened Math__div_def_i
import opened Math__mul_i

lemma lemma_div_is_div_boogie(x:int, d:int)
    requires d != 0;
//-    ensures INTERNAL_div(x, d) == INTERNAL_div_boogie(x, d);
{
}

lemma lemma_mod_is_mod_boogie(x:int, d:int)
    requires d > 0;
    //-ensures INTERNAL_mod(x, d) == INTERNAL_mod_boogie(x, d);
{
}

} 
