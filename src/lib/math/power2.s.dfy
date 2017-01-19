module Math__power2_s {

function {:opaque} power2(exp: nat) : nat
    ensures power2(exp) > 0;
{
    if (exp==0) then
        1
    else
        2*power2(exp-1)
}

lemma lemma_power2_32()
    ensures power2(8) == 0x100;
    ensures power2(16) == 0x10000;
    ensures power2(24) == 0x1000000;
    ensures power2(32) == 0x100000000;
{
    reveal_power2();
    assert power2(0) == 0x1;
    assert power2(2) == 0x4;
    assert power2(4) == 0x10;
    assert power2(6) == 0x40;
    assert power2(8) == 0x100;
    assert power2(10) == 0x400;
    assert power2(12) == 0x1000;
    assert power2(14) == 0x4000;
    assert power2(16) == 0x10000;
    assert power2(18) == 0x40000;
    assert power2(20) == 0x100000;
    assert power2(22) == 0x400000;
    assert power2(24) == 0x1000000;
    assert power2(26) == 0x4000000;
    assert power2(28) == 0x10000000;
    assert power2(30) == 0x40000000;
}

} 
