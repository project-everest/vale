include "../../../lib/math/power2.s.dfy"

module x64__Poly1305_common_i
{
import opened Math__power2_s

lemma{:fuel power2, 10} lemma_bytes_power2()
    ensures power2(0)  == 0x1
    ensures power2(8)  == 0x1_00
    ensures power2(16) == 0x1_0000
    ensures power2(24) == 0x1_0000_00
    ensures power2(32) == 0x1_0000_0000
    ensures power2(40) == 0x1_0000_0000_00
    ensures power2(48) == 0x1_0000_0000_0000
    ensures power2(56) == 0x1_0000_0000_0000_00
{
}

}
