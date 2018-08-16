include "operations.s.dfy"

module operations_i {

import opened operations_s

lemma lemma_BitwiseAdd32EquivalentToAddMod2To32(x:uint32, y:uint32)
    ensures BitwiseAdd32(x, y) == (x + y) % 0x1_0000_0000;
{
    reveal_BitwiseAdd32();
}

lemma lemma_BitwiseAdd64EquivalentToAddMod2To64(x:uint64, y:uint64)
    ensures BitwiseAdd64(x, y) == (x + y) % 0x1_0000_0000_0000_0000;
{
    reveal_BitwiseAdd64();
}

} // end module operations_i
