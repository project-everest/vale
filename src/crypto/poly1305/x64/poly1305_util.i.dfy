include "poly1305.s.dfy"
include "../../../lib/math/mul_auto.i.dfy"
include "../../../lib/math/mod_auto.i.dfy"
include "../../../lib/math/div_auto.i.dfy"
include "../../../lib/math/mul.i.dfy"
include "../../../lib/math/div.i.dfy"
include "../../../lib/math/bitvectors128.i.dfy"
include "../../../arch/x64/vale.i.dfy"
include "../../../lib/util/operations.i.dfy"

module x64__Poly1305_util_i
{
import opened x64__Poly1305_s
import opened Math__mul_auto_i
import opened Math__mod_auto_i
import opened Math__div_auto_i
import opened Math__div_nonlinear_i
import opened Math__mul_i
import opened Math__div_i
import opened bitvectors128_i
import opened x64_def_s
import opened x64_vale_i
import opened operations_i

function{:opaque} lowerUpper192(l:uint128, h:uint64):int
{
    0x1_00000000_00000000_00000000_00000000 * h + l
}

function{:opaque} BitwiseSub64(x:uint64, y:uint64):uint64
{
    (x - y) % 0x1_0000_0000_0000_0000
}

lemma lemma_BitwiseAdd64()
    ensures  forall x:uint64, y:uint64 :: x + y < 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y
    ensures  forall x:uint64, y:uint64 :: x + y >= 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y - 0x1_0000_0000_0000_0000
    ensures  forall x:uint64 :: BitwiseAdd64(x, 0) == x;
{
    reveal_BitwiseAdd64();
}

lemma lemma_BitwiseSub64()
    ensures  forall x:uint64, y:uint64 :: 0 <= x - y ==> BitwiseSub64(x, y) == x - y
    ensures  forall x:uint64, y:uint64 :: 0 > x - y ==> BitwiseSub64(x, y) == x - y + 0x1_0000_0000_0000_0000
    ensures  forall x:uint64 :: BitwiseSub64(x, 0) == x;
{
    reveal_BitwiseSub64();
}

lemma lemma_BitwiseMul64()
    ensures  forall x:uint64, y:uint64 :: x * y < 0x1_0000_0000_0000_0000 ==> BitwiseMul64(x, y) == x * y
    ensures  forall x:uint64, y:uint64 :: 0x1_0000_0000_0000_0000 * BitwiseMul64hi(x, y) + BitwiseMul64(x, y) == x * y
{
    reveal_BitwiseMul64();
    reveal_BitwiseMul64hi();
    lemma_mul_nonnegative_forall();
    forall x:uint64, y:uint64 ensures 0x1_0000_0000_0000_0000 * BitwiseMul64hi(x, y) + BitwiseMul64(x, y) == x * y
    {
        lemma_fundamental_div_mod(x * y, 0x1_0000_0000_0000_0000);
        lemma_mul_strict_upper_bound(x, 0x1_0000_0000_0000_0000, y, 0x1_0000_0000_0000_0000);
    }
}

type va_cmp = operand
function method va_const_cmp(x:uint64):va_cmp { OConst(x) }
function method va_coerce_operand_to_cmp(o:opr):opr { o }

type va_mem_operand = operand

predicate va_is_src_mem_operand_uint64(o:opr, s:va_state)
{
    o.OConst? || (o.OReg? && !o.r.X86Xmm?) || (o.OHeap? && Valid64BitSourceOperand(to_state(s), o))
}

function va_eval_mem_operand_uint64(s:va_state, o:opr):uint64
    requires va_is_src_mem_operand_uint64(o, s)
{
    eval_op64(to_state(s), o)
}

function method va_op_mem_operand_reg64(r:x86reg):opr { OReg(r) }
function method va_coerce_operand_to_mem_operand(o:opr):opr { o }
function method va_const_mem_operand(x:uint64):opr { OConst(x) }

function method va_opr_code_Mem(base:va_operand, offset:int, taint:taint):va_mem_operand
{
    MakeHeapOp(base, offset, taint)
}

function method va_opr_lemma_Mem(s:va_state, base:va_operand, offset:int, taint:taint, id:heaplet_id):va_mem_operand
    requires x86_ValidState(s)
    requires base.OReg?
    requires ValidMemAddr(MReg(base.r, offset))
    requires ValidSrcAddr(s.heaplets, id, va_get_reg64(base.r, s) + offset, 64, taint)
    ensures  Valid64BitSourceOperand(to_state(s), OHeap(MReg(base.r, offset), taint))
    ensures  eval_op64(to_state(s), OHeap(MReg(base.r, offset), taint)) == s.heaplets[id].mem64[va_get_reg64(base.r, s) + offset].v
{
    reveal_x86_ValidState();
    va_opr_code_Mem(base, offset, taint)
}

// only the case for exact multiples of 16:
function{:opaque} poly1305_heap_blocks(h:int, pad:int, r:int, m:map<int, Heaplet64Entry>, i:int, k:int):int
    requires i <= k
    requires (k - i) % 16 == 0
    requires forall j :: i <= j < k && (j - i) % 8 == 0 ==> j in m
    decreases k - i
{
    if i == k then h
    else
        var kk := k - 16;
        var hh := poly1305_heap_blocks(h, pad, r, m, i, kk);
        modp((hh + pad + 0x1_0000_0000_0000_0000 * m[kk + 8].v + m[kk].v) * r)
}

function{:opaque} heapletTo128(m:map<int, Heaplet64Entry>, i:int, k:int):map<int, uint128>
    requires i <= k
    requires forall j :: i <= j < k && (j - i) % 16 == 0 ==> j in m && j + 8 in m
{
    map j:int | i <= j < k && (j - i) % 16 == 0 ::
        [m[j].v + 0x1_0000_0000_0000_0000 * m[j + 8].v][0] // HACK: [...][0] works around Dafny resolver issue
}

lemma lemma_poly1305_heap_hash_blocks(h:int, pad:int, r:int, m:map<int, Heaplet64Entry>, i:int, k:int, k2:int)
    requires i <= k <= k2
    requires (k - i) % 16 == 0
    requires (k2 - i) % 16 == 0
    requires forall j :: i <= j < k2 && (j - i) % 8 == 0 ==> j in m
    ensures  forall j :: i <= j < k2 && (j - i) % 16 == 0 ==> j in heapletTo128(m, i, k2)
    ensures  poly1305_heap_blocks(h, pad, r, m, i, k) == poly1305_hash_blocks(h, pad, r, heapletTo128(m, i, k2), i, k)
    decreases k - i
{
    reveal_poly1305_heap_blocks();
    reveal_poly1305_hash_blocks();
    reveal_heapletTo128();
    if (i != k)
    {
        lemma_poly1305_heap_hash_blocks(h, pad, r, m, i, k - 16, k2);
    }
}

function{:opaque} poly1305_heap(key_r:uint128, key_s:uint128, m:map<int, Heaplet64Entry>, start:int, len:nat):int
    requires forall j :: start <= j < start + len && (j - start) % 16 == 0 ==> j in m && j + 8 in m
{
    reveal_heapletTo128();
    poly1305_hash(key_r, key_s, heapletTo128(m, start, start + len), start, len)
}

lemma{:fuel power2, 16} lemma_power2_add64(n:nat)
    ensures power2(64 + n) == 0x1_0000_0000_0000_0000 * power2(n)
{
    assert power2(16 + n) == 0x1_0000 * power2(n);
    assert power2(32 + n) == 0x1_0000_0000 * power2(n);
    assert power2(48 + n) == 0x1_0000_0000_0000 * power2(n);
}


lemma lemma_uint128_64_mod(x1:uint64, x0:uint64, y1:uint64)
    requires y1 != 0
    ensures  (x1 * 0x1_0000_0000_0000_0000 + x0) % (y1 * 0x1_0000_0000_0000_0000) == ((x1 % y1) * 0x1_0000_0000_0000_0000) + x0
{
    lemma_mod_breakdown(x1 * 0x1_0000_0000_0000_0000 + x0, 0x1_0000_0000_0000_0000, y1);
}

lemma lemma_reduce128(h:int, h2:uint64, h1:uint64, h0:uint64, g:int, g2:uint64, g1:uint64, g0:uint64)
    requires h2 < 5
    requires g == h + 5
    requires h == lowerUpper192(lowerUpper128(h0, h1), h2)
    requires g == lowerUpper192(lowerUpper128(g0, g1), g2)
    ensures  g2 < 4 ==> lowerUpper128(h0, h1) == mod2_128(modp(h))
    ensures  g2 >= 4 ==> lowerUpper128(g0, g1) == mod2_128(modp(h))
{
    if (g2 < 4)
    {
        assert 0 <= h < 0x3_ffffffff_ffffffff_ffffffff_fffffffb by { reveal_lowerUpper192(); }
        calc
        {
            mod2_128(modp(h));
            { reveal_modp(); assert modp(h) == h % 0x3_ffffffff_ffffffff_ffffffff_fffffffb; }
            mod2_128(h);
            { reveal_lowerUpper128(); reveal_lowerUpper192(); reveal_mod2_128(); }
            lowerUpper128(h0, h1);
        }
    }
    else
    {
        assert 0 <= h - 0x3_ffffffff_ffffffff_ffffffff_fffffffb < 0x3_ffffffff_ffffffff_ffffffff_fffffffb by { reveal_lowerUpper192(); }
        calc
        {
            mod2_128(modp(h));
            { reveal_modp(); assert modp(h) == h % 0x3_ffffffff_ffffffff_ffffffff_fffffffb; }
            mod2_128(h - 0x3_ffffffff_ffffffff_ffffffff_fffffffb);
            { reveal_lowerUpper128(); reveal_lowerUpper192(); reveal_mod2_128(); }
            lowerUpper128(g0, g1);
        }
    }
}

lemma lemma_add_mod128(x:int, y:int)
    ensures  mod2_128(mod2_128(x) + y) == mod2_128(x + y)
{
    reveal_mod2_128();
}

}
