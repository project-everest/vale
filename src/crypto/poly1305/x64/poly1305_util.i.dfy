include "../../../lib/math/mul_auto.i.dfy"
include "../../../lib/math/mod_auto.i.dfy"
include "../../../lib/math/div_auto.i.dfy"
include "../../../lib/math/mul.i.dfy"
include "../../../lib/math/div.i.dfy"
include "../../../arch/x64/vale.i.dfy"
include "../../../lib/util/operations.i.dfy"

module x64__Poly1305_util_i
{
import opened Math__mul_auto_i
import opened Math__mod_auto_i
import opened Math__div_auto_i
import opened Math__div_nonlinear_i
import opened Math__mul_i
import opened Math__div_i
import opened x64_def_s
import opened x64_vale_i
import opened operations_i

lemma lemma_BitwiseAdd64()
    ensures  forall x:uint64, y:uint64 :: x + y < 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y
    ensures  forall x:uint64, y:uint64 :: x + y >= 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y - 0x1_0000_0000_0000_0000
{
    reveal_BitwiseAdd64();
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

function{:opaque} modp(x:int):int
{
    x % (0x1_0000_0000_0000_0000 * 0x1_0000_0000_0000_0000 * 4 - 5)
}

// only the case for exact multiples of 16:
function{:opaque} poly1305_hash(h:int, pad:int, r:int, inp:map<int, Heaplet64Entry>, i:int, j:int):int
    requires i <= j
    requires (j - i) % 16 == 0
    requires forall m :: i <= m < j && (m - i) % 8 == 0 ==> m in inp
    decreases j - i
{
    if i == j then h
    else
        var jj := j - 16;
        var hh := poly1305_hash(h, pad, r, inp, i, jj);
        modp((hh + pad + 0x1_0000_0000_0000_0000 * inp[jj + 8].v + inp[jj].v) * r)
}

}
