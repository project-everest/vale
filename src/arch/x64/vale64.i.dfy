include "vale.i.dfy"
include "../../lib/util/operations.i.dfy"

module x64_vale64_i
{
import opened x64_def_s
import opened x64_vale_i
import opened operations_i

function{:opaque} BitwiseSub64(x:uint64, y:uint64):uint64
{
    (x - y) % 0x1_0000_0000_0000_0000
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

}
