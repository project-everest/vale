// Trusted specification for x86 semantics

include "../../lib/util/operations.s.dfy"

module x64_def_s {

import opened operations_s

datatype x86reg =
  X86Eax | X86Ebx | X86Ecx | X86Edx | X86Esi | X86Edi | X86Ebp
| X86R8 | X86R9 | X86R10 | X86R11 | X86R12 | X86R13 | X86R14 | X86R15
| X86Xmm(xmm:int)
datatype maddr = MConst(n:int) | MReg(reg:x86reg, offset:int) | MIndex(base:x86reg, scale:int, index:x86reg, index_offset:int)
datatype operand = OConst(n:uint64) | OReg(r:x86reg) | OStack(s:int) | OHeap(addr:maddr)
datatype ocmp = OEq | ONe | OLe | OGe | OLt | OGt
datatype obool = OCmp(cmp:ocmp, o1:operand, o2:operand)

datatype ins =
  Rand(xRand:operand)
| Mov32(dstMov:operand, srcMov:operand)
| Mov64(dstMov64:operand, srcMov64:operand)
| Add32(dstAdd:operand, srcAdd:operand)
| Add64(dstAdd64:operand, srcAdd64:operand)
| AddLea64(dstAddLea64:operand, src1AddLea64:operand, src2AddLea64:operand)
| Sub32(dstSub:operand, srcSub:operand)
| Sub64(dstSub64:operand, srcSub64:operand)
| Mul32(srcMul:operand)
| Mul64(srcMul64:operand)
| IMul64(dstIMul64:operand, srcIMul64:operand)
| AddCarry(dstAddCarry:operand, srcAddCarry:operand)
| AddCarry64(dstAddCarry64:operand, srcAddCarry64:operand)
| Xor32(dstXor:operand, srcXor:operand)
| Xor64(dstXorq:operand, srcXorq:operand)
| And32(dstAnd:operand, srcAnd:operand)
| And64(dstAnd64:operand, srcAnd64:operand)
| Not32(dstNot:operand)
| GetCf(dstCf:operand) // corresponds to SETC instruction
| Rol32(dstRolConst:operand, amountRolConst:operand)
| Ror32(dstRorConst:operand, amountRorConst:operand)
| Shl32(dstShlConst:operand, amountShlConst:operand)
| Shl64(dstShlConst64:operand, amountShlConst64:operand)
| Shr32(dstShrConst:operand, amountShrConst:operand)
| Shr64(dstShrConst64:operand, amountShrConst64:operand)
| Pxor(dstPXor:operand, srcPXor:operand)

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)

type Frame = map<int, uint32>
type Stack = seq<Frame>
datatype memEntry = Mem8(v8:uint8) | Mem16(v16:uint16) | Mem32(v32:uint32) | Mem64(v64:uint64)
type heap = map<int, memEntry>
datatype state = state(
    regs:map<x86reg, uint64>,
    xmms:map<int, Quadword>,
    flags:uint32,
    stack:Stack,
    heap:heap,
    ok:bool)

predicate IsUInt32(i:int) { 0 <= i < 0x1_0000_0000 }

predicate ValidRegister(regs:map<x86reg, uint64>, r:x86reg)
{
    r in regs
}

function eval_reg(regs:map<x86reg, uint64>, r:x86reg) : uint64
{
    if !ValidRegister(regs, r) then 24
    else regs[r]
}

predicate ValidMemAddr(addr:maddr)
{
    match addr
        case MConst(n) => true
        case MReg(r, offset) => !r.X86Xmm?
        case MIndex(base, scale, index, offset) => !base.X86Xmm? && !index.X86Xmm?
}

function EvalMemAddr(regs:map<x86reg, uint64>, addr:maddr) : int
    requires ValidMemAddr(addr);
{
    match addr
        case MConst(n) => n
        case MReg(r, offset) => eval_reg(regs, r) + offset
        case MIndex(base, scale, index, offset) =>
             eval_reg(regs, base) + scale * eval_reg(regs, index) + offset
}

predicate ValidHeapAddr(s:state, addr:maddr)
{
    ValidMemAddr(addr)
 && var resolved_addr := EvalMemAddr(s.regs, addr);
    resolved_addr in s.heap
 && s.heap[resolved_addr].Mem32?
}

predicate ValidXmmRegisterIndex(index:int)
{
    0 <= index <= 7
}

predicate ValidXmm(xmms:map<int,Quadword>, r:x86reg)
    requires r.X86Xmm?;
{
    r.xmm in xmms && ValidXmmRegisterIndex(r.xmm)
}

predicate ValidOperand(s:state, size:int, o:operand)
{
    match o
        case OConst(n) => (size == 32 ==> IsUInt32(o.n))
        case OReg(r) =>
            if size == 32 || size == 64 then
                !r.X86Xmm? && ValidRegister(s.regs, r)
            else if size == 64 then
                !r.X86Xmm? && ValidRegister(s.regs, r)
            else if size == 128 then
                r.X86Xmm? && ValidXmm(s.xmms, r)
            else
                false
        case OStack(slot) =>
            if size == 32 then
                |s.stack| > 0 && slot in s.stack[0]
            else if size == 64 then
                |s.stack| > 0 && slot in s.stack[0] && slot + 1 in s.stack[0]
            else
                false
        case OHeap(addr) =>
            if size == 32 then
                ValidHeapAddr(s, addr)
            else if size == 64 then
                Valid64BitHeapOperand(s, o)
            else false
}

function GetValueAtHeapAddress(s:state, addr:maddr) : uint32
    requires ValidHeapAddr(s, addr);
{
    s.heap[EvalMemAddr(s.regs, addr)].v32
}

predicate ValidImm8(s:state, o:operand)
{
       o.OConst?
    && 0 <= o.n < 256
}

predicate ValidShiftAmountOperand(s:state, o:operand)
{
       (   o.OConst?
        && 0 <= o.n < 32)
    || (   o == OReg(X86Ecx)
        && o.r in s.regs
        && IsUInt32(s.regs[o.r]))
}

predicate ValidShiftAmountOperand64(s:state, o:operand)
{
       (   o.OConst?
        && 0 <= o.n < 64)
    || (   o == OReg(X86Ecx)
        && o.r in s.regs
        && IsUInt32(s.regs[o.r]))
}

predicate ValidSourceOperand(s:state, size:int, o:operand)
{
       ValidOperand(s, size, o)
    && (size == 32 && o.OReg? ==> IsUInt32(s.regs[o.r]))
}

predicate Valid32BitSourceOperand(s:state, o:operand)
{
     ValidSourceOperand(s, 32, o)
}

predicate Valid64BitSourceOperand(s:state, o:operand)
{
     ValidSourceOperand(s, 64, o)
}

predicate ValidDestinationOperand(s:state, size:int, o:operand)
{
      !o.OConst?
    && ValidOperand(s, size, o)
}

predicate Valid32BitDestinationOperand(s:state, o:operand)
{
    ValidDestinationOperand(s, 32, o)
}

predicate Valid64BitDestinationOperand(s:state, o:operand)
{
    ValidDestinationOperand(s, 64, o)
}

predicate method IsXmmOperand(o:operand)
{
    o.OReg? && o.r.X86Xmm?
}

predicate ValidXmmOperand(s:state, o:operand)
{
       IsXmmOperand(o)
    && ValidXmm(s.xmms, o.r)
}

predicate ValidXmmSourceOperand(s:state, o:operand)
{
       ValidSourceOperand(s, 128, o)
    && ValidXmmOperand(s, o)
}

predicate ValidXmmDestinationOperand(s:state, o:operand)
{
       ValidDestinationOperand(s, 128, o)
    && ValidXmmOperand(s, o)
}

predicate Valid64BitHeapOperand(s:state, o:operand)
    requires o.OHeap?;
{
    ValidMemAddr(o.addr)
 && var m0 := EvalMemAddr(s.regs, o.addr);
    m0 in s.heap
 && s.heap[m0].Mem64?
}

function eval_op32(s:state, o:operand) : uint32
    requires !(o.OReg? && o.r.X86Xmm?);
{
    if !ValidSourceOperand(s, 32, o) then
        42
    else
        match o
            case OConst(n) => n
            case OReg(r) => s.regs[r]
            case OStack(slot) => s.stack[0][slot]
            case OHeap(addr) => GetValueAtHeapAddress(s, addr)
}

function{:opaque} lower64(i:uint64):uint32 { i % 0x1_0000_0000 }
function{:opaque} upper64(i:uint64):uint32 { i / 0x1_0000_0000 }
function{:opaque} lowerUpper64(l:uint32, u:uint32):uint64 { l + 0x1_0000_0000 * u }

function eval_op64(s:state, o:operand) : uint64
    requires !(o.OReg? && o.r.X86Xmm?)
{
    if !ValidSourceOperand(s, 64, o) then
        42
    else
        match o
            case OConst(n) => n
            case OReg(r) => s.regs[r]
            case OStack(slot) => lowerUpper64(s.stack[0][slot], s.stack[0][slot + 1])
            case OHeap(addr) => s.heap[EvalMemAddr(s.regs, addr)].v64
}

function UpdateHeap32(h:heap, addr:int, v:uint32) : heap
{
    h[addr := Mem32(v)]
}

function UpdateHeap64(h:heap, addr:int, v:uint64) : heap
{
    h[addr := Mem64(v)]
}

predicate evalUpdateAndMaintainFlags(s:state, o:operand, v:uint32, r:state)
    requires Valid32BitDestinationOperand(s, o);
    requires !(o.OReg? && o.r.X86Xmm?);
{
    match o
        case OReg(reg)    => r == s.(regs := s.regs[reg := v])
        case OStack(slot) => r == s.(stack := [s.stack[0][slot := v]] + s.stack[1..])
        case OHeap(addr)  => r == s.(heap := UpdateHeap32(s.heap, EvalMemAddr(s.regs, o.addr), v))
}

predicate evalUpdateAndMaintainFlags64(s:state, o:operand, v:uint64, r:state)
    requires Valid64BitDestinationOperand(s, o);
    requires !(o.OReg? && o.r.X86Xmm?);
{
    match o
        case OReg(reg)    => r == s.(regs := s.regs[reg := v])
        case OStack(slot) => r == s.(stack := [s.stack[0][slot := lower64(v)][slot + 1 := upper64(v)]] + s.stack[1..])
        case OHeap(addr)  => r == s.(heap := UpdateHeap64(s.heap, EvalMemAddr(s.regs, addr), v))
}

predicate evalUpdateAndHavocFlags(s:state, o:operand, v:uint32, r:state)
    requires Valid32BitDestinationOperand(s, o);
{
    match o
        case OReg(reg)    => r == s.(regs := s.regs[reg := v], flags := r.flags)
        case OStack(slot) => r == s.(stack := [s.stack[0][slot := v]] + s.stack[1..], flags := r.flags)
        case OHeap(addr)  => r == s.(heap := UpdateHeap32(s.heap, EvalMemAddr(s.regs, o.addr), v), flags := r.flags)
}

predicate evalUpdateAndHavocFlags64(s:state, o:operand, v:uint64, r:state)
    requires Valid64BitDestinationOperand(s, o);
{
    match o
        case OReg(reg)    => r == s.(regs := s.regs[reg := v], flags := r.flags)
        case OStack(slot) => r == s.(ok := false) // not yet supported
        case OHeap(addr)  => r == s.(ok := false) // not yet supported
}

predicate evalUpdateXmmsAndHavocFlags(s:state, o:operand, v:Quadword, r:state)
    requires ValidXmmOperand(s, o);
{
    r == s.(xmms := s.xmms[o.r.xmm := v], flags := r.flags)
}

predicate Valid128BitDestinationOperand(s:state, o:operand)
{
    ValidDestinationOperand(s, 128, o)
}

function evalCmp(c:ocmp, i1:uint64, i2:uint64):bool
{
    match c
        case OEq => i1 == i2
        case ONe => i1 != i2
        case OLe => i1 <= i2
        case OGe => i1 >= i2
        case OLt => i1 <  i2
        case OGt => i1 >  i2
}

function evalOBool(s:state, o:obool):bool
    requires ValidSourceOperand(s, 64, o.o1);
    requires ValidSourceOperand(s, 64, o.o2);
{
    evalCmp(o.cmp, eval_op64(s, o.o1), eval_op64(s, o.o2))
}

function clear_low_byte(n:uint32) : uint32
{
    (n / 256) * 256
}

function xor32(x:uint32, y:uint32) : uint32  { BitwiseXor(x, y) }

function xor64(x:uint64, y:uint64) : uint64  { BitwiseXor64(x, y) }

function and32(x:uint32, y:uint32) : uint32  { BitwiseAnd(x, y) }

function not32(x:uint32) : uint32 { BitwiseNot(x) }

function rol32(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    { RotateLeft(x, amount) }

function ror32(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    { RotateRight(x, amount) }

function shl32(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    { LeftShift(x, amount) }

function shr32(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    { RightShift(x, amount) }

// Is the carry flag (CF) set?
predicate{:axiom} Cf(flags:uint32)

predicate ValidInstruction(s:state, ins:ins)
{
    match ins
        case Rand(xRand) => Valid32BitDestinationOperand(s, xRand)
        case Mov32(dstMov, srcMov) => Valid32BitDestinationOperand(s, dstMov) && Valid32BitSourceOperand(s, srcMov)
        case Mov64(dstMov, srcMov) => Valid64BitDestinationOperand(s, dstMov) && Valid64BitSourceOperand(s, srcMov)
        case Add32(dstAdd, srcAdd) => Valid32BitDestinationOperand(s, dstAdd) && Valid32BitSourceOperand(s, srcAdd) && Valid32BitSourceOperand(s, dstAdd)
        case Add64(dstAdd, srcAdd) => Valid64BitDestinationOperand(s, dstAdd) && Valid64BitSourceOperand(s, srcAdd) && Valid64BitSourceOperand(s, dstAdd)
        case AddLea64(dstAdd, srcAdd1, srcAdd2) => Valid64BitDestinationOperand(s, dstAdd) && Valid64BitSourceOperand(s, srcAdd1) && Valid64BitSourceOperand(s, srcAdd2) && Valid64BitSourceOperand(s, dstAdd)
        case Sub32(dstSub, srcSub) => Valid32BitDestinationOperand(s, dstSub) && Valid32BitSourceOperand(s, srcSub) && Valid32BitSourceOperand(s, dstSub)
        case Sub64(dstSub, srcSub) => Valid64BitDestinationOperand(s, dstSub) && Valid64BitSourceOperand(s, srcSub) && Valid64BitSourceOperand(s, dstSub)
        case Mul32(srcMul) => Valid32BitSourceOperand(s, srcMul) && Valid32BitSourceOperand(s, OReg(X86Eax)) && Valid32BitDestinationOperand(s, OReg(X86Eax)) && Valid32BitDestinationOperand(s, OReg(X86Edx))
        case Mul64(srcMul) => Valid64BitSourceOperand(s, srcMul) && Valid64BitSourceOperand(s, OReg(X86Eax)) && Valid64BitDestinationOperand(s, OReg(X86Eax)) && Valid64BitDestinationOperand(s, OReg(X86Edx))
        case IMul64(dst, src) => Valid64BitDestinationOperand(s, dst) && Valid64BitSourceOperand(s, src) && Valid64BitSourceOperand(s, dst)
        case AddCarry(dstAddCarry, srcAddCarry) => Valid32BitDestinationOperand(s, dstAddCarry) && Valid32BitSourceOperand(s, srcAddCarry) && Valid32BitSourceOperand(s, dstAddCarry)
        case AddCarry64(dstAddCarry, srcAddCarry) => Valid64BitDestinationOperand(s, dstAddCarry) && Valid64BitSourceOperand(s, srcAddCarry) && Valid64BitSourceOperand(s, dstAddCarry)
        case Xor32(dstXor, srcXor) => Valid32BitDestinationOperand(s, dstXor) && Valid32BitSourceOperand(s, srcXor) && Valid32BitSourceOperand(s, dstXor)
        case Xor64(dstXor, srcXor) => Valid64BitDestinationOperand(s, dstXor) && Valid64BitSourceOperand(s, srcXor) && Valid64BitSourceOperand(s, dstXor)
        case And32(dstAnd, srcAnd) => Valid32BitDestinationOperand(s, dstAnd) && Valid32BitSourceOperand(s, srcAnd) && Valid32BitSourceOperand(s, dstAnd)
        case And64(dstAnd, srcAnd) => Valid64BitDestinationOperand(s, dstAnd) && Valid64BitSourceOperand(s, srcAnd) && Valid64BitSourceOperand(s, dstAnd)
        case Not32(dstNot) => Valid32BitDestinationOperand(s, dstNot) && Valid32BitSourceOperand(s, dstNot)
        case GetCf(dstCf) => Valid32BitDestinationOperand(s, dstCf) && Valid32BitSourceOperand(s, dstCf)
        case Rol32(dstRolConst, amountRol) => Valid32BitDestinationOperand(s, dstRolConst) && ValidShiftAmountOperand(s, amountRol) && Valid32BitSourceOperand(s, dstRolConst)
        case Ror32(dstRorConst, amountRor) => Valid32BitDestinationOperand(s, dstRorConst) && ValidShiftAmountOperand(s, amountRor) && Valid32BitSourceOperand(s, dstRorConst)
        case Shl32(dstShlConst, amountShl) => Valid32BitDestinationOperand(s, dstShlConst) && ValidShiftAmountOperand(s, amountShl) && Valid32BitSourceOperand(s, dstShlConst)
        case Shl64(dstShrConst, amountShr) => Valid64BitDestinationOperand(s, dstShrConst) && ValidShiftAmountOperand64(s, amountShr) && Valid64BitSourceOperand(s, dstShrConst)
        case Shr32(dstShrConst, amountShr) => Valid32BitDestinationOperand(s, dstShrConst) && ValidShiftAmountOperand(s, amountShr) && Valid32BitSourceOperand(s, dstShrConst)
        case Shr64(dstShrConst, amountShr) => Valid64BitDestinationOperand(s, dstShrConst) && ValidShiftAmountOperand64(s, amountShr) && Valid64BitSourceOperand(s, dstShrConst)
        case Pxor(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
}

lemma {:axiom} lemma_division_in_bounds(a:uint32, b:uint32)
    ensures 0 <= (a * b) / 0x1_0000_0000 < 0x1_0000_0000;

lemma {:axiom} lemma_division_in_bounds64(a:uint64, b:uint64)
    ensures 0 <= (a * b) / 0x1_0000_0000_0000_0000 < 0x1_0000_0000_0000_0000;

predicate evalIns(ins:ins, s:state, r:state)
{
    if !s.ok || !ValidInstruction(s, ins) then
        !r.ok
    else
        match ins
            case Rand(x) => exists n:uint32 :: evalUpdateAndHavocFlags(s, x, n, r)
            case Mov32(dst, src) => evalUpdateAndMaintainFlags(s, dst, eval_op32(s, src), r) // mov doesn't change flags
            case Mov64(dst, src) => evalUpdateAndMaintainFlags64(s, dst, eval_op64(s, src), r) // mov doesn't change flags
            case Add32(dst, src) => evalUpdateAndHavocFlags(s, dst, (eval_op32(s, dst) + eval_op32(s, src)) % 0x1_0000_0000, r)
            case Add64(dst, src) => var sum := eval_op64(s, dst) + eval_op64(s, src);
                                    evalUpdateAndHavocFlags64(s, dst, sum % 0x1_0000_0000_0000_0000, r)
                                    && Cf(r.flags) == (sum >= 0x1_0000_0000_0000_0000)
            case AddLea64(dst, src1, src2) => evalUpdateAndMaintainFlags64(s, dst, (eval_op64(s, src1) + eval_op64(s, src2)) % 0x1_0000_0000_0000_0000, r)
            case Sub32(dst, src) => evalUpdateAndHavocFlags(s, dst, (eval_op32(s, dst) - eval_op32(s, src)) % 0x1_0000_0000, r)
            case Sub64(dst, src) => evalUpdateAndHavocFlags64(s, dst, (eval_op64(s, dst) - eval_op64(s, src)) % 0x1_0000_0000_0000_0000, r)
            case Mul32(src)      => var product := s.regs[X86Eax] * eval_op32(s, src);
                                    lemma_division_in_bounds(s.regs[X86Eax], eval_op32(s, src));  // Annoying
                                    var hi := (product / 0x1_0000_0000);
                                    var lo := (product % 0x1_0000_0000);
                                    r == s.(regs := s.regs[X86Edx := hi][X86Eax := lo], flags := r.flags)
            case Mul64(src)      => var product := s.regs[X86Eax] * eval_op64(s, src);
                                    lemma_division_in_bounds64(s.regs[X86Eax], eval_op64(s, src));  // Annoying
                                    var hi := (product / 0x1_0000_0000_0000_0000);
                                    var lo := (product % 0x1_0000_0000_0000_0000);
                                    r == s.(regs := s.regs[X86Edx := hi][X86Eax := lo], flags := r.flags)
            case IMul64(dst, src) => evalUpdateAndHavocFlags64(s, dst, (eval_op64(s, dst) * eval_op64(s, src)) % 0x1_0000_0000_0000_0000, r)
            // Add with carry (ADC) instruction
            case AddCarry(dst, src) => var old_carry := if Cf(s.flags) then 1 else 0;
                                       var sum := eval_op32(s, dst) + eval_op32(s, src) + old_carry;
                                       evalUpdateAndHavocFlags(s, dst, sum % 0x1_0000_0000, r)
                                    && Cf(r.flags) == (sum >= 0x1_0000_0000)
            case AddCarry64(dst, src) => var old_carry := if Cf(s.flags) then 1 else 0;
                                       var sum := eval_op64(s, dst) + eval_op64(s, src) + old_carry;
                                       evalUpdateAndHavocFlags64(s, dst, sum % 0x1_0000_0000_0000_0000, r)
                                    && Cf(r.flags) == (sum >= 0x1_0000_0000_0000_0000)
            case Xor32(dst, src) => evalUpdateAndHavocFlags(s, dst, xor32(eval_op32(s, dst), eval_op32(s, src)), r)
            case Xor64(dst, src) => evalUpdateAndHavocFlags64(s, dst, xor64(eval_op64(s, dst), eval_op64(s, src)), r)
            case And32(dst, src) => evalUpdateAndHavocFlags(s, dst, and32(eval_op32(s, dst), eval_op32(s, src)), r)
            case And64(dst, src) => evalUpdateAndHavocFlags64(s, dst, BitwiseAnd64(eval_op64(s, dst), eval_op64(s, src)), r)
            case Not32(dst)      => evalUpdateAndHavocFlags(s, dst, not32(eval_op32(s, dst)), r)
            // Sticks the carry flag (CF) in a register (see SETC instruction)
            case GetCf(dst)      => // Instruction only writes the first uint8
                                    evalUpdateAndMaintainFlags(s, dst, clear_low_byte(eval_op32(s, dst)) + if Cf(s.flags) then 1 else 0, r)
            case Rol32(dst, amount)  =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, rol32(eval_op32(s, dst), n), r) else !r.ok

            case Ror32(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, ror32(eval_op32(s, dst), n), r) else !r.ok

            case Shl32(dst, amount)  =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, shl32(eval_op32(s, dst), n), r) else !r.ok
            case Shl64(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 64 then evalUpdateAndHavocFlags64(s, dst, BitwiseShl64(eval_op64(s, dst), n), r) else !r.ok

            case Shr32(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, shr32(eval_op32(s, dst), n), r) else !r.ok
            case Shr64(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 64 then evalUpdateAndHavocFlags64(s, dst, BitwiseShr64(eval_op64(s, dst), n), r) else !r.ok
            case Pxor(dst, src) => evalUpdateXmmsAndHavocFlags(s, dst, QuadwordXor(s.xmms[dst.r.xmm], s.xmms[src.r.xmm]), r)
}

predicate evalBlock(block:codes, s:state, r:state)
{
    if block.CNil? then
        r == s
    else
        exists r':state :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
}

function {:axiom} updateFlagsUsingCondition(flags:uint32, cond:bool) : uint32

predicate branchRelation(s:state, s':state, cond:bool)
{
    // TODO: Make zero flag depend on evalOBool(s, cond)
    s' == s.(flags := updateFlagsUsingCondition(s.flags, cond))
}

predicate evalIfElse(cond:obool, ifT:code, ifF:code, s:state, r:state)
    decreases if ValidSourceOperand(s, 64, cond.o1) && ValidSourceOperand(s, 64, cond.o2) && evalOBool(s, cond) then ifT else ifF;
{
    if s.ok && ValidSourceOperand(s, 64, cond.o1) && ValidSourceOperand(s, 64, cond.o2) then
        exists s' ::
           branchRelation(s, s', evalOBool(s, cond))
        && (if evalOBool(s, cond) then evalCode(ifT, s', r) else evalCode(ifF, s', r))
    else
        !r.ok
}

predicate evalWhile(b:obool, c:code, n:nat, s:state, r:state)
  decreases c, n
{
    if s.ok && ValidSourceOperand(s, 64, b.o1) && ValidSourceOperand(s, 64, b.o2) then
        if n == 0 then
            !evalOBool(s, b) && branchRelation(s, r, false)
        else
            exists loop_start:state, loop_end:state ::    evalOBool(s, b)
                                                 && branchRelation(s, loop_start, true)
                                                 && evalCode(c, loop_start, loop_end)
                                                 && evalWhile(b, c, n - 1, loop_end, r)
    else
        !r.ok
}

// evaluation (zero or more steps) may succeed and change s to r where r.ok == true
// evaluation (zero or more steps) may fail where r.ok == false
predicate evalCode(c:code, s:state, r:state)
  decreases c, 0
{
    match c
        case Ins(ins) => evalIns(ins, s, r)
        case Block(block) => evalBlock(block, s, r)
        case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        case While(cond, body) => exists n:nat :: evalWhile(cond, body, n, s, r)
}

}
