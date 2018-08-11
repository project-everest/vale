include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/util/operations.s.dfy"

module ARM_def_s {

import opened words_and_bytes_s 
import opened operations_s

//-----------------------------------------------------------------------------
// Core types (for a 32-bit uint32-aligned machine)
//-----------------------------------------------------------------------------
predicate WordAligned(i:int) { i % 4 == 0 }
function  WordsToBytes(w:int) : int { 4 * w }
function  BytesToWords(b:int) : int requires WordAligned(b) { b / 4 }

type addr = x | isUInt32(x) && WordAligned(x)
type shift_amount = s | 0 <= s < 32 // Some shifts allow s=32, but we'll be conservative for simplicity

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
datatype ARMReg = R0|R1|R2|R3|R4|R5|R6|R7|R8|R9|R10|R11|R12|SP|LR

datatype Shift = LSLShift(amount_lsl:shift_amount)
               | LSRShift(amount_lsr:shift_amount)
               | RORShift(amount_ror:shift_amount)

datatype operand = OConst(n:uint32)
    | OReg(r:ARMReg)
    | OShift(reg:ARMReg, s:Shift)
    | OSymbol(sym:string)
    | OSP
    | OLR

datatype mementry = mementry(v:uint32)
type memmap = map<addr, mementry>
datatype memstate = MemState(addresses:memmap,
                             globals:map<operand, seq<uint32>>)

datatype state = State(regs:map<ARMReg, uint32>,
                       m:memstate,
                       ok:bool)

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------
datatype ins =
      ADD(dstADD:operand, src1ADD:operand, src2ADD:operand)
    | SUB(dstSUB:operand, src1SUB:operand, src2SUB:operand)
    | AND(dstAND:operand, src1AND:operand, src2AND:operand)
    | EOR(dstEOR:operand, src1EOR:operand, src2EOR:operand) // Also known as XOR
    | REV(dstREV:operand, srcREV:operand)
    | MOV(dstMOV:operand, srcMOV:operand)
    | LDR(rdLDR:operand,  baseLDR:operand, ofsLDR:operand)
    | LDR_global(rdLDR_global:operand, globalLDR:operand,
                 baseLDR_global:operand, ofsLDR_global:operand)
    | LDR_reloc(rdLDR_reloc:operand, symLDR_reloc:operand)
    | STR(rdSTR:operand,  baseSTR:operand, ofsSTR:operand)
    | STR_global(rdSTR_global:operand, globalSTR:operand,
                 baseSTR_global:operand, ofsSTR_global:operand)

//-----------------------------------------------------------------------------
// Code Representation
//-----------------------------------------------------------------------------
datatype ocmp = OEq | ONe | OLe | OGe | OLt | OGt
datatype obool = OCmp(cmp:ocmp, o1:operand, o2:operand)

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)

//-----------------------------------------------------------------------------
// Validity
//-----------------------------------------------------------------------------
predicate ValidState(s:state)
{
    ValidRegState(s.regs) && ValidMemState(s.m)
}

predicate {:opaque} ValidRegState(regs:map<ARMReg, uint32>)
{
    forall r:ARMReg :: r in regs
}

// All valid states have the same memory address domain, but we don't care what 
// it is (at this level).
function {:axiom} TheValidAddresses(): set<addr>

predicate {:opaque} ValidMemState(s:memstate)
{
    // regular mem
    (forall m:addr :: m in TheValidAddresses() <==> m in s.addresses)
    // globals: same names/sizes as decls
    && (forall g :: g in TheGlobalDecls() <==> g in s.globals)
    && (forall g :: g in TheGlobalDecls()
        ==> |s.globals[g]| == BytesToWords(TheGlobalDecls()[g]))
}

predicate ValidOperand(o:operand)
{
    match o
        case OConst(n) => true
        case OReg(r) => !(r.SP? || r.LR?) // not used directly
        case OShift(_,_) => false
        case OSP => true
        case OLR => true
        case OSymbol(s) => false
}

predicate ValidSecondOperand(o:operand)
{
    ValidOperand(o) 
 || (o.OShift? && !(o.reg.SP? || o.reg.LR?))
}

predicate ValidMem(addr:int)
{
    isUInt32(addr) && WordAligned(addr) && addr in TheValidAddresses()
}

predicate ValidMemRange(base:int, limit:int)
{
    isUInt32(base) && isUInt32(limit) &&
    forall m:addr :: base <= m < limit && WordAligned(m) ==> m in TheValidAddresses()
}

predicate ValidShiftOperand(s:state, o:operand)
    requires ValidState(s)
    { ValidOperand(o) && OperandContents(s, o) < 32 }

predicate ValidRegOperand(o:operand)
    { !o.OConst? && !o.OShift? && ValidOperand(o) }

//-----------------------------------------------------------------------------
// Globals
//-----------------------------------------------------------------------------
type globaldecls = map<operand, addr>

predicate ValidGlobal(o:operand)
{
    o.OSymbol? && o in TheGlobalDecls()
}

predicate ValidGlobalDecls(decls:globaldecls)
{
    forall d :: d in decls ==> d.OSymbol? && decls[d] != 0
}

predicate ValidGlobalAddr(g:operand, addr:int)
{
    ValidGlobal(g) && WordAligned(addr) 
 && AddressOfGlobal(g) <= addr < AddressOfGlobal(g) + SizeOfGlobal(g)
}

predicate ValidGlobalOffset(g:operand, offset:int)
{
    ValidGlobal(g) && WordAligned(offset) 
 && 0 <= offset < SizeOfGlobal(g)
}

// globals have an unknown (uint32) address, only establised by LDR-reloc
function {:axiom} AddressOfGlobal(g:operand): addr

function SizeOfGlobal(g:operand): uint32
    requires ValidGlobal(g)
    ensures WordAligned(SizeOfGlobal(g))
{
    TheGlobalDecls()[g]
}

// global declarations are the responsibility of the program, as long as they're valid
function {:axiom} TheGlobalDecls(): globaldecls
    ensures ValidGlobalDecls(TheGlobalDecls());

//-----------------------------------------------------------------------------
// Functions for uint8wise operations
//-----------------------------------------------------------------------------

function bswap32(x:uint32) : uint32 { 
    var uint8s := WordToBytes(x);
    BytesToWord(uint8s[3], uint8s[2], uint8s[1], uint8s[0])
}

//-----------------------------------------------------------------------------
// Evaluation
//-----------------------------------------------------------------------------

function EvalShift(w:uint32, shift:Shift) : uint32
{
    match shift
        case LSLShift(amount) => LeftShift(w, amount)
        case LSRShift(amount) => RightShift(w, amount)
        case RORShift(amount) => RotateRight(w, amount)
}

function OperandContents(s:state, o:operand): uint32
    requires ValidOperand(o) || ValidSecondOperand(o)
    requires ValidState(s)
{
    reveal_ValidRegState();
    match o
        case OConst(n) => n
        case OReg(r) => s.regs[r]
        case OShift(r, amount) => EvalShift(s.regs[r], amount)
        case OSP => s.regs[SP]
        case OLR => s.regs[LR]
}

function MemContents(s:memstate, m:addr): uint32
    requires ValidMemState(s)
    requires ValidMem(m)
{
    reveal_ValidMemState();
    //assert m in s.addresses;
    s.addresses[m].v
}

function GlobalFullContents(s:memstate, g:operand): seq<uint32>
    requires ValidMemState(s)
    requires ValidGlobal(g)
    ensures WordsToBytes(|GlobalFullContents(s, g)|) == SizeOfGlobal(g)
{
    reveal_ValidMemState();
    s.globals[g]
}

function GlobalWord(s:memstate, g:operand, offset:uint32): uint32
    requires ValidGlobalOffset(g, offset)
    requires ValidMemState(s)
{
    reveal_ValidMemState();
    GlobalFullContents(s, g)[BytesToWords(offset)]
}

predicate evalUpdate(s:state, o:operand, v:uint32, r:state)
    requires ValidState(s)
    requires ValidRegOperand(o)
    ensures evalUpdate(s, o, v, r) ==> ValidState(r)
{
    reveal_ValidRegState();
    match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])
        case OLR => r == s.(regs := s.regs[LR := v])
        case OSP => r == s.(regs := s.regs[SP := v])
}

predicate evalLoad(s:state, o:operand, base:int, ofs:int, r:state)
    requires ValidState(s)
    requires ValidRegOperand(o)
    requires WordAligned(base + ofs)
    requires ValidMem(base + ofs)
    ensures  evalLoad(s, o, base, ofs, r) ==> ValidState(r)
{
    var v := MemContents(s.m, base + ofs);
    reveal_ValidRegState();
    match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])
        case OLR => r == s.(regs := s.regs[LR := v])
        case OSP => r == s.(regs := s.regs[SP := v])
}

predicate evalLoadGlobal(s:state, o:operand, g:operand, base:int, ofs:int, r:state)
    requires ValidState(s)
    requires ValidRegOperand(o)
    requires ValidGlobalOffset(g, base + ofs - AddressOfGlobal(g))
    requires ValidGlobalAddr(g, base + ofs)
    ensures  evalLoadGlobal(s, o, g, base, ofs, r) ==> ValidState(r)
{
    var v := GlobalWord(s.m, g, base + ofs - AddressOfGlobal(g));
    reveal_ValidRegState();
    match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])
        case OLR => r == s.(regs := s.regs[LR := v])
        case OSP => r == s.(regs := s.regs[SP := v])
}

predicate evalStore(s:state, base:int, ofs:int, v:uint32, r:state)
    requires ValidState(s)
    requires ValidMem(base + ofs)
    ensures  evalStore(s, base, ofs, v, r) ==> ValidState(r)
{
    reveal_ValidMemState();
    r == s.(m := s.m.(addresses := s.m.addresses[base + ofs := mementry(v)]))
}

predicate evalStoreGlobal(s:state, g:operand, base:int, ofs:int, v:uint32, r:state)
    requires ValidState(s)
    requires ValidGlobalOffset(g, base + ofs - AddressOfGlobal(g))
    requires ValidGlobalAddr(g, base + ofs)
    ensures  evalStoreGlobal(s, g, base, ofs, v, r) ==> ValidState(r) && GlobalWord(r.m, g, base + ofs - AddressOfGlobal(g)) == v
{
    reveal_ValidMemState();
    var oldval := s.m.globals[g];
    var addr := base + ofs - AddressOfGlobal(g);
    var newval := oldval[BytesToWords(addr) := v];
    assert |newval| == |oldval|;
    r == s.(m := s.m.(globals := s.m.globals[g := newval]))
}

function evalCmp(c:ocmp, i1:uint32, i2:uint32):bool
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
    requires ValidState(s)
    requires ValidOperand(o.o1)
    requires ValidOperand(o.o2)
{
    evalCmp(o.cmp, OperandContents(s, o.o1), OperandContents(s, o.o2))
}

predicate branchRelation(s:state, s':state, cond:bool)
{
    s' == s
}

predicate ValidInstruction(s:state, ins:ins)
{ 
    ValidState(s) && match ins
        case ADD(dest, src1, src2) => ValidOperand(src1) &&
            ValidSecondOperand(src2) && ValidRegOperand(dest)
        case SUB(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidRegOperand(dest) &&
            isUInt32(OperandContents(s,src1) - OperandContents(s,src2))
        case AND(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidRegOperand(dest)
        case EOR(dest, src1, src2) => ValidOperand(src1) &&
            ValidSecondOperand(src2) && ValidRegOperand(dest)
        case REV(dest, src) => ValidRegOperand(src) &&
            ValidRegOperand(dest)
        case LDR(rd, base, ofs) => 
            ValidRegOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            var addr := OperandContents(s, base) + OperandContents(s, ofs);
            WordAligned(addr) &&
            ValidMem(addr)
        case LDR_global(rd, global, base, ofs) => 
            ValidRegOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            ValidGlobalOffset(global, OperandContents(s, base) + OperandContents(s, ofs) - AddressOfGlobal(global)) &&
            ValidGlobalAddr(global, OperandContents(s, base) + OperandContents(s, ofs))
        case LDR_reloc(rd, global) => 
            ValidRegOperand(rd) && ValidGlobal(global)
        case STR(rd, base, ofs) =>
            ValidRegOperand(rd) &&
            ValidOperand(ofs) && ValidOperand(base) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(OperandContents(s, base) + OperandContents(s, ofs))
        case STR_global(rd, global, base, ofs) => 
            ValidRegOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            ValidGlobalOffset(global, OperandContents(s, base) + OperandContents(s, ofs) - AddressOfGlobal(global)) &&
            ValidGlobalAddr(global, OperandContents(s, base) + OperandContents(s, ofs))
        case MOV(dst, src) => ValidRegOperand(dst) &&
            ValidSecondOperand(src)
}

predicate evalIns(ins:ins, s:state, r:state)
{
    if !s.ok || !ValidInstruction(s, ins) then !r.ok
    else match ins
        case ADD(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) + OperandContents(s, src2)) % 0x1_0000_0000),
            r)
        case SUB(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) - OperandContents(s, src2))),
            r)
        case AND(dst, src1, src2) => evalUpdate(s, dst,
            BitwiseAnd(OperandContents(s, src1), OperandContents(s, src2)),
            r)
        case EOR(dst, src1, src2) => evalUpdate(s, dst,
            BitwiseXor(OperandContents(s, src1), OperandContents(s, src2)),
            r)
        case REV(dst, src) => evalUpdate(s, dst, bswap32(OperandContents(s, src)), r)
        case LDR(rd, base, ofs) => 
            evalLoad(s, rd, OperandContents(s, base), OperandContents(s, ofs), r)
        case LDR_global(rd, global, base, ofs) => 
            evalLoadGlobal(s, rd, global, OperandContents(s, base), OperandContents(s, ofs), r)
        case LDR_reloc(rd, name) =>
            evalUpdate(s, rd, AddressOfGlobal(name), r)
        case STR(rd, base, ofs) => 
            evalStore(s, OperandContents(s, base), OperandContents(s, ofs), OperandContents(s, rd), r)
        case STR_global(rd, global, base, ofs) => 
            evalStoreGlobal(s, global, OperandContents(s, base), OperandContents(s, ofs), OperandContents(s, rd), r)
        case MOV(dst, src) => evalUpdate(s, dst,
            OperandContents(s, src),
            r)
}

predicate evalBlock(block:codes, s:state, r:state)
{
    if block.CNil? then
        r == s
    else
        exists r' :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
}

predicate evalIfElse(cond:obool, ifT:code, ifF:code, s:state, r:state)
    decreases if ValidState(s) && ValidOperand(cond.o1) && ValidOperand(cond.o2) && evalOBool(s, cond) then ifT else ifF
{
    if ValidState(s) && s.ok && ValidOperand(cond.o1) && ValidOperand(cond.o2) then
        exists s' :: branchRelation(s, s', evalOBool(s, cond)) && (if evalOBool(s, cond) then evalCode(ifT, s', r) else evalCode(ifF, s', r))
    else
        !r.ok
}

predicate evalWhile(b:obool, c:code, n:nat, s:state, r:state)
    decreases c, n
{
    if ValidState(s) && s.ok && ValidOperand(b.o1) && ValidOperand(b.o2) then
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
