// Untrusted Dafny-Vale interface

include "def.s.dfy"

module x64_vale_i {

import opened x64_def_s

type opr = operand

////////////////////////////////////////////////////////////////////////
//
//  Connecting Vale types to Dafny types
//
////////////////////////////////////////////////////////////////////////

type va_int = int
type va_bool = bool
type va_operand = operand
type va_code = code
type va_codes = codes
type va_state = state

type imm8 = uint8

////////////////////////////////////////////////////////////////////////
//
//  Connecting Vale functions to Dafny functions
//
////////////////////////////////////////////////////////////////////////

function va_get_ok(s:va_state):bool { s.ok }
//function va_get_reg32(r:x86reg, s:va_state):uint32 requires r in s.regs && IsUInt32(s.regs[r]) { s.regs[r] }
function va_get_reg32(r:x86reg, s:va_state):uint32 requires r in s.regs { if IsUInt32(s.regs[r]) then s.regs[r] else lower64(s.regs[r]) }
function va_get_reg64(r:x86reg, s:va_state):uint64 requires r in s.regs { s.regs[r] }
function va_get_Quadword(r:int, s:va_state):Quadword requires r in s.xmms { s.xmms[r] }
function va_get_flags(s:va_state):uint32 { s.flags }
function va_get_mem(s:va_state):heap { s.heap }
function va_get_stack(s:va_state):Stack { s.stack }

function va_update_ok(sM:va_state, sK:va_state):va_state { sK.(ok := sM.ok) }
function va_modify_reg32(r:x86reg, sM:va_state, sK:va_state):va_state
    requires r in sM.regs
{ sK.(regs := sK.regs[r := sM.regs[r]]) }
function va_update_reg64(r:x86reg, sM:va_state, sK:va_state):va_state
    requires r in sM.regs
{ sK.(regs := sK.regs[r := sM.regs[r]]) }
function va_modify_Quadword(r:int, sM:va_state, sK:va_state):va_state
    requires r in sM.xmms
{ sK.(xmms := sK.xmms[r := sM.xmms[r]]) }
function va_update_mem(sM:va_state, sK:va_state):va_state { sK.(heap := sM.heap) }
function va_update_flags(sM:va_state, sK:va_state):va_state { sK.(flags := sM.flags) }
function va_update_stack(sM:va_state, sK:va_state):va_state { sK.(stack := sM.stack) }

predicate va_is_src_opr_imm8(o:opr, s:va_state) { o.OConst? && 0 <= o.n < 256 }

type va_value_opr32 = uint32
type va_operand_opr32 = va_operand
predicate is_src_opr32(o:opr, s:va_state) { (o.OConst? && IsUInt32(o.n)) || (o.OReg? && !o.r.X86Xmm?) }
predicate va_is_src_opr32(o:opr, s:va_state) { (o.OConst? && IsUInt32(o.n)) || (o.OReg? && !o.r.X86Xmm? && o.r in s.regs && IsUInt32(s.regs[o.r])) }
predicate va_is_dst_opr32(o:opr, s:va_state) { o.OReg? && !o.r.X86Xmm? && o.r in s.regs && IsUInt32(s.regs[o.r]) }

type va_value_opr64 = uint64
type va_operand_opr64 = va_operand
predicate va_is_src_opr64(o:opr, s:va_state) { o.OConst? || (o.OReg? && !o.r.X86Xmm?) }
predicate va_is_dst_opr64(o:opr, s:va_state) { o.OReg? && !o.r.X86Xmm? }

type va_value_opr_quad  = Quadword
type va_operand_opr_quad = va_operand
predicate va_is_src_opr_quad(o:opr, s:va_state) { o.OReg? && o.r.X86Xmm? && 0 <= o.r.xmm <= 7 }
predicate va_is_dst_opr_quad(o:opr, s:va_state) { o.OReg? && o.r.X86Xmm? && 0 <= o.r.xmm <= 7 }

type va_value_opr_imm8 = imm8
type va_operand_opr_imm8 = va_operand
function va_eval_opr_imm8(s:va_state, o:opr):uint32
    requires va_is_src_opr_imm8(o, s);
{
    o.n
}

function va_eval_opr32(s:va_state, o:opr):uint32
    requires is_src_opr32(o, s);
{
    eval_op32(s, o)
}

function va_eval_opr64(s:va_state, o:opr):uint64
    requires va_is_src_opr64(o, s);
{
    eval_op64(s, o)
}

function va_eval_opr_quad(s:va_state, o:opr):Quadword
    requires va_is_src_opr_quad(o, s);
    requires o.r.xmm in s.xmms;
{
    s.xmms[o.r.xmm]
}

function va_update_operand_opr32(o:opr, sM:va_state, sK:va_state):va_state
    requires o.OReg?;
    requires o.r in sM.regs;
    requires o.r.X86Xmm? ==> o.r.xmm in sM.xmms;
{
    va_update_operand(o, sM, sK)
}

function va_update_operand_opr64(o:opr, sM:va_state, sK:va_state):va_state
    requires o.OReg?;
    requires o.r in sM.regs;
    requires o.r.X86Xmm? ==> o.r.xmm in sM.xmms;
{
    va_update_operand(o, sM, sK)
}

function va_update_operand_opr_quad(o:opr, sM:va_state, sK:va_state):va_state
    requires o.OReg?;
    requires o.r in sM.regs;
    requires o.r.X86Xmm? ==> o.r.xmm in sM.xmms;
{
    va_update_operand(o, sM, sK)
}

function va_update_operand(o:opr, sM:va_state, sK:va_state):va_state
    requires o.OReg?;
    requires o.r in sM.regs;
    requires o.r.X86Xmm? ==> o.r.xmm in sM.xmms;
{
    if o.r.X86Xmm? then va_modify_Quadword(o.r.xmm, sM, sK) else va_update_reg64(o.r, sM, sK)
}

predicate va_state_eq(s0:va_state, s1:va_state)
{
    s0.regs == s1.regs
 && s0.xmms == s1.xmms
 && s0.flags == s1.flags
 && s0.stack == s1.stack
 && s0.heap == s1.heap
 && s0.ok == s1.ok
}

predicate{:opaque} evalCodeOpaque(c:code, s0:state, sN:state)
{
    evalCode(c, s0, sN)
}

predicate eval_code(c:code, s:state, r:state)
{
    s.ok ==> evalCodeOpaque(c, s, r)
}

function method va_CNil():codes { CNil }
predicate cHeadIs(b:codes, c:code) { b.va_CCons? && b.hd == c }
predicate cTailIs(b:codes, t:codes) { b.va_CCons? && b.tl == t }

predicate va_require(b0:codes, c1:code, s0:va_state, sN:va_state)
{
    cHeadIs(b0, c1)
 //&& s0.ok
 && eval_code(Block(b0), s0, sN)
 && x86_ValidState(s0)
}

// Weaker form of eval_code that we can actually ensure generically in instructions
predicate eval_weak(c:code, s:state, r:state)
{
    s.ok && r.ok ==> evalCodeOpaque(c, s, r)
}

predicate va_ensure(b0:codes, b1:codes, s0:va_state, s1:va_state, sN:va_state)
{
    cTailIs(b0, b1)
 //&& s1.ok
 && eval_weak(b0.hd, s0, s1)
 && eval_code(Block(b1), s1, sN)
 && x86_ValidState(s1)
}

function method va_const_operand(n:uint64):opr { OConst(n) }
function method va_const_opr_imm8(n:imm8):opr { OConst(n) }
function method va_const_opr32(n:uint32):opr { OConst(n) }
function method va_const_opr64(n:uint64):opr { OConst(n) }
function method va_op_operand_reg32(r:x86reg):opr { OReg(r) }
function method va_op_opr32_reg32(r:x86reg):opr { OReg(r) }
function method va_op_operand_reg64(r:x86reg):opr { OReg(r) }
function method va_op_opr_reg64(r:x86reg):opr { OReg(r) }
function method va_op_opr64_reg64(r:x86reg):opr { OReg(r) }
function method va_op_operand_Quadword(r:int):opr { OReg(X86Xmm(r)) }
function method va_op_opr_quad_Quadword(r:int):opr { OReg(X86Xmm(r)) }
function method va_op_cmp_reg32(r:x86reg):opr { OReg(r) }
function method va_op_cmp_reg64(r:x86reg):opr { OReg(r) }

function method va_cmp_eq(o1:opr, o2:opr):obool { OCmp(OEq, o1, o2) }
function method va_cmp_ne(o1:opr, o2:opr):obool { OCmp(ONe, o1, o2) }
function method va_cmp_le(o1:opr, o2:opr):obool { OCmp(OLe, o1, o2) }
function method va_cmp_ge(o1:opr, o2:opr):obool { OCmp(OGe, o1, o2) }
function method va_cmp_lt(o1:opr, o2:opr):obool { OCmp(OLt, o1, o2) }
function method va_cmp_gt(o1:opr, o2:opr):obool { OCmp(OGt, o1, o2) }

function method va_Block(block:codes):code { Block(block) }
function method va_IfElse(ifb:obool, ift:code, iff:code):code { IfElse(ifb, ift, iff) }
function method va_While(whileb:obool, whilec:code):code { While(whileb, whilec) }

function method va_get_block(c:code):codes requires c.Block? { c.block }
function method va_get_ifCond(c:code):obool requires c.IfElse? { c.ifCond }
function method va_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
function method va_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }
function method va_get_whileCond(c:code):obool requires c.While? { c.whileCond }
function method va_get_whileBody(c:code):code requires c.While? { c.whileBody }

function method va_mem_code(oBase:opr, oOffset:opr):operand
    requires oBase.OReg?
    requires oOffset.OConst?
{
    OHeap(MReg(oBase.r, 4 * oOffset.n))
}

////////////////////////////////////////////////////////////////////////
//
//  Invariants over the state
//
////////////////////////////////////////////////////////////////////////

predicate valid_state(s:state)
{
    |s.stack| > 0
 && (forall r :: r in s.regs)
 && (forall r :: r in s.xmms)
}

predicate {:opaque} x86_ValidState(s:state)
    ensures x86_ValidState(s) ==> valid_state(s);
{
    valid_state(s)
}

////////////////////////////////////////////////////////////////////////
//
//  User annotations for memory and stack accessors' validity
//
////////////////////////////////////////////////////////////////////////

predicate ValidDstAddr(h:heap, addr:int, size:int)
{
    addr in h
 && match h[addr]
        case Mem8(_)  => size ==  8
        case Mem16(_) => size == 16
        case Mem32(_) => size == 32
        case Mem64(_) => size == 64
}

predicate ValidSrcAddr(h:heap, addr:int, size:int)
{
    ValidDstAddr(h, addr, size)
}

predicate HasStackSlot(s:Stack, slot:int)
{
    |s| > 0
 && slot in s[0]
}

predicate HasStackSlots(s:Stack, count:int)
{
    |s| > 0
 && (forall slot :: 0 <= slot < count ==> slot in s[0])
}

////////////////////////////////////////////////////////////////////////
//
//  Convenient shorthands
//
////////////////////////////////////////////////////////////////////////

predicate x86_branchRelation(s:state, r:state, cond:bool)
{
    //TODO: Not quite right, flags should depend on cond
    branchRelation(s, r, cond)
}

function method stack(slot:int):opr {  OStack(slot) }

function method MakeHeapOp(o:opr, offset:int) : opr
{
    if o.OReg? then OHeap(MReg(o.r, offset))
    else if o.OConst? then OHeap(MConst(o.n + offset))
    else OConst(42)
}

////////////////////////////////////////////////////////////////////////
//
//  Helper lemmas about control flow
//
////////////////////////////////////////////////////////////////////////

lemma evalWhile_validity(b:obool, c:code, n:nat, s:state, r:state)
    requires evalWhile(b, c, n, s, r);
    decreases c, 1, n;
    ensures  valid_state(s) && r.ok ==> valid_state(r);
{
    if valid_state(s) && r.ok && ValidOperand(s, 64, b.o1) && ValidOperand(s, 64, b.o2) && n > 0 {
        var s', r' :| evalOBool(s, b) && branchRelation(s, s', true) && evalCode(c, s', r') && evalWhile(b, c, n - 1, r', r);
        code_state_validity(c, s', r');
        evalWhile_validity(b, c, n - 1, r', r);
        assert valid_state(r);
    }
}

lemma lemma_FailurePreservedByBlock(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    ensures  !s.ok ==> !r.ok;
    decreases block;
{
    if !block.CNil? {
        var r' :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        lemma_FailurePreservedByCode(block.hd, s, r');
        lemma_FailurePreservedByBlock(block.tl, r', r);
    }
}

lemma lemma_FailurePreservedByCode(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    ensures  !s.ok ==> !r.ok;
{
    if c.Block? {
        lemma_FailurePreservedByBlock(c.block, s, r);
    }
}

lemma block_state_validity(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    requires valid_state(s);
    decreases block, 0;
    ensures  r.ok ==> valid_state(r);
{
    if block.va_CCons? {
        var r':state :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        code_state_validity(block.hd, s, r');
        if r'.ok {
            block_state_validity(block.tl, r', r);
        }
        else {
            lemma_FailurePreservedByBlock(block.tl, r', r);
        }
    }
}

lemma code_state_validity(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    requires valid_state(s);
    decreases c, 0;
    ensures  r.ok ==> valid_state(r);
{
    if r.ok {
        if c.Ins? {
            assert valid_state(r);
        } else if c.Block? {
            block_state_validity(c.block, s, r);
        } else if c.IfElse? {
            if ValidOperand(s, 64, c.ifCond.o1) && ValidOperand(s, 64, c.ifCond.o2) {
                var s' :| branchRelation(s, s', evalOBool(s, c.ifCond)) &&
                    if evalOBool(s, c.ifCond) then
                        evalCode(c.ifTrue, s', r)
                    else
                        evalCode(c.ifFalse, s', r);
                if evalOBool(s, c.ifCond) {
                    code_state_validity(c.ifTrue, s', r);
                } else {
                    code_state_validity(c.ifFalse, s', r);
                }
            }
            assert valid_state(r);
        } else if c.While? {
            var n:nat :| evalWhile(c.whileCond, c.whileBody, n, s, r);
            evalWhile_validity(c.whileCond, c.whileBody, n, s, r);
            assert valid_state(r);
        }
    }
}

////////////////////////////////////////////////////////////////////////
//
//  Lemmas that Vale invokes to cope with control flow
//
////////////////////////////////////////////////////////////////////////

lemma va_lemma_empty(s:va_state, r:va_state) returns(r':va_state)
    requires eval_code(Block(va_CNil()), s, r)
    ensures  s.ok ==> r.ok
    ensures  r' == s
    ensures  s.ok ==> r == s
{
    reveal_evalCodeOpaque();
    r' := s;
}


lemma va_lemma_block(b:codes, s0:va_state, r:va_state) returns(r1:va_state, c0:code, b1:codes)
    requires b.va_CCons?
    requires eval_code(Block(b), s0, r)
    ensures  b == va_CCons(c0, b1)
    //ensures  x86_ValidState(s0) && r1.ok ==> x86_ValidState(r1);
    ensures  eval_code(c0, s0, r1)
    ensures  eval_code(Block(b1), r1, r)
{
    reveal_evalCodeOpaque();
    c0 := b.hd;
    b1 := b.tl;
    if s0.ok {
        assert evalBlock(b, s0, r);
        var r':state :| evalCode(b.hd, s0, r') && evalBlock(b.tl, r', r);
        c0 := b.hd;
        b1 := b.tl;
        r1 := state(r'.regs, r'.xmms, r'.flags, r'.stack, r'.heap, r'.ok);
        if x86_ValidState(s0) {
            reveal_x86_ValidState();
            code_state_validity(c0, s0, r1);
        }
        assert eval_code(c0, s0, r1);
    } else {
        // If s0 isn't okay, we can do whatever we want,
        // so we ensure r1.ok is false, and hence eval_code(*, r1, *) is trivially true
        r1 := s0;
    }
}

lemma va_lemma_ifElse(ifb:obool, ct:code, cf:code, s:va_state, r:va_state) returns(cond:bool, s':va_state)
    requires !ifb.o1.OHeap? && !ifb.o2.OHeap?;
    requires x86_ValidState(s);
    requires va_is_src_opr64(ifb.o1, s) && ValidSourceOperand(s, 64, ifb.o1);
    requires va_is_src_opr64(ifb.o2, s) && ValidSourceOperand(s, 64, ifb.o2);
    requires eval_code(IfElse(ifb, ct, cf), s, r)
    ensures  if s.ok then
                    s'.ok
                 && x86_ValidState(s')
                 && cond == evalOBool(s, ifb)
                 && x86_branchRelation(s, s', cond)
                 && (if cond then eval_code(ct, s', r) else eval_code(cf, s', r))
             else
                true
                 //!r.ok;
{
    reveal_evalCodeOpaque();
    reveal_x86_ValidState();
    assert s.ok ==> evalIfElse(ifb, ct, cf, s, r);
    if s.ok {
        cond := evalOBool(s, ifb);
        var t:state :| branchRelation(s, t, cond)
                    && (if cond then evalCode(ct, t, r) else evalCode(cf, t, r));
        s' := state(t.regs, t.xmms, t.flags, t.stack, t.heap, t.ok);
    }
}

predicate{:opaque} evalWhileOpaque(b:obool, c:code, n:nat, s:state, r:state) { evalWhile(b, c, n, s, r) }
predicate evalWhileLax(b:obool, c:code, n:nat, s:state, r:state) { s.ok ==> evalWhileOpaque(b, c, n, s, r) }

predicate va_whileInv(b:obool, c:code, n:int, r1:va_state, r2:va_state)
{
    n >= 0 && x86_ValidState(r1) && evalWhileLax(b, c, n, r1, r2)
}

lemma va_lemma_while(b:obool, c:code, s:va_state, r:va_state) returns(n:nat, r':va_state)
    requires va_is_src_opr64(b.o1, s);
    requires va_is_src_opr64(b.o2, s);
    requires x86_ValidState(s);
    requires eval_code(While(b, c), s, r)
    ensures  evalWhileLax(b, c, n, s, r)
    //ensures  r'.ok
    ensures  x86_ValidState(r');
    ensures  r' == s
{
    reveal_evalCodeOpaque();
    reveal_x86_ValidState();
    reveal_evalWhileOpaque();
    if s.ok {
        assert evalCode(While(b, c), s, r);
        n :| evalWhile(b, c, n, s, r);
    } else {
        n := 0;
    }
    r' := s;
}

lemma va_lemma_whileTrue(b:obool, c:code, n:nat, s:va_state, r:va_state) returns(s':va_state, r':va_state)
    requires va_is_src_opr64(b.o1, s) && ValidSourceOperand(s, 64, b.o1);
    requires va_is_src_opr64(b.o2, s) && ValidSourceOperand(s, 64, b.o2);
    requires n > 0
    requires evalWhileLax(b, c, n, s, r)
    ensures  x86_ValidState(s) ==> x86_ValidState(s');
    ensures  evalWhileLax(b, c, n - 1, r', r)
    ensures  eval_code(c, s', r');
    ensures  x86_ValidState(s) ==> if s.ok then x86_branchRelation(s, s', true) else s' == s;
    ensures  if s.ok && x86_ValidState(s) then
                    s'.ok
                 && va_is_src_opr64(b.o1, s)
                 && evalOBool(s, b)
             else
                 true; //!r.ok;
{
    reveal_evalCodeOpaque();
    reveal_evalWhileOpaque();
    reveal_x86_ValidState();

    if !s.ok {
        s' := s;
        r' := s;
        return;
    }
    assert evalWhile(b, c, n, s, r); // TODO: Dafny reveal/opaque issue

    if x86_ValidState(s) {
        var s'':state, r'':state :| evalOBool(s, b) && branchRelation(s, s'', true) && evalCode(c, s'', r'')
                                && evalWhile(b, c, n - 1, r'', r);
        s' := state(s''.regs, s''.xmms, s''.flags, s''.stack, s''.heap, s''.ok);
        r' := state(r''.regs, r''.xmms, r''.flags, r''.stack, r''.heap, r''.ok);
        code_state_validity(c, s'', r'');
    } else {
        s' := s.(ok := false);
        r' := s.(ok := false);
    }
}

lemma va_lemma_whileFalse(b:obool, c:code, s:va_state, r:va_state) returns(r':va_state)
    requires va_is_src_opr64(b.o1, s) && ValidSourceOperand(s, 64, b.o1);
    requires va_is_src_opr64(b.o2, s) && ValidSourceOperand(s, 64, b.o2);
    requires evalWhileLax(b, c, 0, s, r)
    ensures  if s.ok then
                (if x86_ValidState(s) then
                    (r'.ok ==> x86_ValidState(r'))
                 && x86_branchRelation(s, r', false)
                 && !evalOBool(s, b)
                 && r.ok
                 else
                    true)
                  && r' == r
            else
                r' == s; //!r.ok;
{
    reveal_evalCodeOpaque();
    reveal_evalWhileOpaque();
    reveal_x86_ValidState();

    if !s.ok {
        r' := s;
        return;
    }
    r' := r;
}

}
