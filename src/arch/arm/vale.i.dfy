include "def.s.dfy"

module ARM_vale_i {

import opened ARM_vale_i_ARM_def_s = ARM_def_s

type opr = operand

//-----------------------------------------------------------------------------
// Vale Types
//-----------------------------------------------------------------------------
type va_int = int
type va_bool = bool
type va_operand = operand
type va_code = code
type va_codes = codes
type va_state = state

//-----------------------------------------------------------------------------
// Vale-Verification Interface
//-----------------------------------------------------------------------------

predicate {:opaque} eval_code(c:code, s:state, r:state)
{
    s.ok ==> evalCode(c, s, r)
}

/*
function va_eval_operand_uint32(s:state, o:operand): uint32
    requires ValidState(s)
    requires ValidOperand(o) || ValidSecondOperand(o)
{
    OperandContents(s,o)
}
*/

function va_eval_operand_addr(s:state, o:operand): uint32
    requires ValidState(s)
    requires ValidOperand(o)
{
    OperandContents(s,o)
}

function method va_CNil():codes { CNil }
predicate cHeadIs(b:codes, c:code) { b.va_CCons? && b.hd == c }
predicate cTailIs(b:codes, t:codes) { b.va_CCons? && b.tl == t }

predicate ValidRegState'(regs:map<ARMReg, uint32>)
{
    forall r:ARMReg :: r in regs
}

predicate va_require(b0:codes, c1:code, s0:va_state, sN:va_state)
{
    cHeadIs(b0, c1)
// && s0.ok
 && eval_code(Block(b0), s0, sN)
 && ValidState(s0)
 && ValidRegState'(s0.regs)
}

//// Weaker form of eval_code that we can actually ensure generically in instructions
//predicate eval_weak(c:code, s:va_state, r:va_state) 
//{ 
//    s.ok && r.ok ==> evalCodeOpaque(c, s, r) 
//}

predicate va_ensure(b0:codes, b1:codes, s0:va_state, s1:va_state, sN:va_state)
{
    cTailIs(b0, b1)
// && s1.ok
// && eval_code(b0.hd, s0, s1)
// && eval_weak(b0.hd, s0, s1)
 && eval_code(Block(b1), s1, sN)
 && ValidState(s1)
 && ValidRegState'(s1.regs)
}

function method fromOperand(o:operand):operand { o }
function method va_const_operand(n:uint32):operand { OConst(n) }
function method va_const_opr32(n:uint32):operand { OConst(n) }

function method va_cmp_eq(o1:operand, o2:operand):obool { OCmp(OEq, o1, o2) }
function method va_cmp_ne(o1:operand, o2:operand):obool { OCmp(ONe, o1, o2) }
function method va_cmp_le(o1:operand, o2:operand):obool { OCmp(OLe, o1, o2) }
function method va_cmp_ge(o1:operand, o2:operand):obool { OCmp(OGe, o1, o2) }
function method va_cmp_lt(o1:operand, o2:operand):obool { OCmp(OLt, o1, o2) }
function method va_cmp_gt(o1:operand, o2:operand):obool { OCmp(OGt, o1, o2) }

function method va_Block(block:codes):code { Block(block) }
function method va_IfElse(ifb:obool, ift:code, iff:code):code { IfElse(ifb, ift, iff) }
function method va_While(whileb:obool, whilec:code):code { While(whileb, whilec) }

function method va_get_block(c:code):codes requires c.Block? { c.block }
function method va_get_ifCond(c:code):obool requires c.IfElse? { c.ifCond }
function method va_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
function method va_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }
function method va_get_whileCond(c:code):obool requires c.While? { c.whileCond }
function method va_get_whileBody(c:code):code requires c.While? { c.whileBody }

function method va_op_operand_osp():operand { OSP }
function method va_op_opr32_osp():operand { OSP }
function method va_op_operand_olr():operand { OLR }
function method va_op_opr_reg_olr():operand { OLR }
function method va_op_opr32_olr():operand { OLR }
function method va_op_operand_reg(r:ARMReg):operand { OReg(r) }
function method va_op_opr32_reg(r:ARMReg):operand { OReg(r) }
function method va_op_opr_snd_reg(r:ARMReg):operand { OReg(r) }
function method va_op_opr_reg_reg(r:ARMReg):operand { OReg(r) }
function method va_op_cmp_reg(r:ARMReg):operand { OReg(r) }
function method va_coerce_opr32_to_opr_reg(o:opr):opr { o }
function method va_coerce_opr32_to_opr_snd(o:opr):opr { o }

function va_get_ok(s:va_state):bool { s.ok }
function va_get_reg(r:ARMReg, s:va_state):uint32 requires r in s.regs { s.regs[r] }
function va_get_mem(s:va_state):memmap { s.m.addresses }
function va_get_globals(s:va_state):map<operand, seq<uint32>> { s.m.globals }
function va_get_osp(s:va_state):uint32 
    requires SP in s.regs
{
    s.regs[SP]
}
function va_get_olr(s:va_state):uint32 
    requires LR in s.regs
{
    s.regs[LR]
}

function va_update_ok(sM:va_state, sK:va_state):state { sK.(ok := sM.ok) }
function va_update_reg(r:ARMReg, sM:va_state, sK:va_state):va_state
    requires r in sM.regs
{ sK.(regs := sK.regs[r := sM.regs[r]]) }
function va_update_mem(sM:va_state, sK:va_state):va_state {
    sK.(m := sK.m.(addresses := sM.m.addresses))
}
function va_update_osp(sM:va_state, sK:va_state):va_state
    requires SP in sM.regs
{
    va_update_reg(SP, sM, sK)
}
function va_update_olr(sM:va_state, sK:va_state):va_state
    requires LR in sM.regs
{
    va_update_reg(LR, sM, sK)
}

function va_update_operand_opr32(o:operand, sM:va_state, sK:va_state):va_state
    requires ValidRegOperand(o);
    requires match o
                case OReg(r) => r in sM.regs
                case OLR => LR in sM.regs 
                case OSP => SP in sM.regs 
{ 
    va_update_operand(o, sM, sK)
}
	
function va_update_operand(o:operand, sM:va_state, sK:va_state):va_state
    requires ValidRegOperand(o);
    requires match o
                case OReg(r) => r in sM.regs
                case OLR => LR in sM.regs 
                case OSP => SP in sM.regs 
{ 
    match o
        case OReg(r) => va_update_reg(o.r, sM, sK)
        case OLR => va_update_reg(LR, sM, sK)
        case OSP => va_update_reg(SP, sM, sK)
}

function method GetProbableReg(o:operand) : ARMReg { if o.OReg? then o.r else R0 }

type va_value_opr32 = uint32
type va_operand_opr32 = va_operand
predicate va_is_src_opr32(o:operand, s:va_state) { ValidOperand(o) }
predicate va_is_dst_opr32(o:operand, s:va_state) { ValidRegOperand(o) }

type reg = uint32
type va_value_opr_reg = reg
type va_operand_opr_reg = va_operand
predicate va_is_src_opr_reg(o:operand, s:va_state) { ValidRegOperand(o) }

type snd = uint32
type va_value_opr_snd = snd
type va_operand_opr_snd = va_operand
predicate va_is_src_opr_snd(o:operand, s:va_state) { ValidOperand(o) && o.OReg? }

predicate va_is_src_operandglobal(o:operand, s:va_state) { ValidGlobal(o) }

function va_eval_opr32(s:va_state, o:operand):uint32
    requires va_is_src_opr32(o, s);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function va_eval_opr_reg(s:va_state, o:operand):reg
    requires va_is_src_opr_reg(o, s);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function va_eval_opr_snd(s:va_state, o:operand):snd
    requires va_is_src_opr_snd(o, s);
    requires ValidState(s)
{
    OperandContents(s,o)
}

type global = string
function va_eval_operandglobal(s:va_state, o:operand):global
    requires va_is_src_operandglobal(o, s);
{
    o.sym
}

predicate va_state_eq(s0:va_state, s1:va_state)
{
    s0.regs == s1.regs
 && s0.m == s1.m
 && s0.ok == s1.ok
}

predicate ValidAddr(m:memmap, addr:int)
{
    ValidMem(addr)
 && addr in m
}

predicate ValidSrcAddr(m:memmap, addr:int)
{
    ValidMem(addr)
 && addr in m
}

predicate ValidAddrs(mem:memmap, base:int, num_uint32s:int)
{
    //forall j {:trigger ValidAddr(mem, base+j*4)} {:trigger  base+j*4 in mem } :: 0 <= j < num_uint32s ==> ValidAddr(mem, base + j*4)
    forall addr {:trigger ValidAddr(mem, addr)} 
                {:trigger addr in mem } :: 
        base <= addr < base + num_uint32s*4 && (addr - base) % 4 == 0 ==> ValidAddr(mem, addr)
}

predicate ValidSrcAddrs(mem:memmap, base:int, num_uint32s:int)
{
    forall addr {:trigger ValidAddr(mem, addr)} {:trigger ValidSrcAddr(mem, addr)} 
                {:trigger addr in mem } :: 
        base <= addr < base + num_uint32s*4 && (addr - base) % 4 == 0 ==> ValidSrcAddr(mem, addr)
    //forall j {:trigger ValidAddr(mem, base+j*4)} {:trigger ValidSrcAddr(mem, base+j*4)} {:trigger  base+j*4 in mem } :: 
//        0 <= j < num_uint32s ==> ValidSrcAddr(mem, base + j*4)
}

//-----------------------------------------------------------------------------
// Useful invariants preserved by instructions
//-----------------------------------------------------------------------------
predicate AllMemInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m == s'.m
}

predicate GlobalsInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m.globals == s'.m.globals
}

predicate AddrMemInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m.addresses == s'.m.addresses
}

predicate AllRegsInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.regs == s'.regs
}

//-----------------------------------------------------------------------------
// Control Flow Lemmas
//-----------------------------------------------------------------------------

predicate valid_state(s:state) { ValidState(s) }

lemma va_lemma_empty(s:va_state, r:va_state) returns(r':va_state)
    requires eval_code(Block(va_CNil()), s, r)
    ensures  s.ok ==> r.ok
    ensures  r' == s
    ensures  s.ok ==> r == s
    ensures  forall b, s' :: eval_code(b, r, s') ==> eval_code(b, s, s')
{
    reveal_eval_code();
    r' := s;
}

lemma evalWhile_validity(b:obool, c:code, n:nat, s:state, r:state)
    requires evalWhile(b, c, n, s, r);
    decreases c, 1, n;
    ensures  valid_state(s) && r.ok ==> valid_state(r);
{
    if valid_state(s) && r.ok && ValidOperand(b.o1) && ValidOperand(b.o2) && n > 0 {
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
            if ValidOperand(c.ifCond.o1) && ValidOperand(c.ifCond.o2) {
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

lemma va_lemma_block(b:codes, s0:va_state, r:va_state) returns(r1:va_state, c0:code, b1:codes)
    requires b.va_CCons?
    requires eval_code(Block(b), s0, r)
    ensures  b == va_CCons(c0, b1)
    ensures  ValidState(s0) && r1.ok ==> ValidState(r1);
    ensures  eval_code(c0, s0, r1)
    ensures  eval_code(Block(b1), r1, r)
{
    reveal_eval_code();
    c0 := b.hd;
    b1 := b.tl;
    if s0.ok {
        assert evalBlock(b, s0, r);
        var r':state :| evalCode(b.hd, s0, r') && evalBlock(b.tl, r', r);
        r1 := r';
        if ValidState(s0) {
            code_state_validity(c0, s0, r1);
        }
        assert eval_code(c0, s0, r1);
    } else {
        r1 := s0;
    }
}

lemma va_lemma_ifElse(ifb:obool, ct:code, cf:code, s:va_state, r:va_state) returns(cond:bool, s':va_state)
    requires ValidState(s) && ValidOperand(ifb.o1) && ValidOperand(ifb.o2)
    requires eval_code(IfElse(ifb, ct, cf), s, r)
    ensures  forall c, t, t' :: eval_code(c, t, t') == (t.ok ==> eval_code(c, t, t'));
    ensures  if s.ok then
                    s'.ok
                 && ValidState(s')
                 && cond == evalOBool(s, ifb)
                 && branchRelation(s, s', cond)
                 && (if cond then eval_code(ct, s', r) else eval_code(cf, s', r))
             else
                 true //!r.ok;
{
    reveal_eval_code();
    if s.ok {
        assert evalIfElse(ifb, ct, cf, s, r);
        cond := evalOBool(s, ifb);
        var t:state :| branchRelation(s, t, cond) && (if cond then evalCode(ct, t, r) else evalCode(cf, t, r));
        s' := t;
    }
}

predicate{:opaque} evalWhileOpaque(b:obool, c:code, n:nat, s:state, r:state)
{
    evalWhile(b, c, n, s, r)
}

predicate evalWhileLax(b:obool, c:code, n:nat, s:state, r:state)
{
    s.ok ==> evalWhileOpaque(b, c, n, s, r)
}

predicate ValidRegStateTransparent(regs:map<ARMReg, uint32>)
{
    forall r:ARMReg :: r in regs
}

predicate ValidStateTransparent(s:state)
    ensures ValidStateTransparent(s) ==> ValidRegStateTransparent(s.regs);
{
    reveal_ValidRegState();
    ValidState(s)
}

predicate va_whileInv(b:obool, c:code, n:int, r1:va_state, r2:va_state)
{
    n >= 0 && ValidStateTransparent(r1) && evalWhileLax(b, c, n, r1, r2)
}

lemma va_lemma_while(b:obool, c:code, s:va_state, r:va_state) returns(n:nat, r':va_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2)
    requires eval_code(While(b, c), s, r)
    ensures  evalWhileLax(b, c, n, s, r)
    //ensures  r'.ok
    ensures  ValidState(r');
    ensures  r' == s
    ensures  forall c', t, t' :: eval_code(c', t, t') == (t.ok ==> eval_code(c', t, t'));
{
    reveal_eval_code();
    reveal_evalWhileOpaque();
//    unpack_eval_while(b, c, s, r);
    if s.ok {
        assert evalCode(While(b, c), s, r);
        n :| evalWhile(b, c, n, s, r);
    } else {
        n := 0;
    }
    r' := s;
}

lemma va_lemma_whileTrue(b:obool, c:code, n:int, s:va_state, r:va_state) returns(s':va_state, r':va_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2);
    requires n > 0
    requires evalWhileLax(b, c, n, s, r)
    //ensures  ValidState(s) && r'.ok ==> ValidState(r');
    ensures  ValidState(s) ==> ValidState(s');
    ensures  evalWhileLax(b, c, n-1, r', r)
    ensures  eval_code(c, s', r');
    ensures  ValidState(s) ==> if s.ok then branchRelation(s, s', true) else s' == s;
    ensures  forall c', t, t' :: eval_code(c', t, t') == (t.ok ==> eval_code(c', t, t'));
    ensures  if s.ok then
                    s'.ok
                 //&& evalGuard(s, b, s')
                 && evalOBool(s, b)
                 //&& eval_code(c, s', r')
                 //&& evalWhileOpaque(b, c, n - 1, r', r)
             else
                 true //!r.ok;
{
    reveal_eval_code();
    reveal_evalWhileOpaque();

    if !s.ok {
        s' := s;
        r' := s;
        return;
    }
    assert evalWhile(b, c, n, s, r); // TODO: Dafny reveal/opaque issue

    if ValidState(s) {
        var s'', r'':state :| evalOBool(s, b) && branchRelation(s, s'', true) && evalCode(c, s'', r'')
            && evalWhile(b, c, n - 1, r'', r);
        code_state_validity(c, s'', r'');
        s' := s'';
        r' := r'';
    } else {
        s' := s.(ok := false);
        r' := s.(ok := false);
    }
}

lemma va_lemma_whileFalse(b:obool, c:code, s:va_state, r:va_state) returns(r':va_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2);
    requires evalWhileLax(b, c, 0, s, r)
    ensures  forall c', t, t' :: eval_code(c', t, t') == (t.ok ==> eval_code(c', t, t'));
    ensures  if s.ok then
                    (if ValidState(s) then
                        (r'.ok ==> ValidState(r'))
                     && branchRelation(s, r', false)
                     && !evalOBool(s, b)
                     && r.ok
                     && r' == r
                     else 
                        true)
                 && r' == r
            else
                r' == s
{
    reveal_eval_code();
    reveal_evalWhileOpaque();

    if !s.ok {
        r' := s;
        return;
    }

    r' := r;
}

}
