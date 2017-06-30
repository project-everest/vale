// Untrusted Dafny-Vale interface

include "def.s.dfy"
include "../../lib/util/words_and_bytes.i.dfy"

module x86_vale_i {

import opened x86_def_s
import opened words_and_bytes_i_temp = words_and_bytes_i

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
type va_state = State

type imm8 = uint8 

////////////////////////////////////////////////////////////////////////
//
//  Defining an enriched notion of state with heaplets
//
////////////////////////////////////////////////////////////////////////

datatype HeapletType = WordHeapletType | ByteHeapletType | QuadwordHeapletType
datatype ByteHeapletEntry     = ByteHeapletEntry(v:uint8, t:taint)
datatype WordHeapletEntry     = WordHeapletEntry(v:uint32, t:taint)
datatype QuadwordHeapletEntry = QuadwordHeapletEntry(v:Quadword, t:taint)
datatype Heaplet = ByteHeaplet(bytes:map<int, ByteHeapletEntry>)
                 | WordHeaplet(words:map<int, WordHeapletEntry>) 
                 | QuadwordHeaplet(quads:map<int, QuadwordHeapletEntry>)

type heaplet_id = int
type Heaplets = map<heaplet_id, Heaplet>

// This State augments the state type defined in x86def with a set of heaplets
datatype State = State(regs:map<x86reg, uint32>, xmms:map<int, Quadword>, 
                       flags:uint32, stack:Stack, heap:heap, trace:seq<observation>, 
                       ok:bool, heaplets:Heaplets)
function to_state(s:State):state { state(s.regs, s.xmms, s.flags, s.stack, s.heap, s.trace, s.ok) }


////////////////////////////////////////////////////////////////////////
//
//  Connecting Vale functions to Dafny functions 
//
////////////////////////////////////////////////////////////////////////

function va_get_ok(s:va_state):bool { s.ok }
function va_get_reg(r:x86reg, s:va_state):uint32 requires r in s.regs { s.regs[r] }
function va_get_Quadword(r:int, s:va_state):Quadword requires r in s.xmms { s.xmms[r] }
function va_get_flags(s:va_state):uint32 { s.flags }
function va_get_mem(s:va_state):Heaplets { s.heaplets }
function va_get_memory(s:va_state):heap { s.heap}
function va_get_stack(s:va_state):Stack { s.stack }

function va_update_ok(sM:va_state, sK:va_state):va_state { sK.(ok := sM.ok) }
function va_update_reg(r:x86reg, sM:va_state, sK:va_state):va_state 
    requires r in sM.regs 
{ sK.(regs := sK.regs[r := sM.regs[r]]) }
function va_update_Quadword(r:int, sM:va_state, sK:va_state):va_state 
    requires r in sM.xmms
{ sK.(xmms := sK.xmms[r := sM.xmms[r]]) }
function va_update_mem(sM:va_state, sK:va_state):va_state { sK.(heap := sM.heap, heaplets := sM.heaplets) }
function va_update_memory(sM:va_state, sK:va_state):va_state { sK.(heap := sM.heap) }
function va_update_flags(sM:va_state, sK:va_state):va_state { sK.(flags := sM.flags) }
function va_update_stack(sM:va_state, sK:va_state):va_state { sK.(stack := sM.stack) }

predicate va_is_src_operand_imm8(o:opr, s:va_state) { o.OConst? && 0 <= o.n < 256 }

predicate va_is_src_operand_uint32(o:opr, s:va_state) { o.OConst? || (o.OReg? && !o.r.X86Xmm?) }
predicate va_is_dst_operand_uint32(o:opr, s:va_state) { o.OReg? && !o.r.X86Xmm? }

predicate va_is_src_operand_Quadword(o:opr, s:va_state) { o.OReg? && o.r.X86Xmm? && 0 <= o.r.xmm <= 7 }
predicate va_is_dst_operand_Quadword(o:opr, s:va_state) { o.OReg? && o.r.X86Xmm? && 0 <= o.r.xmm <= 7 }

function va_eval_operand_imm8(s:va_state, o:opr):uint32
    requires va_is_src_operand_imm8(o, s);
{
    o.n
}

function va_eval_operand_uint32(s:va_state, o:opr):uint32
    requires va_is_src_operand_uint32(o, s);
{
    eval_op(to_state(s), o)
}

function va_eval_operand_Quadword(s:va_state, o:opr):Quadword
    requires va_is_src_operand_Quadword(o, s);
    requires o.r.xmm in s.xmms;
{
    Eval128BitOperand(to_state(s), o)
}

function va_update_operand(o:opr, sM:va_state, sK:va_state):va_state
    requires o.OReg?;
    requires o.r in sM.regs;
    requires o.r.X86Xmm? ==> o.r.xmm in sM.xmms;
{
    if o.r.X86Xmm? then va_update_Quadword(o.r.xmm, sM, sK) else va_update_reg(o.r, sM, sK)
}

predicate va_state_eq(s0:va_state, s1:va_state)
{
    s0.regs == s1.regs
 && s0.xmms == s1.xmms
 && s0.flags == s1.flags
 && s0.stack == s1.stack
 && s0.heap == s1.heap
 //&& s0.trace == s1.trace   // Functional verification doesn't care about the state of the trace, so let it float
 && s0.ok == s1.ok
 && s0.heaplets == s1.heaplets
}

predicate{:opaque} evalCodeOpaque(c:code, s0:state, sN:state)
{
    evalCode(c, s0, sN)
}

predicate eval_code(c:code, s:State, r:State) 
{ 
    s.ok ==> evalCodeOpaque(c, to_state(s), to_state(r)) 
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
predicate eval_weak(c:code, s:State, r:State) 
{ 
    s.ok && r.ok ==> evalCodeOpaque(c, to_state(s), to_state(r)) 
}

predicate va_ensure(b0:codes, b1:codes, s0:va_state, s1:va_state, sN:va_state)
{
    cTailIs(b0, b1)
 //&& s1.ok
 && eval_weak(b0.hd, s0, s1)
 && eval_code(Block(b1), s1, sN)
 && x86_ValidState(s1)
}

function method va_const_operand(n:uint32):opr { OConst(n) }
function method va_op_operand_reg(r:x86reg):opr { OReg(r) }
function method va_op_operand_Quadword(r:int):opr { OReg(X86Xmm(r)) }
function method va_op_cmp_reg(r:x86reg):opr { OReg(r) }

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

function method va_mem_code(oBase:opr, oOffset:opr, taint:taint):operand
    requires oBase.OReg?
    requires oOffset.OConst?
{
    OHeap(MReg(oBase.r, 4 * oOffset.n), taint)
}

function method va_mem_code_HeapPublic(oBase:opr, oOffset:opr):operand requires oBase.OReg? requires oOffset.OConst? { va_mem_code(oBase, oOffset, Public) }
function method va_mem_code_HeapSecret(oBase:opr, oOffset:opr):operand requires oBase.OReg? requires oOffset.OConst? { va_mem_code(oBase, oOffset, Secret) }

//function va_mem_lemma(h:HeapMeta, oBase:opr, oOffset:opr, taint:taint):opr
//    requires oBase.OReg?
//    requires oOffset.OConst?
//{
//    //OHeap(h.t, h.id, MReg(oBase.r, 4 * (oOffset.n as int)))
//    HeapOp(h, oBase.r, oOffset.n, taint)
//}

//function va_mem_lemma_HeapPublic(h:HeapMeta, oBase:opr, oOffset:opr):opr requires oBase.OReg? requires oOffset.OConst? { va_mem_lemma(h, oBase, oOffset, Public) }
//function va_mem_lemma_HeapSecret(h:HeapMeta, oBase:opr, oOffset:opr):opr requires oBase.OReg? requires oOffset.OConst? { va_mem_lemma(h, oBase, oOffset, Secret) }

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

predicate ValidHeapletAddr(h:Heaplet, addr:int)
{
    match h
        case WordHeaplet(w) => addr in w       // Word heaplets only occupy every 4th address
                            && addr + 1 !in w
                            && addr + 2 !in w
                            && addr + 3 !in w
        case ByteHeaplet(b) => addr in b
        case QuadwordHeaplet(s) =>  addr in s
                                 && addr + 1 !in s && addr + 2 !in s && addr +  3 !in s
                                 && addr + 4 !in s && addr + 5 !in s && addr +  6 !in s && addr +  7 !in s
                                 && addr + 8 !in s && addr + 9 !in s && addr + 10 !in s && addr + 11 !in s
                                 && addr +12 !in s && addr +13 !in s && addr + 14 !in s && addr + 15 !in s
}

predicate AddrInHeaplet(addr:int, h:Heaplet)
{
    match h
        case WordHeaplet(w)     => addr in w 
        case ByteHeaplet(b)     => addr in b
        case QuadwordHeaplet(s) => addr in s 
}

predicate ConsistentHeapletAddr(h:Heaplet, H:heap, addr:int)
{
    match h
        case WordHeaplet(_) => addr     in H
                            && addr + 1 in H
                            && addr + 2 in H
                            && addr + 3 in H
        case ByteHeaplet(_) => addr in H
        case QuadwordHeaplet(_) =>  addr      in H && addr +  1 in H && addr +  2 in H && addr +  3 in H
                                 && addr +  4 in H && addr +  5 in H && addr +  6 in H && addr +  7 in H
                                 && addr +  8 in H && addr +  9 in H && addr + 10 in H && addr + 11 in H
                                 && addr + 12 in H && addr + 13 in H && addr + 14 in H && addr + 15 in H
}

predicate AddrNotInHeaplet(addr:int, h:Heaplet)
{
    match h
        case WordHeaplet(w)     => addr !in w
        case ByteHeaplet(b)     => addr !in b
        case QuadwordHeaplet(s) => addr !in s
}

predicate ConsistentHeapletValue(h:Heaplet, H:heap, addr:int)
    requires ConsistentHeapletAddr(h, H, addr);
    requires ValidHeapletAddr(h, addr);
{
    match h
        case WordHeaplet(w) => w[addr].v == BytesToWord(H[addr+3].v,
                                                        H[addr+2].v,
                                                        H[addr+1].v,
                                                        H[addr].v)
        case ByteHeaplet(b) => b[addr].v == H[addr].v
        case QuadwordHeaplet(s) => s[addr].v == Quadword(
                BytesToWord(H[addr +  3].v, H[addr +  2].v, H[addr +  1].v, H[addr].v),
                BytesToWord(H[addr +  7].v, H[addr +  6].v, H[addr +  5].v, H[addr +  4].v),
                BytesToWord(H[addr + 11].v, H[addr + 10].v, H[addr +  9].v, H[addr +  8].v),
                BytesToWord(H[addr + 15].v, H[addr + 14].v, H[addr + 13].v, H[addr + 12].v))
}

predicate ConsistentHeapletTaint(h:Heaplet, H:heap, addr:int)
    requires ConsistentHeapletAddr(h, H, addr);
    requires ValidHeapletAddr(h, addr);
{
    match h
        case WordHeaplet(w) => w[addr].t == H[addr+3].t
                                         == H[addr+2].t
                                         == H[addr+1].t
                                         == H[addr].t
        case ByteHeaplet(b) => b[addr].t == H[addr].t
        case QuadwordHeaplet(s) => s[addr].t == H[addr     ].t == H[addr +  1].t == H[addr +  2].t == H[addr +  3].t
                                             == H[addr +  4].t == H[addr +  5].t == H[addr +  6].t == H[addr +  7].t
                                             == H[addr +  8].t == H[addr +  9].t == H[addr + 10].t == H[addr + 11].t
                                             == H[addr + 12].t == H[addr + 13].t == H[addr + 14].t == H[addr + 15].t
}

predicate AddrExclusive(heaplets:Heaplets, h_id:heaplet_id, h_id':heaplet_id, addr:int)
    requires h_id in heaplets
          && h_id' in heaplets 
          && h_id != h_id'
          && ValidHeapletAddr(heaplets[h_id], addr);
{
    var h := heaplets[h_id];
    var h' := heaplets[h_id'];
    match h
        case WordHeaplet(_) => AddrNotInHeaplet(addr, h')      // None of the four uint8 addresses are in another heaplet
                            && AddrNotInHeaplet(addr + 1, h')
                            && AddrNotInHeaplet(addr + 2, h')
                            && AddrNotInHeaplet(addr + 3, h')
        case ByteHeaplet(_) => AddrNotInHeaplet(addr, h')
        case QuadwordHeaplet(_) => AddrNotInHeaplet(addr,      h') && AddrNotInHeaplet(addr +  1, h') && AddrNotInHeaplet(addr +  2, h') && AddrNotInHeaplet(addr +  3, h')
                                && AddrNotInHeaplet(addr +  4, h') && AddrNotInHeaplet(addr +  5, h') && AddrNotInHeaplet(addr +  6, h') && AddrNotInHeaplet(addr +  7, h')
                                && AddrNotInHeaplet(addr +  8, h') && AddrNotInHeaplet(addr +  9, h') && AddrNotInHeaplet(addr + 10, h') && AddrNotInHeaplet(addr + 11, h')
                                && AddrNotInHeaplet(addr + 12, h') && AddrNotInHeaplet(addr + 13, h') && AddrNotInHeaplet(addr + 14, h') && AddrNotInHeaplet(addr + 15, h') 

}

predicate HeapletsExclusive(heaplets:Heaplets)
{
  forall addr, h_id, h_id' :: h_id in heaplets
                          && h_id' in heaplets 
                          && h_id != h_id'
                          && AddrInHeaplet(addr, heaplets[h_id])
                          ==> 
                             ValidHeapletAddr(heaplets[h_id], addr)
                          && AddrExclusive(heaplets, h_id, h_id', addr)
}

predicate HeapletsConsistent(heaplets:Heaplets, heap:heap)
{
  forall addr, h_id :: h_id in heaplets
                  && AddrInHeaplet(addr, heaplets[h_id])
                  ==> 
                      ValidHeapletAddr(heaplets[h_id], addr)
                   && ConsistentHeapletAddr(heaplets[h_id], heap, addr)
                   && ConsistentHeapletValue(heaplets[h_id], heap, addr)
                   && ConsistentHeapletTaint(heaplets[h_id], heap, addr)
}

predicate {:opaque} x86_ValidState(s:State)
    ensures x86_ValidState(s) ==> valid_state(to_state(s));
{
    valid_state(to_state(s))
 && HeapletsExclusive(s.heaplets) 
 && HeapletsConsistent(s.heaplets, s.heap)
}


////////////////////////////////////////////////////////////////////////
//
//  User annotations for memory and stack accessors' validity
//
////////////////////////////////////////////////////////////////////////

predicate ValidDstAddr(h:Heaplets, id:heaplet_id, addr:int, size:int) 
{
    id in h 
 && AddrInHeaplet(addr, h[id])
 && match h[id]
        case ByteHeaplet(_)     => size ==   8
        case WordHeaplet(_)     => size ==  32
        case QuadwordHeaplet(_) => size == 128
}

predicate ValidSrcAddr(h:Heaplets, id:heaplet_id, addr:int, size:int, taint:taint) 
{
    id in h 
 && AddrInHeaplet(addr, h[id])
 && match h[id]
        case ByteHeaplet(_)     => size ==   8 && h[id].bytes[addr].t == taint
        case WordHeaplet(_)     => size ==  32 && h[id].words[addr].t == taint
        case QuadwordHeaplet(_) => size == 128 && h[id].quads[addr].t == taint
}

predicate ValidSrcAddrs(h:Heaplets, id:heaplet_id, addr:int, size:int, taint:taint, num_bytes:int)
{
    // The "id in h" and "h[id].*Heaplet?" clauses below are redundant with ValidSrcAddr,
    // but it's important to have them here, so they're available without the need to trigger the quantifier
    id in h
 && if size == 8 then 
        h[id].ByteHeaplet? 
     && forall a {:trigger ValidSrcAddr(h, id, a, 8, taint) } 
                 {:trigger h[id].bytes[a] } 
                 {:trigger a in h[id].bytes } 
        :: addr <= a < addr+num_bytes ==> ValidSrcAddr(h, id, a, 8, taint)
    else if size == 32 then
        h[id].WordHeaplet? 
     && forall a {:trigger ValidSrcAddr(h, id, a, 32, taint) } 
                 {:trigger h[id].words[a] } 
                 {:trigger a in h[id].words } 
     :: addr <= a < addr+num_bytes && (a - addr) % 4 == 0 ==> ValidSrcAddr(h, id, a, 32, taint)
    else 
        h[id].QuadwordHeaplet?
     && forall a {:trigger ValidSrcAddr(h, id, a, 128, taint) } 
                 {:trigger h[id].quads[a] } 
                 {:trigger a in h[id].quads } 
     :: addr <= a < addr+num_bytes && (a - addr) % 16 == 0 ==> ValidSrcAddr(h, id, a, 128, taint)
}

predicate ValidDstAddrs(h:Heaplets, id:heaplet_id, addr:int, size:int, num_bytes:int)
{
    // The "id in h" and "h[id].*Heaplet?" clauses below are redundant with ValidSrcAddr,
    // but it's important to have them here, so they're available without the need to trigger the quantifier
    id in h
 && if size == 8 then 
        h[id].ByteHeaplet? 
     && forall a {:trigger ValidDstAddr(h, id, a, 8) } 
                 {:trigger h[id].bytes[a] } 
                 {:trigger a in h[id].bytes } 
        :: addr <= a < addr+num_bytes ==> ValidDstAddr(h, id, a, 8)
    else if size == 32 then
        h[id].WordHeaplet? 
     && forall a {:trigger ValidDstAddr(h, id, a, 32) } 
                 {:trigger h[id].words[a] } 
                 {:trigger a in h[id].words } 
     :: addr <= a < addr+num_bytes && (a - addr) % 4 == 0 ==> ValidDstAddr(h, id, a, 32)
    else 
        h[id].QuadwordHeaplet?
     && forall a {:trigger ValidDstAddr(h, id, a, 128) } 
                 {:trigger h[id].quads[a] } 
                 {:trigger a in h[id].quads } 
     :: addr <= a < addr+num_bytes && (a - addr) % 16 == 0 ==> ValidDstAddr(h, id, a, 128)
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

predicate x86_branchRelation(s:State, r:State, cond:bool)
{
    //TODO: Not quite right, flags should depend on cond
    branchRelation(to_state(s), to_state(r), cond)
}

function method stack(slot:int):opr {  OStack(slot) }

function method MakeHeapOp(o:opr, offset:int, taint:taint) : opr
{
    if o.OReg? then OHeap(MReg(o.r, offset), taint)
    else if o.OConst? then OHeap(MConst(o.n + offset), taint)
    else OConst(42)
}

////////////////////////////////////////////////////////////////////////
//
//  Tools for working with heaplets
//
////////////////////////////////////////////////////////////////////////


function UpdateHeaplets(s:State, addr:int, id:heaplet_id, taint:taint, v:uint32) : Heaplets
    requires ValidDstAddr(s.heaplets, id, addr, 32);
    requires s.heaplets[id].ByteHeaplet? ==> 0 <= v < 256;
{
    s.heaplets[id := match s.heaplets[id] 
                           case ByteHeaplet(b) => ByteHeaplet(b[addr := ByteHeapletEntry(v, taint)])
                           case WordHeaplet(w) => WordHeaplet(w[addr := WordHeapletEntry(v, taint)])
              ]
}

function UpdateHeaplets128(s:State, addr:int, id:heaplet_id, taint:taint, v:Quadword) : Heaplets
    requires ValidDstAddr(s.heaplets, id, addr, 128);
{
    var old_heaplet := s.heaplets[id];
    s.heaplets[id := old_heaplet.(quads := old_heaplet.quads[addr := QuadwordHeapletEntry(v, taint)])]
}

lemma {:timeLimitMultiplier 10} lemma_HeapletsUpdatedCorrectly32(s:State, r:State, addr:int, id:heaplet_id, taint:taint, v:uint32)
    requires x86_ValidState(s);
    requires ValidDstAddr(s.heaplets, id, addr, 32);
    requires valid_state(to_state(r));
    requires s.heaplets[id].ByteHeaplet? || s.heaplets[id].WordHeaplet?;
    requires s.heaplets[id].ByteHeaplet? ==> 0 <= v < 256;
    requires r.heap == UpdateHeap32(s.heap, addr, v, taint)
          && r.heaplets == UpdateHeaplets(s, addr, id, taint, v);
    ensures  x86_ValidState(r);
{
    reveal_x86_ValidState();
    lemma_WordToBytes_BytesToWord_inverses(v);

    // Establish HeapletsExclusive
    forall a, h_id, h_id' | h_id in r.heaplets
                          && h_id' in r.heaplets 
                          && h_id != h_id'
                          && AddrInHeaplet(a, r.heaplets[h_id])
        ensures ValidHeapletAddr(r.heaplets[h_id], a); 
        ensures AddrExclusive(r.heaplets, h_id, h_id', a);
    {
      assert ValidHeapletAddr(s.heaplets[h_id], a);
    }
    assert HeapletsExclusive(r.heaplets);

    // Establish HeapletsConsistent
    forall a, h_id | h_id in r.heaplets
                  && AddrInHeaplet(a, r.heaplets[h_id]) 
      ensures    ValidHeapletAddr(r.heaplets[h_id], a)
              && ConsistentHeapletAddr(r.heaplets[h_id], r.heap, a)
              && ConsistentHeapletValue(r.heaplets[h_id], r.heap, a)
              && ConsistentHeapletTaint(r.heaplets[h_id], r.heap, a);
    {
      assert h_id in s.heaplets;
      assert ValidHeapletAddr(s.heaplets[h_id], a);
    }
    assert HeapletsConsistent(r.heaplets, r.heap);
}

lemma {:timeLimitMultiplier 10} lemma_HeapletsUpdatedCorrectly128(s:State, r:State, addr:int, id:heaplet_id, taint:taint, v:Quadword)
    requires x86_ValidState(s);
    requires ValidDstAddr(s.heaplets, id, addr, 128);
    requires valid_state(to_state(r));
    requires r.heap == UpdateHeap128(s.heap, addr, v, taint)
          && r.heaplets == UpdateHeaplets128(s, addr, id, taint, v);
    ensures  x86_ValidState(r);
{
    reveal_x86_ValidState();
    lemma_WordToBytes_BytesToWord_inverses(v.lo);
    lemma_WordToBytes_BytesToWord_inverses(v.mid_lo);
    lemma_WordToBytes_BytesToWord_inverses(v.mid_hi);
    lemma_WordToBytes_BytesToWord_inverses(v.hi);

    // Establish HeapletsExclusive
    forall a, h_id, h_id' | h_id in r.heaplets
                             && h_id' in r.heaplets 
                             && h_id != h_id'
                             && AddrInHeaplet(a, r.heaplets[h_id])
        ensures ValidHeapletAddr(r.heaplets[h_id], a);
        ensures AddrExclusive(r.heaplets, h_id, h_id', a);
    {
      assert ValidHeapletAddr(s.heaplets[h_id], a);
    }
    assert HeapletsExclusive(r.heaplets);

    // Establish HeapletsConsistent
    forall a, h_id | h_id in r.heaplets
                     && AddrInHeaplet(a, r.heaplets[h_id])
        ensures 
           ValidHeapletAddr(r.heaplets[h_id], a)
        && ConsistentHeapletAddr(r.heaplets[h_id], r.heap, a)
        && ConsistentHeapletValue(r.heaplets[h_id], r.heap, a)
        && ConsistentHeapletTaint(r.heaplets[h_id], r.heap, a);
    {
      assert h_id in s.heaplets;
      assert ValidHeapletAddr(s.heaplets[h_id], a);
    }
    assert HeapletsConsistent(r.heaplets, r.heap);
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
    if valid_state(s) && r.ok && ValidOperand(s, 32, b.o1) && ValidOperand(s, 32, b.o2) && n > 0 {
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
            if ValidOperand(s, 32, c.ifCond.o1) && ValidOperand(s, 32, c.ifCond.o2) {
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
    ensures  s.ok ==> to_state(r) == to_state(s)
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
        assert evalBlock(b, to_state(s0), to_state(r));
        var r':state :| evalCode(b.hd, to_state(s0), r') && evalBlock(b.tl, r', to_state(r));
        c0 := b.hd;
        b1 := b.tl;
        r1 := State(r'.regs, r'.xmms, r'.flags, r'.stack, r'.heap, r'.trace, r'.ok, s0.heaplets);
        if x86_ValidState(s0) {
            reveal_x86_ValidState();
            code_state_validity(c0, to_state(s0), to_state(r1));
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
    requires va_is_src_operand_uint32(ifb.o1, s);
    requires va_is_src_operand_uint32(ifb.o2, s);
    requires eval_code(IfElse(ifb, ct, cf), s, r)
    ensures  if s.ok then
                    s'.ok
                 && x86_ValidState(s')
                 && cond == evalOBool(to_state(s), ifb)
                 && x86_branchRelation(s, s', cond)
                 && (if cond then eval_code(ct, s', r) else eval_code(cf, s', r))
             else
                true
                 //!r.ok;
{
    reveal_evalCodeOpaque();
    reveal_x86_ValidState();
    assert s.ok ==> evalIfElse(ifb, ct, cf, to_state(s), to_state(r));
    if s.ok {
        cond := evalOBool(to_state(s), ifb);
        var t:state :| branchRelation(to_state(s), t, cond)
                    && (if cond then evalCode(ct, t, to_state(r)) else evalCode(cf, t, to_state(r)));
        s' := State(t.regs, t.xmms, t.flags, t.stack, t.heap, t.trace, t.ok, s.heaplets);
    } 
}

predicate{:opaque} evalWhileOpaque(b:obool, c:code, n:nat, s:state, r:state) { evalWhile(b, c, n, s, r) }
predicate evalWhileLax(b:obool, c:code, n:nat, s:state, r:state) { s.ok ==> evalWhileOpaque(b, c, n, s, r) }

predicate va_whileInv(b:obool, c:code, n:int, r1:va_state, r2:va_state)
{
    n >= 0 && x86_ValidState(r1) && evalWhileLax(b, c, n, to_state(r1), to_state(r2))
}

lemma va_lemma_while(b:obool, c:code, s:va_state, r:va_state) returns(n:nat, r':va_state)
    requires va_is_src_operand_uint32(b.o1, s);
    requires va_is_src_operand_uint32(b.o2, s);
    requires x86_ValidState(s);
    requires eval_code(While(b, c), s, r)
    ensures  evalWhileLax(b, c, n, to_state(s), to_state(r))
    //ensures  r'.ok
    ensures  x86_ValidState(r');
    ensures  r' == s
{
    reveal_evalCodeOpaque();
    reveal_x86_ValidState();
    reveal_evalWhileOpaque();
    if s.ok {
        assert evalCode(While(b, c), to_state(s), to_state(r));
        n :| evalWhile(b, c, n, to_state(s), to_state(r));
    } else {
        n := 0;
    }
    r' := s;
}

lemma va_lemma_whileTrue(b:obool, c:code, n:nat, s:va_state, r:va_state) returns(s':va_state, r':va_state)
    requires va_is_src_operand_uint32(b.o1, s);
    requires va_is_src_operand_uint32(b.o2, s);
    requires n > 0
    requires evalWhileLax(b, c, n, to_state(s), to_state(r))
    ensures  x86_ValidState(s) ==> x86_ValidState(s');
    ensures  evalWhileLax(b, c, n - 1, to_state(r'), to_state(r))
    ensures  eval_code(c, s', r');
    ensures  x86_ValidState(s) ==> if s.ok then x86_branchRelation(s, s', true) else s' == s;
    ensures  if s.ok && x86_ValidState(s) then
                    s'.ok
                 && va_is_src_operand_uint32(b.o1, s)
                 && evalOBool(to_state(s), b)
                 && (s.heaplets == s'.heaplets == r'.heaplets)
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
    assert evalWhile(b, c, n, to_state(s), to_state(r)); // TODO: Dafny reveal/opaque issue

    if x86_ValidState(s) {
        var s'':state, r'':state :| evalOBool(to_state(s), b) && branchRelation(to_state(s), s'', true) && evalCode(c, s'', r'')
                                && evalWhile(b, c, n - 1, r'', to_state(r));
        s' := State(s''.regs, s''.xmms, s''.flags, s''.stack, s''.heap, s''.trace, s''.ok, s.heaplets);
        r' := State(r''.regs, r''.xmms, r''.flags, r''.stack, r''.heap, r''.trace, r''.ok, s.heaplets);
        code_state_validity(c, s'', r'');
    } else {
        s' := s.(ok := false);
        r' := s.(ok := false);
    }
}

lemma va_lemma_whileFalse(b:obool, c:code, s:va_state, r:va_state) returns(r':va_state)
    requires va_is_src_operand_uint32(b.o1, s);
    requires va_is_src_operand_uint32(b.o2, s);
    requires evalWhileLax(b, c, 0, to_state(s), to_state(r))
    ensures  if s.ok then
                (if x86_ValidState(s) then
                    (r'.ok ==> x86_ValidState(r'))
                 && x86_branchRelation(s, r', false)
                 && !evalOBool(to_state(s), b)
                 && r.ok
                 else 
                    true)
 
                 && to_state(r') == to_state(r)
                 && r'.heaplets == s.heaplets
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

    r' := r.(heaplets := s.heaplets);
}

}
