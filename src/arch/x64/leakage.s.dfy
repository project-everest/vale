include "def.s.dfy"
module x64_leakage_s {

import opened x64_def_s

datatype taintState = TaintState(stackTaint:map<int,taint>,
        regTaint:map<x86reg,taint>, xmmTaint:map<int,taint>, flagsTaint:taint)

datatype Value =
    Operand(o:operand)
    | Predicate(p:obool)

predicate publicXMMValuesAreSame(ts:taintState, s1:state, s2:state)
{
    forall x :: x in ts.xmmTaint && ts.xmmTaint[x].Public?
        ==> x in s1.xmms
         && x in s2.xmms
         && s1.xmms[x] == s2.xmms[x]
}

predicate publicFlagValuesAreSame(ts:taintState, s1:state, s2:state)
{
    ts.flagsTaint == Public ==>
        (s1.flags == s2.flags)
}

predicate publicHeapValuesAreSame(s1:state, s2:state)
{
    forall h :: h in s1.heap && s1.heap[h].t.Public?
        ==> (h in s2.heap && s1.heap[h] == s2.heap[h])
}

predicate publicRegisterValuesAreSame(ts:taintState, s1:state, s2:state)
{
    forall r :: r in ts.regTaint && ts.regTaint[r].Public?
        ==> r in s1.regs
         && r in s2.regs
         && s1.regs[r] == s2.regs[r]
}

predicate publicStackValuesAreSame(ts:taintState, s1:state, s2:state)
{
    forall s :: s in ts.stackTaint && ts.stackTaint[s].Public?
        ==> |s1.stack| > 0
         && |s2.stack| > 0
         && s in s1.stack[0]
         && s in s2.stack[0]
         && s1.stack[0][s] == s2.stack[0][s]
}

predicate publicValuesAreSame(ts:taintState, s1:state, s2:state)
{
       publicHeapValuesAreSame(s1, s2)
    && publicXMMValuesAreSame(ts, s1, s2)
    && publicFlagValuesAreSame(ts, s1, s2)
    && publicStackValuesAreSame(ts, s1, s2)
    && publicRegisterValuesAreSame(ts, s1, s2)
}

predicate constTimeInvariant(ts:taintState, s:state, s':state)
{
       publicValuesAreSame(ts, s, s')
    && s.trace == s'.trace
}

predicate isConstantTimeGivenStates(code:code, ts:taintState, s1:state,
        s2:state, r1:state, r2:state)
{
    (evalCode(code, s1, r1)
    && evalCode(code, s2, r2)
    && s1.ok && r1.ok
    && s2.ok && r2.ok
    && constTimeInvariant(ts, s1, s2))
        ==> r1.trace == r2.trace
}

predicate isConstantTime(code:code, ts:taintState)
{
    forall s1, s2, r1, r2 ::
        isConstantTimeGivenStates(code, ts, s1, s2, r1, r2)
}

predicate isExplicitLeakageFreeGivenStates(code:code, ts:taintState, ts':taintState, s1:state,
        s2:state, r1:state, r2:state)
{
      (evalCode(code, s1, r1)
    && evalCode(code, s2, r2)
    && s1.ok && r1.ok
    && s2.ok && r2.ok
    && constTimeInvariant(ts, s1, s2))
    ==> publicValuesAreSame(ts', r1, r2)
}

predicate isExplicitLeakageFree(code:code, ts:taintState, ts':taintState)
{
    forall s1, s2, r1, r2 ::
        isExplicitLeakageFreeGivenStates(code, ts, ts', s1, s2, r1, r2)
}

predicate isLeakageFree(code:code, ts:taintState, ts':taintState)
{
       isConstantTime(code, ts)
    && isExplicitLeakageFree(code, ts, ts')
}
}
