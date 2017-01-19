include "def.s.dfy"

module ARM_leakage_s {

import opened ARM_def_s

datatype taintState = TaintState(regTaint:map<ARMReg,taint>)

datatype Value =
    Operand(o:operand)
    | Predicate(p:obool)

predicate publicMemValuesAreSame(s1:state, s2:state)
{
    forall addr :: addr in s1.m.addresses && s1.m.addresses[addr].t.Public?
             ==> addr in s2.m.addresses && s2.m.addresses[addr] == s1.m.addresses[addr]
}

predicate publicRegisterValuesAreSame(ts:taintState, s1:state, s2:state)
{
    forall r :: r in ts.regTaint && ts.regTaint[r].Public?
        ==> r in s1.regs
         && r in s2.regs
         && s1.regs[r] == s2.regs[r]
}

predicate publicValuesAreSame(ts:taintState, s1:state, s2:state)
{
       publicMemValuesAreSame(s1, s2)
    && publicRegisterValuesAreSame(ts, s1, s2)
    && s1.m.globals == s2.m.globals
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
