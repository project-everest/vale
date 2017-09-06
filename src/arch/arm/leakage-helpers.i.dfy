include "leakage.s.dfy"

module ARM_leakage_helpers_i {

import opened ARM_leakage_s

function method domain<U, V>(m: map<U,V>): set<U>
    ensures forall i :: i in domain(m) <==> i in m;
{
    set s | s in m
}

predicate taintStateModInvariant(ts:taintState, ts':taintState)
{
    (forall r :: r in ts.regTaint ==> r in ts'.regTaint)
}

predicate insPostconditions(ins:ins, ts:taintState, ts':taintState,
        fixedTime:bool)
{
    fixedTime ==>
           (taintStateModInvariant(ts, ts')
        && forall state1, state2, state1', state2' ::
            (evalIns(ins, state1, state1')
            && evalIns(ins, state2, state2')
            && state1.ok && state1'.ok
            && state2.ok && state2'.ok
            && constTimeInvariant(ts, state1, state2))
                ==> constTimeInvariant(ts', state1', state2'))
}

predicate blockPostconditions(block:codes, ts:taintState, ts':taintState,
        fixedTime:bool)
{
    fixedTime ==>
           (taintStateModInvariant(ts, ts')
        && forall state1, state2, state1', state2' ::
            (evalBlock(block, state1, state1')
            && evalBlock(block, state2, state2')
            && state1.ok && state1'.ok
            && state2.ok && state2'.ok
            && constTimeInvariant(ts, state1, state2))
                ==> constTimeInvariant(ts', state1', state2'))
}

predicate codePostconditions(code:code, ts:taintState, ts':taintState,
        fixedTime:bool)
{
    fixedTime ==>
           (taintStateModInvariant(ts, ts')
        && forall state1, state2, state1', state2' ::
            (evalCode(code, state1, state1')
            && evalCode(code, state2, state2')
            && state1.ok && state1'.ok
            && state2.ok && state2'.ok
            && constTimeInvariant(ts, state1, state2))
                ==> constTimeInvariant(ts', state1', state2'))
}

predicate specTaintCheckIns(ins:ins, ts:taintState, ts':taintState,
        fixedTime:bool)
{
    insPostconditions(ins, ts, ts', fixedTime)
}

predicate specTaintCheckBlock(block:codes, ts:taintState, ts':taintState,
        fixedTime:bool)
{
    blockPostconditions(block, ts, ts', fixedTime)
    && if block.CNil? then
        fixedTime == true && ts' == ts
    else
        exists ts_int ::
            specTaintCheckCode(block.hd, ts, ts_int, fixedTime)
            && specTaintCheckBlock(block.tl, ts_int, ts', fixedTime)
}

predicate specTaintCheckCode(code:code, ts:taintState, ts':taintState,
        fixedTime:bool)
    decreases code, 0
{
       codePostconditions(code, ts, ts', fixedTime)
    && (code.Block? ==> specTaintCheckBlock(code.block, ts, ts', fixedTime))
}

function specMergeTaint(t1:taint, t2:taint) : taint
    ensures specMergeTaint(t1, t2).Public? ==> t1.Public? && t2.Public?;
{
    if t1.Secret? || t2.Secret? then
        Secret
    else
        Public
}

predicate specCombineTaints<T>(t1:map<T,taint>, t2:map<T,taint>,
        t:map<T,taint>)
{
    forall elem :: elem in t
        ==> (((elem in t1 || elem in t2)
                && (elem in t1 && elem in t2 ==>
                        t[elem] == specMergeTaint(t1[elem], t2[elem]))
                && (elem in t1 && elem !in t2 ==> t[elem].Secret?)
                && (elem in t2 && elem !in t1 ==> t[elem].Secret?))
            && (t[elem].Public? ==> ((elem in t1 ==> t1[elem].Public?)
                && (elem in t2 ==> t2[elem].Public?))))
}

predicate specCombineTaintStates(ts1:taintState, ts2:taintState, ts:taintState)
{
       specCombineTaints(ts1.regTaint, ts2.regTaint, ts.regTaint)
    && taintStateModInvariant(ts1, ts)
    && taintStateModInvariant(ts2, ts)
}

predicate taintSubset<T>(t1:map<T, taint>, t2:map<T, taint>)
{
    forall elem :: elem in t2 && t2[elem].Public? ==> elem in t1 && t1[elem].Public?
}

predicate taintStateSubset(ts1:taintState, ts2:taintState)
{
    taintSubset(ts1.regTaint, ts2.regTaint)
}

lemma lemma_CombiningTaintsProducesSuperset<T>(t1:map<T, taint>, t2:map<T, taint>, t':map<T, taint>)
    requires specCombineTaints(t1, t2, t');
    ensures  taintSubset(t1, t');
    ensures  taintSubset(t2, t');
{
}

lemma lemma_CombiningTaintStatesProducesSuperset(ts1:taintState, ts2:taintState, ts':taintState)
    requires specCombineTaintStates(ts1, ts2, ts');
    ensures  taintStateSubset(ts1, ts');
    ensures  taintStateSubset(ts2, ts');
{
    lemma_CombiningTaintsProducesSuperset(ts1.regTaint, ts2.regTaint, ts'.regTaint);
}

lemma lemma_TaintSupersetImpliesPublicValuesAreSameIsPreserved(ts:taintState, ts':taintState, s1:state, s2:state)
    requires publicValuesAreSame(ts, s1, s2);
    requires taintStateSubset(ts, ts');
    ensures  publicValuesAreSame(ts', s1, s2);
{
}

function method GetRegisterFromOperand(op:operand) : ARMReg
    requires op.OShift? || op.OReg? || op.OSP? || op.OLR?
{
    match op {
        case OShift(reg, s)       => reg
        case OReg(reg)            => reg
        case OSP                  => SP
        case OLR                  => LR
    }
}

function specOperandTaint(op:operand, ts:taintState) : taint
{
    if op.OConst? || op.OSymbol? then
        Public
    else
        var reg := GetRegisterFromOperand(op);
        if reg in ts.regTaint then ts.regTaint[reg] else Secret
}

function specTaint(value:Value, ts:taintState) : taint
{
    if value.Operand? then
        specOperandTaint(value.o, ts)
    else
        specMergeTaint(specOperandTaint(value.p.o1, ts), specOperandTaint(value.p.o2, ts))

}

predicate specOperandDoesNotUseSecrets(base:operand, ofs:operand, ts:taintState)
{
    var base_taint := specOperandTaint(base, ts);
    var ofs_taint := specOperandTaint(ofs, ts);
    base_taint.Public? && ofs_taint.Public?
}

lemma lemma_ValuesOfPublic32BitOperandAreSame(ts:taintState, s1:state, s2:state, op:operand)
    ensures    specOperandTaint(op, ts).Public?
            && publicValuesAreSame(ts, s1, s2)
            && ValidOperand(op)
            && ValidState(s1)
            && ValidState(s2)
            ==> OperandContents(s1, op) == OperandContents(s2, op);
{
}

lemma lemma_oBoolEvaluation(pred:obool, ift:code, iff:code, fixedTime:bool, ts:taintState)
    requires specOperandTaint(pred.o1, ts).Public?
        && specOperandTaint(pred.o2, ts).Public?;

    ensures fixedTime ==> (forall state1, state2, state1', state2' ::
           evalIfElse(pred, ift, iff, state1, state1')
        && evalIfElse(pred, ift, iff, state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2)
            ==> evalOBool(state1, pred) == evalOBool(state2, pred));
{
    forall state1, state2, state1', state2' |
           evalIfElse(pred, ift, iff, state1, state1')
        && evalIfElse(pred, ift, iff, state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2)
    ensures evalOBool(state1, pred) == evalOBool(state2, pred);
    {
        var state1_int :|
            branchRelation(state1, state1_int, evalOBool(state1, pred))
            && state1_int.ok
            && (if evalOBool(state1, pred) then
                    evalCode(ift, state1_int, state1')
                else
                    evalCode(iff, state1_int, state1'));

        var state2_int :|
            branchRelation(state2, state2_int, evalOBool(state2, pred))
            && state2_int.ok
            && (if evalOBool(state2, pred) then
                    evalCode(ift, state2_int, state2')
                else
                    evalCode(iff, state2_int, state2'));

        lemma_ValuesOfPublic32BitOperandAreSame(ts, state1, state2, pred.o1);
        lemma_ValuesOfPublic32BitOperandAreSame(ts, state1, state2, pred.o2);

        assert evalOBool(state1, pred) == evalOBool(state2, pred);
    }
}

lemma lemma_ifElse(pred:obool, ift:code, iff:code, fixedTime:bool,
        ts:taintState, tsIft:taintState, tsIff:taintState, ts':taintState)
    requires specOperandTaint(pred.o1, ts).Public?
        && specOperandTaint(pred.o2, ts).Public?;

    requires specTaintCheckCode(ift, ts, tsIft, fixedTime);
    requires specTaintCheckCode(iff, ts, tsIff, fixedTime);
    requires specCombineTaintStates(tsIft, tsIff, ts');

    requires forall state1, state2, state1', state2' ::
        evalCode(ift, state1, state1')
        && evalCode(ift, state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2)
    ==> constTimeInvariant(tsIft, state1', state2');

    requires forall state1, state2, state1', state2' ::
        evalCode(iff, state1, state1')
        && evalCode(iff, state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2)
    ==> constTimeInvariant(tsIff, state1', state2');

    ensures fixedTime ==> taintStateModInvariant(ts, ts');
    ensures codePostconditions(IfElse(pred, ift, iff), ts, ts', fixedTime);
    ensures fixedTime ==> isConstantTime(IfElse(pred, ift, iff), ts);
    ensures specTaintCheckCode(IfElse(pred, ift, iff), ts, ts', fixedTime);
    ensures fixedTime ==> isLeakageFree(IfElse(pred, ift, iff), ts, ts');
{
    if fixedTime == false {
        return;
    }

    lemma_oBoolEvaluation(pred, ift, iff, fixedTime, ts);

    forall state1, state2, state1', state2' |
           evalIfElse(pred, ift, iff, state1, state1')
        && evalIfElse(pred, ift, iff, state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2)
    ensures constTimeInvariant(ts', state1', state2');
    ensures state1'.trace == state2'.trace;
    {
        var state1_int :|
            branchRelation(state1, state1_int, evalOBool(state1, pred)) && state1_int.ok
            && (if evalOBool(state1, pred) then evalCode(ift, state1_int, state1') else evalCode(iff, state1_int, state1'));

        var state2_int :|
            branchRelation(state2, state2_int, evalOBool(state2, pred)) && state2_int.ok
            && (if evalOBool(state2, pred) then evalCode(ift, state2_int, state2') else evalCode(iff, state2_int, state2'));

        assert evalOBool(state1, pred) == evalOBool(state2, pred);
        if evalOBool(state1, pred) {
            assert evalCode(ift, state1_int, state1');
            assert evalCode(ift, state2_int, state2');
            assert state1_int.ok && state1'.ok;
            assert state2_int.ok && state2'.ok;
            assert constTimeInvariant(ts, state1_int, state2_int);
            assert constTimeInvariant(tsIft, state1', state2');
        } else {
            assert evalCode(iff, state1_int, state1');
            assert evalCode(iff, state2_int, state2');
            assert state1_int.ok && state1'.ok;
            assert state2_int.ok && state2'.ok;
            assert constTimeInvariant(ts, state1_int, state2_int);
            assert constTimeInvariant(tsIff, state1', state2');
        }

        assert evalOBool(state1, pred) ==> publicValuesAreSame(tsIft, state1', state2');
        assert (evalOBool(state1, pred) == false) ==> publicValuesAreSame(tsIff, state1', state2');

        forall
        ensures publicRegisterValuesAreSame(ts', state1', state2');
        {
        }

        assert evalCode(IfElse(pred, ift, iff), state1, state1');
        assert evalCode(IfElse(pred, ift, iff), state2, state2');

        assert state1'.trace == state2'.trace;
        assert constTimeInvariant(ts', state1', state2');
    }

    forall
    ensures taintStateModInvariant(tsIft, ts');
    ensures taintStateModInvariant(tsIff, ts');
    ensures taintStateModInvariant(ts, ts');
    {
    }
}

predicate method publicRegisterTaintsAreAsExpected(tsAnalysis:taintState, tsExpected:taintState)
{
    forall r :: r in tsExpected.regTaint && tsExpected.regTaint[r].Public?
        ==> (r in tsAnalysis.regTaint && tsAnalysis.regTaint[r].Public?)
}

predicate method publicTaintsAreAsExpected(tsAnalysis:taintState, tsExpected:taintState)
{
    publicRegisterTaintsAreAsExpected(tsAnalysis, tsExpected)
}

lemma lemma_ConsequencesOfIsLeakageFreeGivenStates(code:code, ts:taintState, ts':taintState)
    requires (forall s1, s2, r1, r2 :: isExplicitLeakageFreeGivenStates(code, ts, ts', s1, s2, r1, r2));
    ensures forall s1, s2, r1, r2 :: (evalCode(code, s1, r1)
            && evalCode(code, s2, r2)
            && s1.ok && r1.ok
            && s2.ok && r2.ok
            && constTimeInvariant(ts, s1, s2))
            ==> publicValuesAreSame(ts', r1, r2); 
{
    forall s1, s2, r1, r2 
        ensures (evalCode(code, s1, r1)
            && evalCode(code, s2, r2)
            && s1.ok && r1.ok
            && s2.ok && r2.ok
            && constTimeInvariant(ts, s1, s2))
            ==> publicValuesAreSame(ts', r1, r2);
    {
        assert isExplicitLeakageFreeGivenStates(code, ts, ts', s1, s2, r1, r2);
    }
}

}
