include "leakage-helpers.i.dfy"
include "vale.i.dfy"

module ARM_leakage_i {

import opened ARM_leakage_helpers_i
import opened ARM_vale_i

method mergeTaint(t1:taint, t2:taint)
    returns (taint:taint)

    ensures taint == specMergeTaint(t1, t2)
    ensures taint.Secret? == (t1.Secret? || t2.Secret?);
{
    if t1.Secret? || t2.Secret? {
        taint := Secret;
    } else {
        taint := Public;
    }
}

method operandTaint(op:operand, ts:taintState)
    returns (operandTaint:taint)

    ensures operandTaint == specOperandTaint(op, ts)
    ensures operandTaint.Public? && op.OReg? ==> op.r in ts.regTaint
{
    match op {
        case OConst(_)          => operandTaint := Public;
        case OShift(reg, _)     =>
            if reg in ts.regTaint {
                operandTaint := ts.regTaint[reg];
            } else {
                operandTaint := Secret;
            }
        case OReg(reg)          =>
            if reg in ts.regTaint {
                operandTaint := ts.regTaint[reg];
            } else {
                operandTaint := Secret;
            }
        case OSymbol(_)         => operandTaint := Public;
        case OSP                =>
            if SP in ts.regTaint {
                operandTaint := ts.regTaint[SP];
            }
            else {
                operandTaint := Secret;
            }
        case OLR                =>
            if LR in ts.regTaint {
                operandTaint := ts.regTaint[LR];
            }
            else {
                operandTaint := Secret;
            }
    }
}

method maddrDoesNotUseSecrets(base:operand, ofs:operand, ts:taintState)
    returns (pass:bool)
    ensures pass == specOperandDoesNotUseSecrets(base, ofs, ts);
{
    var baseTaint := operandTaint(base, ts);
    var ofsTaint := operandTaint(ofs, ts);
    pass := baseTaint.Public? && ofsTaint.Public?;
}

method setTaint(op:operand, ts:taintState, valueTaint:taint)
    returns (ts':taintState)
    requires op.OReg? || op.OSP? || op.OLR?;
    ensures  op.OReg? ==> ts' == ts.(regTaint := ts.regTaint[op.r := valueTaint]);
    ensures  op.OSP? ==> ts' == ts.(regTaint := ts.regTaint[SP := valueTaint]);
    ensures  op.OLR? ==> ts' == ts.(regTaint := ts.regTaint[LR := valueTaint]);
{
    match op {
        case OReg(reg)      =>
            ts' := ts.(regTaint := ts.regTaint[reg := valueTaint]);
        case OSP            =>
            ts' := ts.(regTaint := ts.regTaint[SP := valueTaint]);
        case OLR            =>
            ts' := ts.(regTaint := ts.regTaint[LR := valueTaint]);
    }
}

method checkIfAddConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.ADD?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src1 := ins.src1ADD;
    var src2 := ins.src2ADD;
    var dst := ins.dstADD;

    var src1Taint := operandTaint(src1, ts);
    var src2Taint := operandTaint(src2, ts);
    var srcTaint := mergeTaint(src1Taint, src2Taint);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OReg? || dst.OSP? || dst.OLR? {
        ts' := setTaint(dst, ts, taint);
        fixedTime := true;
    }
    else {
        fixedTime := false;
        ts' := ts;
    }
}

method checkIfSubConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.SUB?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src1 := ins.src1SUB;
    var src2 := ins.src2SUB;
    var dst := ins.dstSUB;

    var src1Taint := operandTaint(src1, ts);
    var src2Taint := operandTaint(src2, ts);
    var srcTaint := mergeTaint(src1Taint, src2Taint);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OReg? || dst.OSP? || dst.OLR? {
        ts' := setTaint(dst, ts, taint);
        fixedTime := true;
    }
    else {
        fixedTime := false;
        ts' := ts;
    }
}

method checkIfAndConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.AND?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src1 := ins.src1AND;
    var src2 := ins.src2AND;
    var dst := ins.dstAND;

    var src1Taint := operandTaint(src1, ts);
    var src2Taint := operandTaint(src2, ts);
    var srcTaint := mergeTaint(src1Taint, src2Taint);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OReg? || dst.OSP? || dst.OLR? {
        ts' := setTaint(dst, ts, taint);
        fixedTime := true;
    }
    else {
        fixedTime := false;
        ts' := ts;
    }
}

method checkIfEorConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.EOR?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src1 := ins.src1EOR;
    var src2 := ins.src2EOR;
    var dst := ins.dstEOR;

    var src1Taint := operandTaint(src1, ts);
    var src2Taint := operandTaint(src2, ts);
    var srcTaint := mergeTaint(src1Taint, src2Taint);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OReg? || dst.OSP? || dst.OLR? {
        ts' := setTaint(dst, ts, taint);
        fixedTime := true;
    }
    else {
        fixedTime := false;
        ts' := ts;
    }
}

method checkIfRevConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.REV?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcREV;
    var dst := ins.dstREV;

    var srcTaint := operandTaint(src, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OReg? || dst.OSP? || dst.OLR? {
        ts' := setTaint(dst, ts, taint);
        fixedTime := true;
    }
    else {
        fixedTime := false;
        ts' := ts;
    }
}

method checkIfMovConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.MOV?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcMOV;
    var dst := ins.dstMOV;

    var srcTaint := operandTaint(src, ts);

    if dst.OReg? || dst.OSP? || dst.OLR? {
        ts' := setTaint(dst, ts, srcTaint);
        fixedTime := true;
    }
    else {
        fixedTime := false;
        ts' := ts;
    }
}

method checkIfLdrConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.LDR?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var base := ins.baseLDR;
    var ofs := ins.ofsLDR;
    var srcTaint := ins.taintLDR;
    var dst := ins.rdLDR;
    var dstTaint := operandTaint(dst, ts);

    var ftSrc := maddrDoesNotUseSecrets(base, ofs, ts);
    if !ftSrc {
        fixedTime := false;
        return;
    }

    if !dst.OReg? && !dst.OSP? && !dst.OLR? {
        fixedTime := false;
        return;
    }


    fixedTime := true;
    ts' := setTaint(dst, ts, srcTaint);
}

method checkIfLdrGlobalConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.LDR_global?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var base := ins.baseLDR_global;
    var ofs := ins.ofsLDR_global;
    var dst := ins.rdLDR_global;

    var ftSrc := maddrDoesNotUseSecrets(base, ofs, ts);
    if !ftSrc {
        fixedTime := false;
        return;
    }

    if !dst.OReg? && !dst.OSP? && !dst.OLR? {
        fixedTime := false;
        return;
    }

    fixedTime := true;
    ts' := setTaint(dst, ts, Public);
}

method checkIfLdrRelocConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.LDR_reloc?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var dst := ins.rdLDR_reloc;

    if !dst.OReg? && !dst.OSP? && !dst.OLR? {
        fixedTime := false;
        return;
    }

    fixedTime := true;
    ts' := setTaint(dst, ts, Public);
}

method checkIfStrConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.STR?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.rdSTR;
    var srcTaint := operandTaint(src, ts);
    var base := ins.baseSTR;
    var ofs := ins.ofsSTR;
    var dstTaint := ins.taintSTR;

    var ftSrc := maddrDoesNotUseSecrets(base, ofs, ts);
    if !ftSrc {
        fixedTime := false;
        return;
    }

    if srcTaint.Secret? && dstTaint.Public? {
        fixedTime := false;
        return;
    }

    fixedTime := true;
    ts' := ts;
}

method checkIfStrGlobalConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.STR_global?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.rdSTR_global;
    var srcTaint := operandTaint(src, ts);
    var base := ins.baseSTR_global;
    var ofs := ins.ofsSTR_global;

    var ftSrc := maddrDoesNotUseSecrets(base, ofs, ts);
    if !ftSrc {
        fixedTime := false;
        return;
    }

    if srcTaint.Secret? {
        fixedTime := false;
        return;
    }

    fixedTime := true;
    ts' := ts;
}

method checkIfInstructionConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)
    ensures specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    match ins {
        case ADD(_,_,_)          => fixedTime, ts' := checkIfAddConsumesFixedTime(ins, ts);
        case SUB(_,_,_)          => fixedTime, ts' := checkIfSubConsumesFixedTime(ins, ts);
        case AND(_,_,_)          => fixedTime, ts' := checkIfAndConsumesFixedTime(ins, ts);
        case EOR(_,_,_)          => fixedTime, ts' := checkIfEorConsumesFixedTime(ins, ts);
        case REV(_,_)            => fixedTime, ts' := checkIfRevConsumesFixedTime(ins, ts);
        case MOV(_,_)            => fixedTime, ts' := checkIfMovConsumesFixedTime(ins, ts);
        case LDR(_,_,_,_)        => fixedTime, ts' := checkIfLdrConsumesFixedTime(ins, ts);
        case LDR_global(_,_,_,_) => fixedTime, ts' := checkIfLdrGlobalConsumesFixedTime(ins, ts);
        case LDR_reloc(_,_)      => fixedTime, ts' := checkIfLdrRelocConsumesFixedTime(ins, ts);
        case STR(_,_,_,_)        => fixedTime, ts' := checkIfStrConsumesFixedTime(ins, ts);
        case STR_global(_,_,_,_) => fixedTime, ts' := checkIfStrGlobalConsumesFixedTime(ins, ts);
    }
}

method { :timeLimitMultiplier 4 } checkIfBlockConsumesFixedTime(block:codes, ts:taintState)
    returns (fixedTime:bool, ts':taintState)
    ensures fixedTime ==> taintStateModInvariant(ts, ts');
    ensures fixedTime ==> specTaintCheckBlock(block, ts, ts', fixedTime);
    decreases *
{
    if block.CNil? {
        ts' := ts;
        fixedTime := true;
        return;
    }

    var ts_int;
    fixedTime, ts_int := checkIfCodeConsumesFixedTime(block.hd, ts);
    if (fixedTime == false) {
        ts' := ts;
        return;
    }

    assert specTaintCheckCode(block.hd, ts, ts_int, fixedTime);
    assert codePostconditions(block.hd, ts, ts_int, fixedTime);

    forall state1, state2, state1_int, state2_int |
        (evalCode(block.hd, state1, state1_int)
        && evalCode(block.hd, state2, state2_int)
        && state1.ok && state1_int.ok
        && state2.ok && state2_int.ok
        && constTimeInvariant(ts, state1, state2))
    ensures constTimeInvariant(ts_int, state1_int, state2_int)
    ensures taintStateModInvariant(ts, ts_int);
    {
    }

    fixedTime, ts' := checkIfBlockConsumesFixedTime(block.tl, ts_int);
    if (fixedTime == false) {
        return;
    }

    assert specTaintCheckBlock(block.tl, ts_int, ts', fixedTime);

    forall state1_int, state2_int, state1', state2' |
        evalBlock(block.tl, state1_int, state1')
        && evalBlock(block.tl, state2_int, state2')
        && state1_int.ok && state1'.ok
        && state2_int.ok && state2'.ok
        && constTimeInvariant(ts_int, state1_int, state2_int)
    ensures constTimeInvariant(ts', state1', state2');
    ensures taintStateModInvariant(ts_int, ts');
    {
    }

    forall state1, state2, state1_int, state2_int, state1', state2' |
            taintStateModInvariant(ts, ts_int)
            && taintStateModInvariant(ts_int, ts')
            && evalCode(block.hd, state1, state1_int)
            && evalCode(block.hd, state2, state2_int)
            && constTimeInvariant(ts, state1, state2)
            && evalBlock(block.tl, state1_int, state1')
            && evalBlock(block.tl, state2_int, state2')
            && constTimeInvariant(ts_int, state1_int, state2_int)
            && state1.ok && state1_int.ok && state1'.ok
            && state2.ok && state2_int.ok && state2'.ok
    ensures constTimeInvariant(ts', state1', state2');
    {
        assert constTimeInvariant(ts_int, state1_int, state2_int);
        assert taintStateModInvariant(ts, ts_int);
        assert taintStateModInvariant(ts_int, ts');
    }

    assert specTaintCheckCode(block.hd, ts, ts_int, fixedTime);
    assert specTaintCheckBlock(block.tl, ts_int, ts', fixedTime);

    forall state1,state2,state1',state2' |
        evalBlock(block, state1, state1')
        && evalBlock(block, state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2)
    ensures constTimeInvariant(ts', state1', state2');
    {
        var state1_int :|
            evalCode(block.hd, state1, state1_int)
            && evalBlock(block.tl, state1_int, state1');

        var state2_int :|
            evalCode(block.hd, state2, state2_int)
            && evalBlock(block.tl, state2_int, state2');

        assert specTaintCheckCode(block.hd, ts, ts_int, fixedTime);
        assert specTaintCheckBlock(block.tl, ts_int, ts', fixedTime);

        assert evalCode(block.hd, state1, state1_int);
        assert evalCode(block.hd, state2, state2_int);

        lemma_FailurePreservedByBlock(block.tl, state1_int, state1');
        lemma_FailurePreservedByBlock(block.tl, state2_int, state2');
        assert state1.ok && state1_int.ok;
        assert state2.ok && state2_int.ok;

        assert taintStateModInvariant(ts, ts_int);
        assert taintStateModInvariant(ts_int, ts');

        assert constTimeInvariant(ts, state1, state2);
        assert constTimeInvariant(ts_int, state1_int, state2_int);
        assert constTimeInvariant(ts', state1', state2');
    }

    forall
    ensures blockPostconditions(block, ts, ts', fixedTime)
    {
    }
}

method combineTaints<T>(t1:map<T,taint>, t2:map<T,taint>)
    returns (t:map<T,taint>)

    ensures  specCombineTaints(t1, t2, t)
    ensures forall e :: e in t1 ==> e in t;
    ensures forall e :: e in t2 ==> e in t;
{
    var keysT1 := domain(t1);
    var keysT2 := domain(t2);
    var keys := keysT1 + keysT2;
    var keys' := keys;

    t := map[];

    while (keys' != {})
        invariant forall k :: k in keys' ==> k in keys;
        invariant specCombineTaints(t1, t2, t)
        invariant forall e :: e in t1 ==> (e in t || e in keys');
        invariant forall e :: e in t2 ==> (e in t || e in keys');
        decreases |keys'|
    {
        var e :| e in keys';
        var taint := Public;

        if e in t1 && e in t2 {
            taint := t1[e];
            taint := mergeTaint(taint, t2[e]);
        } else if e in t1 && e !in t2 {
            taint := Secret;
        } else if e !in t1 && e in t2 {
            taint := Secret;
        }

        t := t[e := taint];
        keys' := keys' - { e };
    }
}

method combineTaintStates(ghost ts:taintState, ts1:taintState, ts2:taintState)
    returns (ts':taintState)
    requires taintStateModInvariant(ts, ts1);
    requires taintStateModInvariant(ts, ts2);
    ensures taintStateModInvariant(ts1, ts');
    ensures taintStateModInvariant(ts2, ts');
    ensures taintStateModInvariant(ts, ts');
    ensures specCombineTaintStates(ts1, ts2, ts');
{
    var regTaint := combineTaints(ts1.regTaint, ts2.regTaint);
    ts' := TaintState(regTaint);
}

lemma{:fuel evalCode, 0}{:fuel evalWhile, 0} lemma_checkIfLoopConsumesFixedTimeHelper(
    pred:obool,
    body:code,
    ts:taintState,
    state1:state,
    state2:state,
    state1':state,
    state2':state,
    n1:nat,
    n2:nat
    )
    requires state1.ok;
    requires state1'.ok;
    requires state2.ok;
    requires state2'.ok;
    requires specOperandTaint(pred.o1, ts).Public?;
    requires specOperandTaint(pred.o2, ts).Public?;
    requires constTimeInvariant(ts, state1, state2);
    requires evalWhile(pred, body, n1, state1, state1');
    requires evalWhile(pred, body, n2, state2, state2');
    requires forall pre_guard_state1:state, pre_guard_state2:state, loop_start1:state, loop_start2:state, loop_end1:state, loop_end2:state
                    {:trigger evalCode(body, loop_start1, loop_end1), evalCode(body, loop_start2, loop_end2), branchRelation(pre_guard_state1, loop_start1, true), branchRelation(pre_guard_state2, loop_start2, true), constTimeInvariant(ts, loop_end1, loop_end2)}
                    ::
                    pre_guard_state1.ok
                 && pre_guard_state2.ok
                 && ValidState(pre_guard_state1)
                 && ValidState(pre_guard_state2)
                 && loop_end1.ok
                 && loop_end2.ok
                 && ValidOperand(pred.o1)
                 && ValidOperand(pred.o2)
                 && evalOBool(pre_guard_state1, pred)
                 && evalOBool(pre_guard_state2, pred)
                 && branchRelation(pre_guard_state1, loop_start1, true)
                 && evalCode(body, loop_start1, loop_end1)
                 && branchRelation(pre_guard_state2, loop_start2, true)
                 && evalCode(body, loop_start2, loop_end2)
                 && constTimeInvariant(ts, pre_guard_state1, pre_guard_state2)
                 ==> constTimeInvariant(ts, loop_end1, loop_end2);
    decreases n1;
    ensures  constTimeInvariant(ts, state1', state2');
{
    lemma_ValuesOfPublic32BitOperandAreSame(ts, state1, state2, pred.o1);
    lemma_ValuesOfPublic32BitOperandAreSame(ts, state1, state2, pred.o2);
    assert evalOBool(state1, pred) == evalOBool(state2, pred);

    if n1 == 0 {
        return;
    }

    assert n2 != 0;

    var loop_start1:state, loop_end1:state :|    evalOBool(state1, pred)
                                            && branchRelation(state1, loop_start1, true)
                                            && evalCode(body, loop_start1, loop_end1)
                                            && evalWhile(pred, body, n1 - 1, loop_end1, state1');

    var loop_start2:state, loop_end2:state :|    evalOBool(state2, pred)
                                            && branchRelation(state2, loop_start2, true)
                                            && evalCode(body, loop_start2, loop_end2)
                                            && evalWhile(pred, body, n2 - 1, loop_end2, state2');

    assert loop_end1.ok && loop_end2.ok by
    {
        assert{:fuel evalWhile, 1} loop_end1.ok;
        assert{:fuel evalWhile, 1} loop_end2.ok;
    }
    lemma_checkIfLoopConsumesFixedTimeHelper(pred, body, ts, loop_end1, loop_end2, state1', state2', n1-1, n2-1);
}

method { :timeLimitMultiplier 2 } checkIfLoopConsumesFixedTime(pred:obool, body:code, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    ensures  fixedTime ==> taintStateModInvariant(ts, ts');
    ensures  fixedTime ==> isConstantTime(While(pred, body), ts);
    ensures  fixedTime ==> specTaintCheckCode(While(pred, body), ts, ts', fixedTime)
    ensures  fixedTime ==> isLeakageFree(While(pred, body), ts, ts');
    decreases *
{
    ts' := ts;
    var done := false;
    var next_ts:taintState, combined_ts:taintState, o1:taint, o2:taint, predTaint:taint;

    while (!done)
        invariant taintStateModInvariant(ts, ts');
        invariant taintStateSubset(ts, ts');
        invariant done ==> specOperandTaint(pred.o1, ts').Public?;
        invariant done ==> specOperandTaint(pred.o2, ts').Public?;
        invariant done ==>
                   forall pre_guard_state1:state, pre_guard_state2:state, loop_start1:state, loop_start2:state, loop_end1:state, loop_end2:state ::
                        pre_guard_state1.ok
                     && pre_guard_state2.ok
                     && ValidState(pre_guard_state1)
                     && ValidState(pre_guard_state2)
                     && loop_end1.ok
                     && loop_end2.ok
                     && ValidOperand(pred.o1)
                     && ValidOperand(pred.o2)
                     && evalOBool(pre_guard_state1, pred)
                     && evalOBool(pre_guard_state2, pred)
                     && branchRelation(pre_guard_state1, loop_start1, true)
                     && evalCode(body, loop_start1, loop_end1)
                     && branchRelation(pre_guard_state2, loop_start2, true)
                     && evalCode(body, loop_start2, loop_end2)
                     && constTimeInvariant(ts', pre_guard_state1, pre_guard_state2)
                     ==> constTimeInvariant(ts', loop_end1, loop_end2);
        decreases *;
    {
        o1 := operandTaint(pred.o1, ts');
        o2 := operandTaint(pred.o2, ts');
        predTaint := mergeTaint(o1, o2);

        if predTaint.Secret? {
            fixedTime := false;
            return;
        }

        assert specOperandTaint(pred.o1, ts').Public?;
        assert specOperandTaint(pred.o2, ts').Public?;

        fixedTime, next_ts := checkIfCodeConsumesFixedTime(body, ts');
        if !fixedTime {
            return;
        }

        combined_ts := combineTaintStates(ts, ts', next_ts);
        lemma_CombiningTaintStatesProducesSuperset(ts', next_ts, combined_ts);

        if (combined_ts == ts') {
            done := true;
            forall pre_guard_state1:state, pre_guard_state2:state, loop_start1:state, loop_start2:state, loop_end1:state, loop_end2:state |
                            pre_guard_state1.ok
                         && pre_guard_state2.ok
                         && ValidState(pre_guard_state1)
                         && ValidState(pre_guard_state2)
                         && constTimeInvariant(ts', pre_guard_state1, pre_guard_state2)
                         && loop_end1.ok
                         && loop_end2.ok
                         && ValidOperand(pred.o1)
                         && ValidOperand(pred.o2)
                         && evalOBool(pre_guard_state1, pred)
                         && evalOBool(pre_guard_state2, pred)
                         && branchRelation(pre_guard_state1, loop_start1, true)
                         && evalCode(body, loop_start1, loop_end1)
                         && branchRelation(pre_guard_state2, loop_start2, true)
                         && evalCode(body, loop_start2, loop_end2)
                ensures constTimeInvariant(ts', loop_end1, loop_end2);
            {
                assert constTimeInvariant(combined_ts, loop_start1, loop_start2);
                lemma_FailurePreservedByCode(body, loop_start1, loop_end1);
                lemma_FailurePreservedByCode(body, loop_start2, loop_end2);
                assert loop_start1.ok;
                assert loop_start2.ok;
                assert constTimeInvariant(next_ts, loop_end1, loop_end2);
                lemma_TaintSupersetImpliesPublicValuesAreSameIsPreserved(next_ts, combined_ts, loop_end1, loop_end2);
                assert constTimeInvariant(combined_ts, loop_end1, loop_end2);
            }
        }
        else {
            ts' := combined_ts;
        }
    }

    fixedTime := true;

    forall state1, state2, state1', state2' |
           evalCode(While(pred, body), state1, state1')
        && evalCode(While(pred, body), state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2)
        ensures constTimeInvariant(ts', state1', state2');
        ensures state1'.trace == state2'.trace;
    {
        var c := While(pred, body);
        assert evalCode(c, state1, state1');
        assert exists n:nat :: evalWhile(c.whileCond, c.whileBody, n, state1, state1');
        var n1:nat :| evalWhile(pred, body, n1, state1, state1');
        assert evalCode(c, state2, state2');
        assert exists n:nat :: evalWhile(c.whileCond, c.whileBody, n, state2, state2');
        var n2:nat :| evalWhile(pred, body, n2, state2, state2');
        lemma_TaintSupersetImpliesPublicValuesAreSameIsPreserved(ts, ts', state1, state2);
        lemma_checkIfLoopConsumesFixedTimeHelper(pred, body, ts', state1, state2, state1', state2', n1, n2);
    }
}

method checkIfCodeConsumesFixedTime(code:code, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    ensures fixedTime ==> specTaintCheckCode(code, ts, ts', fixedTime);
    ensures fixedTime ==> isConstantTime(code, ts);
    ensures fixedTime ==> taintStateModInvariant(ts, ts');
    ensures fixedTime ==> isLeakageFree(code, ts, ts');

    decreases *
{
    match code {
        case Ins(ins) =>
            fixedTime, ts' := checkIfInstructionConsumesFixedTime(ins, ts);
            if fixedTime == true {
                assert insPostconditions(ins, ts, ts', fixedTime);
            }

        case Block(block) =>
            fixedTime, ts' := checkIfBlockConsumesFixedTime(block, ts);

            if (fixedTime == false) {
                return;
            }

            assert specTaintCheckBlock(block, ts, ts', fixedTime);

            forall state1, state2, state1', state2' |
                (evalBlock(block, state1, state1')
                && evalBlock(block, state2, state2')
                && state1.ok && state1'.ok
                && state2.ok && state2'.ok
                && constTimeInvariant(ts, state1, state2))
            ensures constTimeInvariant(ts', state1', state2');
            ensures state1'.trace == state2'.trace;
            {
            }

        case IfElse(pred, ift, iff) =>
            var o1 := operandTaint(pred.o1, ts);
            var o2 := operandTaint(pred.o2, ts);
            var predTaint := mergeTaint(o1, o2);

            ts' := ts;
            if (o1.Secret? || o2.Secret?)
            {
                fixedTime := false;
                return;
            }

            var validIft:bool, validIff:bool;
            var tsIft:taintState, tsIff:taintState;

            validIft, tsIft := checkIfCodeConsumesFixedTime(ift, ts);
            if (validIft == false)
            {
                fixedTime := false;
                return;
            }

            validIff, tsIff := checkIfCodeConsumesFixedTime(iff, ts);
            if (validIff == false)
            {
                fixedTime := false;
                return;
            }

            fixedTime := true;
            ts' := combineTaintStates(ts, tsIft, tsIff);
            lemma_ifElse(pred, ift, iff, fixedTime, ts, tsIft, tsIff, ts');
            assert isLeakageFree(IfElse(pred, ift, iff), ts, ts');

        case While(pred, body) =>
            fixedTime, ts' := checkIfLoopConsumesFixedTime(pred, body, ts);

            forall
            ensures fixedTime ==> specTaintCheckCode(code, ts, ts', fixedTime)
            {
            }
    }
}

method checkIfCodeisLeakageFree(code:code, ts:taintState, tsExpected:taintState) returns (b:bool)
    ensures b ==> isLeakageFree(code, ts, tsExpected);
    ensures b ==> isConstantTime(code, ts);

    decreases *
{
    var fixedTime, ts' := checkIfCodeConsumesFixedTime(code, ts);

    b := fixedTime;

    if (b) {
        b := publicTaintsAreAsExpected(ts', tsExpected);

       if (b == false) {
            return;

        }

        assert  (forall s1, s2, r1, r2 :: isExplicitLeakageFreeGivenStates(code, ts, ts', s1, s2, r1, r2));
        lemma_ConsequencesOfIsLeakageFreeGivenStates(code, ts, ts');
        assert forall s1, s2, r1, r2 :: (evalCode(code, s1, r1)
            && evalCode(code, s2, r2)
            && s1.ok && r1.ok
            && s2.ok && r2.ok
            && constTimeInvariant(ts, s1, s2))
            ==> publicValuesAreSame(ts', r1, r2);
        assert forall s1, s2, r1, r2 :: (evalCode(code, s1, r1)
            && evalCode(code, s2, r2)
            && s1.ok && r1.ok
            && s2.ok && r2.ok
            && constTimeInvariant(ts, s1, s2)
            && publicValuesAreSame(ts', r1, r2)) ==> publicValuesAreSame(tsExpected, r1, r2);
        assert forall s1, s2, r1, r2 :: (evalCode(code, s1, r1)
            && evalCode(code, s2, r2)
            && s1.ok && r1.ok
            && s2.ok && r2.ok
            && constTimeInvariant(ts, s1, s2))
            ==> publicValuesAreSame(tsExpected, r1, r2);
        assert isLeakageFree(code, ts, tsExpected);
    }
}



}

