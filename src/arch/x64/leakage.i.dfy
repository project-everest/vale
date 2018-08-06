include "leakage-helpers.i.dfy"
include "vale.i.dfy"
include "leakage.s.dfy"

module x64_const_time_i {

import opened x64_leakage_helpers
import opened x64_vale_i
import opened x64_leakage_s

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
    ensures operandTaint == Public ==>
        ((op.OReg?   ==>
            ((op.r.X86Xmm? && op.r.xmm in ts.xmmTaint)
            || op.r in ts.regTaint))
        && (op.OStack? ==> op.s in ts.stackTaint))
{
    match op {
        case OConst(_)          => operandTaint := Public;
        case OReg(reg)          =>
            if reg.X86Xmm? {
                if reg.xmm in ts.xmmTaint {
                    operandTaint := ts.xmmTaint[reg.xmm];
                } else {
                    operandTaint := Secret;
                }
            } else if reg in ts.regTaint {
                operandTaint := ts.regTaint[reg];
            } else {
                operandTaint := Secret;
            }

        case OStack(slot)       =>
            if slot in ts.stackTaint {
                operandTaint := ts.stackTaint[slot];
            } else {
                operandTaint := Secret;
            }
        case OHeap(addr, taint) => {
            operandTaint := taint;
        }
    }
}

method operandTaint64(op:operand, ts:taintState)
    returns (operandTaint:taint)

    ensures operandTaint == specOperandTaint64(op, ts)
    ensures operandTaint == Public ==>
        ((op.OReg?   ==>
            ((op.r.X86Xmm? && op.r.xmm in ts.xmmTaint)
            || op.r in ts.regTaint))
        && (op.OStack? ==> op.s in ts.stackTaint))
{
    match op {
        case OConst(_)          => operandTaint := Public;
        case OReg(reg)          =>
            if reg.X86Xmm? {
                if reg.xmm in ts.xmmTaint {
                    operandTaint := ts.xmmTaint[reg.xmm];
                } else {
                    operandTaint := Secret;
                }
            } else if reg in ts.regTaint {
                operandTaint := ts.regTaint[reg];
            } else {
                operandTaint := Secret;
            }

        case OStack(slot)       =>
            if slot in ts.stackTaint && slot + 1 in ts.stackTaint {
                var taint1 := ts.stackTaint[slot];
                var taint2 := ts.stackTaint[slot + 1];
                operandTaint := mergeTaint(taint1, taint2);
            } else {
                operandTaint := Secret;
            }
        case OHeap(addr, taint) => {
            operandTaint := taint;
        }
    }
}

method maddrDoesNotUseSecrets(addr:maddr, ts:taintState)
    returns (pass:bool)

    ensures pass == specOperandDoesNotUseSecrets(OHeap(addr, Public), ts);
{
    if addr.MConst? {
        pass := true;
    } else if addr.MReg? {
//        assert addr.reg.X86Xmm? == false;
        var taint := operandTaint(OReg(addr.reg), ts);
        pass := taint.Public?;
    } else {
        assert addr.MIndex?;
        var baseOperand := OReg(addr.base);
        var indexOperand := OReg(addr.index);

        var baseTaint := operandTaint(baseOperand, ts);
        var indexTaint := operandTaint(indexOperand, ts);

        pass := baseTaint.Public? && indexTaint.Public?;
    }
}

method operandDoesNotUseSecrets(o:operand, ts:taintState)
    returns (pass:bool)

    ensures  pass == specOperandDoesNotUseSecrets(o, ts);
{
    if o.OConst? || o.OReg? || o.OStack? {
        pass := true;
    } else {
        assert o.OHeap?;
        pass := maddrDoesNotUseSecrets(o.addr, ts);
    }
}

method setTaint(value:Value, ts:taintState, valueTaint:taint)
    returns (ts':taintState)

    requires value.Operand?;

    requires value.o.OConst? == false;
    requires value.o.OHeap? == false;
    ensures value.o.OReg?
        ==> ts' == ts.(regTaint := ts.regTaint[value.o.r := valueTaint]);
    ensures value.o.OStack?
        ==> ts' == ts.(stackTaint := ts.stackTaint[value.o.s := valueTaint]);
    ensures value.o.OHeap?  ==> ts == ts';
{
    match value.o {
        case OReg(reg)      =>
            ts' := ts.(regTaint := ts.regTaint[reg := valueTaint]);

        case OStack(slot)   =>
            ts' := ts.(stackTaint := ts.stackTaint[slot := valueTaint]);

        case OHeap(_, _)    =>
            ts' := ts;
    }
}

method setTaint64(value:Value, ts:taintState, valueTaint:taint)
    returns (ts':taintState)

    requires value.Operand?;

    requires value.o.OConst? == false;
    requires value.o.OHeap? == false;
    ensures value.o.OReg?
        ==> ts' == ts.(regTaint := ts.regTaint[value.o.r := valueTaint]);
    ensures value.o.OStack?
        ==> ts' == ts.(stackTaint := ts.stackTaint[value.o.s := valueTaint][value.o.s + 1 := valueTaint]);
    ensures value.o.OHeap?  ==> ts == ts';
{
    match value.o {
        case OReg(reg)      =>
            ts' := ts.(regTaint := ts.regTaint[reg := valueTaint]);

        case OStack(slot)   =>
            ts' := ts.(stackTaint := ts.stackTaint[slot := valueTaint][slot + 1 := valueTaint]);

        case OHeap(_, _)    =>
            ts' := ts;
    }
}

method checkIfMov32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Mov32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcMov;
    var dst := ins.dstMov;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint(src, ts);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        fixedTime := fixedTime && !(srcTaint.Secret? && dst.taint.Public?);
        ts' := ts;
    } else {
        ts' := setTaint(Operand(dst), ts, srcTaint);
    }

    if fixedTime == false {
        return;
    }

    lemma_Mov32Helper1(ins, fixedTime, ts, ts');
    lemma_Mov32Helper2(ins, fixedTime, ts, ts');
}

method checkIfMov64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Mov64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcMov64;
    var dst := ins.dstMov64;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint64(src, ts);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        fixedTime := fixedTime && !(srcTaint.Secret? && dst.taint.Public?);
        ts' := ts;
    } else {
        ts' := setTaint64(Operand(dst), ts, srcTaint);
    }

    if fixedTime == false {
        return;
    }

    lemma_Mov64Helper1(ins, fixedTime, ts, ts');
    lemma_Mov64Helper2(ins, fixedTime, ts, ts');
}

method checkIfNot32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Not32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var dst := ins.dstNot;
    fixedTime := operandDoesNotUseSecrets(dst, ts);
    var taint := operandTaint(dst, ts);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else {
        ts' := ts.(flagsTaint := Secret);
    }

    lemma_Not32Helper1(ins, fixedTime, ts, ts');
    lemma_Not32Helper2(ins, fixedTime, ts, ts');
}

method checkIfRandConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Rand?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var dst := ins.xRand;
    fixedTime := operandDoesNotUseSecrets(ins.xRand, ts);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && (dst.taint.Secret?);
    } else {
        ts' := setTaint(Operand(dst), ts, Secret);
        ts' := ts'.(flagsTaint := Secret);
    }

    forall state1, state2, state1', state2' |
        (evalIns(ins, state1, state1')
        && evalIns(ins, state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2))
    ensures fixedTime ==> constTimeInvariant(ts', state1', state2')
    {
    }

    forall
    ensures fixedTime ==> isConstantTime(Ins(ins), ts);
    {
    }

    forall
    ensures specTaintCheckIns(ins, ts, ts', fixedTime);
    {
    }
}

method checkIfAdd32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Add32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcAdd;
    var dst := ins.dstAdd;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint(src, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Add32Helper1(ins, fixedTime, ts, ts');
    lemma_Add32Helper2(ins, fixedTime, ts, ts');
}

method checkIfAdd64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Add64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcAdd64;
    var dst := ins.dstAdd64;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint64(src, ts);
    var dstTaint := operandTaint64(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Add64Helper1(ins, fixedTime, ts, ts');
    lemma_Add64Helper2(ins, fixedTime, ts, ts');
}

method checkIfAddLea64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.AddLea64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src1 := ins.src1AddLea64;
    var src2 := ins.src2AddLea64;
    var dst := ins.dstAddLea64;

    var ftSrc1 := operandDoesNotUseSecrets(src1, ts);
    var ftSrc2 := operandDoesNotUseSecrets(src2, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);

    fixedTime := ftSrc1 && ftSrc2 && ftDst;

    var src1Taint := operandTaint64(src1, ts);
    var src2Taint := operandTaint64(src2, ts);
    var dstTaint := operandTaint64(dst, ts);

    var srcTaint := mergeTaint(src1Taint, src2Taint);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_AddLea64Helper1(ins, fixedTime, ts, ts');
    lemma_AddLea64Helper2(ins, fixedTime, ts, ts');
}

method checkIfSub32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Sub32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcSub;
    var dst := ins.dstSub;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint(src, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Sub32Helper1(ins, fixedTime, ts, ts');
    lemma_Sub32Helper2(ins, fixedTime, ts, ts');
}

method checkIfSub64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Sub64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcSub64;
    var dst := ins.dstSub64;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint64(src, ts);
    var dstTaint := operandTaint64(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Sub64Helper1(ins, fixedTime, ts, ts');
    lemma_Sub64Helper2(ins, fixedTime, ts, ts');
}

method checkIfMul32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Mul32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcMul;
    fixedTime := operandDoesNotUseSecrets(src, ts);

    var eaxTaint := operandTaint(OReg(X86Eax), ts);
    var srcTaint := operandTaint(src, ts);
    var taint := mergeTaint(srcTaint, eaxTaint);

    ts' := setTaint(Operand(OReg(X86Eax)), ts, taint);
    ts' := setTaint(Operand(OReg(X86Edx)), ts', taint);
    ts' := ts'.(flagsTaint := Secret);

    lemma_Mul32Helper1(ins, fixedTime, ts, ts');
    lemma_Mul32Helper2(ins, fixedTime, ts, ts');
}

method checkIfMul64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Mul64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcMul64;
    fixedTime := operandDoesNotUseSecrets(src, ts);

    var eaxTaint := operandTaint64(OReg(X86Eax), ts);
    var srcTaint := operandTaint64(src, ts);
    var taint := mergeTaint(srcTaint, eaxTaint);

    ts' := setTaint64(Operand(OReg(X86Eax)), ts, taint);
    ts' := setTaint64(Operand(OReg(X86Edx)), ts', taint);
    ts' := ts'.(flagsTaint := Secret);

    lemma_Mul64Helper1(ins, fixedTime, ts, ts');
    lemma_Mul64Helper2(ins, fixedTime, ts, ts');
}

method checkIfIMul64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.IMul64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcIMul64;
    var dst := ins.dstIMul64;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint64(src, ts);
    var dstTaint := operandTaint64(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_IMul64Helper1(ins, fixedTime, ts, ts');
    lemma_IMul64Helper2(ins, fixedTime, ts, ts');
}

method checkIfAddCarryConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.AddCarry?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcAddCarry;
    var dst := ins.dstAddCarry;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint(src, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    var flagTaint := ts.flagsTaint;
    taint := mergeTaint(taint, flagTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_AddCarryHelper1(ins, fixedTime, ts, ts');
    lemma_AddCarryHelper2(ins, fixedTime, ts, ts');
}

method checkIfAddCarry64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.AddCarry64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcAddCarry64;
    var dst := ins.dstAddCarry64;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint64(src, ts);
    var dstTaint := operandTaint64(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    var flagTaint := ts.flagsTaint;
    taint := mergeTaint(taint, flagTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_AddCarry64Helper1(ins, fixedTime, ts, ts');
    lemma_AddCarry64Helper2(ins, fixedTime, ts, ts');
}

method checkIfXor32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Xor32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcXor;
    var dst := ins.dstXor;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint(src, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else if dst.OReg? && src.OReg? && src == dst {
        ts' := setTaint(Operand(dst), ts, Public);
        ts' := ts'.(flagsTaint := Secret);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Xor32Helper1(ins, fixedTime, ts, ts');
    lemma_Xor32Helper2(ins, fixedTime, ts, ts');
}

method checkIfXor64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Xor64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcXorq;
    var dst := ins.dstXorq;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint64(src, ts);
    var dstTaint := operandTaint64(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else if dst.OReg? && src.OReg? && src == dst {
        ts' := setTaint64(Operand(dst), ts, Public);
        ts' := ts'.(flagsTaint := Secret);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Xor64Helper1(ins, fixedTime, ts, ts');
    lemma_Xor64Helper2(ins, fixedTime, ts, ts');
}

method checkIfAnd32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.And32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcAnd;
    var dst := ins.dstAnd;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint(src, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_And32Helper1(ins, fixedTime, ts, ts');
    lemma_And32Helper2(ins, fixedTime, ts, ts');
}

method checkIfAnd64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.And64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcAnd64;
    var dst := ins.dstAnd64;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint64(src, ts);
    var dstTaint := operandTaint64(dst, ts);
    var taint := mergeTaint(srcTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_And64Helper1(ins, fixedTime, ts, ts');
    lemma_And64Helper2(ins, fixedTime, ts, ts');
}

method checkIfGetCfConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.GetCf?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var dst := ins.dstCf;

    fixedTime := operandDoesNotUseSecrets(dst, ts);
    var dstTaint := operandTaint(dst, ts);
    var flagsTaint := ts.flagsTaint;
    var taint := mergeTaint(flagsTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
        ts' := ts;
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
    }

    lemma_GetCfHelper1(ins, fixedTime, ts, ts');
    lemma_GetCfHelper2(ins, fixedTime, ts, ts');
}

method checkIfRol32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Rol32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var amt := ins.amountRolConst;
    var dst := ins.dstRolConst;

    var ftAmt := operandDoesNotUseSecrets(amt, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftAmt && ftDst;

    var amtTaint := operandTaint(amt, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(amtTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Rol32Helper1(ins, fixedTime, ts, ts');
    lemma_Rol32Helper2(ins, fixedTime, ts, ts');
}

method checkIfRor32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Ror32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var amt := ins.amountRorConst;
    var dst := ins.dstRorConst;

    var ftAmt := operandDoesNotUseSecrets(amt, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftAmt && ftDst;

    var amtTaint := operandTaint(amt, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(amtTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Ror32Helper1(ins, fixedTime, ts, ts');
    lemma_Ror32Helper2(ins, fixedTime, ts, ts');
}

method checkIfBSwap32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.BSwap32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    fixedTime := true;
    ts' := ts;

    forall state1, state2, state1', state2' |
        (evalIns(ins, state1, state1')
        && evalIns(ins, state2, state2')
        && state1.ok && state1'.ok
        && state2.ok && state2'.ok
        && constTimeInvariant(ts, state1, state2))
    ensures fixedTime ==> constTimeInvariant(ts', state1', state2')
    {
    }

    forall
    ensures fixedTime ==> isConstantTime(Ins(ins), ts);
    {
    }

    forall
    ensures specTaintCheckIns(ins, ts, ts', fixedTime);
    {
    }
}

method checkIfShl32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Shl32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var amt := ins.amountShlConst;
    var dst := ins.dstShlConst;

    var ftAmt := operandDoesNotUseSecrets(amt, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftAmt && ftDst;

    var amtTaint := operandTaint(amt, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(amtTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Shl32Helper1(ins, fixedTime, ts, ts');
    lemma_Shl32Helper2(ins, fixedTime, ts, ts');
}

method checkIfShl64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Shl64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var amt := ins.amountShlConst64;
    var dst := ins.dstShlConst64;

    var ftAmt := operandDoesNotUseSecrets(amt, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftAmt && ftDst;

    var amtTaint := operandTaint64(amt, ts);
    var dstTaint := operandTaint64(dst, ts);
    var taint := mergeTaint(amtTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Shl64Helper1(ins, fixedTime, ts, ts');
    lemma_Shl64Helper2(ins, fixedTime, ts, ts');
}

method checkIfShr32ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Shr32?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var amt := ins.amountShrConst;
    var dst := ins.dstShrConst;

    var ftAmt := operandDoesNotUseSecrets(amt, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftAmt && ftDst;

    var amtTaint := operandTaint(amt, ts);
    var dstTaint := operandTaint(dst, ts);
    var taint := mergeTaint(amtTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Shr32Helper1(ins, fixedTime, ts, ts');
    lemma_Shr32Helper2(ins, fixedTime, ts, ts');
}

method checkIfShr64ConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Shr64?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var amt := ins.amountShrConst64;
    var dst := ins.dstShrConst64;

    var ftAmt := operandDoesNotUseSecrets(amt, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftAmt && ftDst;

    var amtTaint := operandTaint64(amt, ts);
    var dstTaint := operandTaint64(dst, ts);
    var taint := mergeTaint(amtTaint, dstTaint);

    if dst.OConst? {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        ts' := ts.(flagsTaint := Secret);
        fixedTime := fixedTime && !(taint.Secret? && dst.taint.Public?);
    } else {
        ts' := setTaint64(Operand(dst), ts, taint);
        ts' := ts'.(flagsTaint := Secret);
    }

    lemma_Shr64Helper1(ins, fixedTime, ts, ts');
    lemma_Shr64Helper2(ins, fixedTime, ts, ts');
}

method checkIfMOVDQUConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.MOVDQU?;
    requires (ins.srcMovdqu.OReg? && ins.srcMovdqu.r.X86Xmm?) || (ins.dstMovdqu.OReg? && ins.dstMovdqu.r.X86Xmm?);
    requires !ins.srcMovdqu.OStack? && !ins.dstMovdqu.OStack?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcMovdqu;
    var dst := ins.dstMovdqu;

    var ftSrc := operandDoesNotUseSecrets(src, ts);
    var ftDst := operandDoesNotUseSecrets(dst, ts);
    fixedTime := ftSrc && ftDst;

    var srcTaint := operandTaint(src, ts);

    if dst.OConst? || dst.OStack? || src.OStack? || (src.OReg? && !src.r.X86Xmm?) || (dst.OReg? && !dst.r.X86Xmm?) {
        fixedTime := false;
        ts' := ts;
    } else if dst.OHeap? {
        fixedTime := fixedTime && !(srcTaint.Secret? && dst.taint.Public?);
        ts' := ts.(flagsTaint := Secret);
    } else {
        ts' := ts.(xmmTaint := ts.xmmTaint[dst.r.xmm := srcTaint], flagsTaint := Secret);
    }

    if fixedTime == false {
        return;
    }

    lemma_MOVDQUHelper1(ins, fixedTime, ts, ts');
    lemma_MOVDQUHelper2(ins, fixedTime, ts, ts');
}

method checkIfPxorConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    requires ins.Pxor?;
    requires ins.srcPXor.OReg? && ins.srcPXor.r.X86Xmm?;
    requires ins.dstPXor.OReg? && ins.dstPXor.r.X86Xmm?;
    ensures  specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures  fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures  fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    var src := ins.srcPXor;
    var dst := ins.dstPXor;

    fixedTime := true;

    if src == dst {
        ts' := ts.(xmmTaint := ts.xmmTaint[dst.r.xmm := Public],
                   flagsTaint := Secret);
    } else {
        var srcTaint := operandTaint(src, ts);
        var dstTaint := operandTaint(dst, ts);
        var mergedTaint := mergeTaint(srcTaint, dstTaint);

        ts' := ts.(xmmTaint := ts.xmmTaint[dst.r.xmm := mergedTaint],
                   flagsTaint := Secret);
    }
    lemma_PxorHelper1(ins, fixedTime, ts, ts');
    lemma_PxorHelper2(ins, fixedTime, ts, ts');
}

method checkIfInstructionConsumesFixedTime(ins:ins, ts:taintState)
    returns (fixedTime:bool, ts':taintState)
    //requires AddrDoesNotUseXmmRegsInIns(ins);
    requires ValidRegsInXmmIns(ins);

    ensures specTaintCheckIns(ins, ts, ts', fixedTime);
    ensures fixedTime ==> isConstantTime(Ins(ins), ts);
    ensures fixedTime ==> isLeakageFree(Ins(ins), ts, ts');
{
    match ins {
        case Rand(x)            => fixedTime, ts' := checkIfRandConsumesFixedTime(ins, ts);
        case Mov32(dst,src)     => fixedTime, ts' := checkIfMov32ConsumesFixedTime(ins, ts);
        case Mov64(dst,src)     => fixedTime, ts' := checkIfMov64ConsumesFixedTime(ins, ts);
        case Add32(dst, src)    => fixedTime, ts' := checkIfAdd32ConsumesFixedTime(ins, ts);
        case Add64(dst, src)    => fixedTime, ts' := checkIfAdd64ConsumesFixedTime(ins, ts);
        case AddLea64(dst, src1, src2) => fixedTime, ts' := checkIfAddLea64ConsumesFixedTime(ins, ts);
        case Sub32(dst, src)    => fixedTime, ts' := checkIfSub32ConsumesFixedTime(ins, ts);
        case Sub64(dst, src)    => fixedTime, ts' := checkIfSub64ConsumesFixedTime(ins, ts);
        case Mul32(src)         => fixedTime, ts' := checkIfMul32ConsumesFixedTime(ins, ts);
        case Mul64(src)         => fixedTime, ts' := checkIfMul64ConsumesFixedTime(ins, ts);
        case IMul64(dst, src)   => fixedTime, ts' := checkIfIMul64ConsumesFixedTime(ins, ts);
        case AddCarry(dst, src) => fixedTime, ts' := checkIfAddCarryConsumesFixedTime(ins, ts);
        case AddCarry64(dst, src) => fixedTime, ts' := checkIfAddCarry64ConsumesFixedTime(ins, ts);
        case Xor32(dst, src)    => fixedTime, ts' := checkIfXor32ConsumesFixedTime(ins, ts);
        case Xor64(dst, src)    => fixedTime, ts' := checkIfXor64ConsumesFixedTime(ins, ts);
        case And32(dst, src)    => fixedTime, ts' := checkIfAnd32ConsumesFixedTime(ins, ts);
        case And64(dst, src)    => fixedTime, ts' := checkIfAnd64ConsumesFixedTime(ins, ts);
        case Not32(dst)         => fixedTime, ts' := checkIfNot32ConsumesFixedTime(ins, ts);
        case GetCf(dst)         => fixedTime, ts' := checkIfGetCfConsumesFixedTime(ins, ts);
        case Rol32(dst, amount) => fixedTime, ts' := checkIfRol32ConsumesFixedTime(ins, ts);
        case Ror32(dst, amount) => fixedTime, ts' := checkIfRor32ConsumesFixedTime(ins, ts);
        case Shl32(dst, amount) => fixedTime, ts' := checkIfShl32ConsumesFixedTime(ins, ts);
        case Shl64(dst, amount) => fixedTime, ts' := checkIfShl64ConsumesFixedTime(ins, ts);
        case Shr32(dst, amount) => fixedTime, ts' := checkIfShr32ConsumesFixedTime(ins, ts);
        case Shr64(dst, amount) => fixedTime, ts' := checkIfShr64ConsumesFixedTime(ins, ts);
        case BSwap32(dst)       => fixedTime, ts' := checkIfBSwap32ConsumesFixedTime(ins, ts);
        case Pxor(dst, src)                     => fixedTime, ts' := checkIfPxorConsumesFixedTime(ins, ts);
        case MOVDQU(dst, src)                   => fixedTime, ts' := checkIfMOVDQUConsumesFixedTime(ins, ts);
    }
}

method { :timeLimitMultiplier 4 } checkIfBlockConsumesFixedTime(block:codes, ts:taintState)
    returns (fixedTime:bool, ts':taintState)

    //requires ValidOperandsInBlock(block);
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
    var regTaint := combineTaints<x86reg>(ts1.regTaint, ts2.regTaint);
    var stackTaint := combineTaints<int>(ts1.stackTaint, ts2.stackTaint);
    var xmmTaint := combineTaints<int>(ts1.xmmTaint, ts2.xmmTaint);
    var flagTaint := mergeTaint(ts1.flagsTaint, ts2.flagsTaint);

    ts' := TaintState(stackTaint, regTaint, xmmTaint, flagTaint);
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
    requires specOperandTaint64(pred.o1, ts).Public?;
    requires specOperandTaint64(pred.o2, ts).Public?;
    requires specOperandDoesNotUseSecrets(pred.o1, ts);
    requires specOperandDoesNotUseSecrets(pred.o2, ts);
    requires constTimeInvariant(ts, state1, state2);
    requires evalWhile(pred, body, n1, state1, state1');
    requires evalWhile(pred, body, n2, state2, state2');
    requires forall pre_guard_state1:state, pre_guard_state2:state, loop_start1:state, loop_start2:state, loop_end1:state, loop_end2:state
                    {:trigger evalCode(body, loop_start1, loop_end1), evalCode(body, loop_start2, loop_end2), branchRelation(pre_guard_state1, loop_start1, true), branchRelation(pre_guard_state2, loop_start2, true), constTimeInvariant(ts, loop_end1, loop_end2)}
                    ::
                    pre_guard_state1.ok
                 && pre_guard_state2.ok
                 && loop_end1.ok
                 && loop_end2.ok
                 && ValidSourceOperand(pre_guard_state1, 64, pred.o1)
                 && ValidSourceOperand(pre_guard_state1, 64, pred.o2)
                 && ValidSourceOperand(pre_guard_state2, 64, pred.o1)
                 && ValidSourceOperand(pre_guard_state2, 64, pred.o2)
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
    lemma_ValuesOfPublic64BitOperandAreSame(ts, state1, state2, pred.o1);
    lemma_ValuesOfPublic64BitOperandAreSame(ts, state1, state2, pred.o2);
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
    var next_ts:taintState, combined_ts:taintState, o1:taint, o2:taint, predTaint:taint, o1Public:bool, o2Public:bool;

    while (!done)
        invariant taintStateModInvariant(ts, ts');
        invariant taintStateSubset(ts, ts');
        invariant done ==> specOperandTaint64(pred.o1, ts').Public?;
        invariant done ==> specOperandTaint64(pred.o2, ts').Public?;
        invariant done ==> specOperandDoesNotUseSecrets(pred.o1, ts');
        invariant done ==> specOperandDoesNotUseSecrets(pred.o2, ts');
        invariant done ==>
                   forall pre_guard_state1:state, pre_guard_state2:state, loop_start1:state, loop_start2:state, loop_end1:state, loop_end2:state ::
                        pre_guard_state1.ok
                     && pre_guard_state2.ok
                     && loop_end1.ok
                     && loop_end2.ok
                     && ValidSourceOperand(pre_guard_state1, 64, pred.o1)
                     && ValidSourceOperand(pre_guard_state1, 64, pred.o2)
                     && ValidSourceOperand(pre_guard_state2, 64, pred.o1)
                     && ValidSourceOperand(pre_guard_state2, 64, pred.o2)
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
        o1 := operandTaint64(pred.o1, ts');
        o2 := operandTaint64(pred.o2, ts');
        predTaint := mergeTaint(o1, o2);

        if predTaint.Secret? {
            fixedTime := false;
            return;
        }

        assert specOperandTaint64(pred.o1, ts').Public?;
        assert specOperandTaint64(pred.o2, ts').Public?;

        o1Public := operandDoesNotUseSecrets(pred.o1, ts');
        if o1Public == false {
            fixedTime := false;
            return;
        }

        o2Public := operandDoesNotUseSecrets(pred.o2, ts');
        if o2Public == false {
            fixedTime := false;
            return;
        }

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
                         && constTimeInvariant(ts', pre_guard_state1, pre_guard_state2)
                         && loop_end1.ok
                         && loop_end2.ok
                         && ValidSourceOperand(pre_guard_state1, 64, pred.o1)
                         && ValidSourceOperand(pre_guard_state1, 64, pred.o2)
                         && ValidSourceOperand(pre_guard_state2, 64, pred.o1)
                         && ValidSourceOperand(pre_guard_state2, 64, pred.o2)
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
            if (ValidRegsInXmmIns(ins)) {
                fixedTime, ts' := checkIfInstructionConsumesFixedTime(ins, ts);
                if fixedTime == true {
                    assert insPostconditions(ins, ts, ts', fixedTime);
                }
            } else {
                fixedTime := false;
                return;
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
            var o1 := operandTaint64(pred.o1, ts);
            var o2 := operandTaint64(pred.o2, ts);
            var predTaint := mergeTaint(o1, o2);

            ts' := ts;
            if (o1.Secret? || o2.Secret?)
            {
                fixedTime := false;
                return;
            }

            var o1Public := operandDoesNotUseSecrets(pred.o1, ts);
            if o1Public == false {
                fixedTime := false;
                return;
            }

            var o2Public := operandDoesNotUseSecrets(pred.o2, ts);
            if o2Public == false {
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

method {:timeLimitMultiplier 2} checkIfCodeisLeakageFree(code:code, ts:taintState, tsExpected:taintState) returns (b:bool)
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
