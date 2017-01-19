// Trusted printer for producing assembly code

include "printMasm.s.dfy"
include "printGcc.s.dfy"

module x86_print_s {
import opened x86_def_s
import opened x86_const_time_i

import Masm = x86_printMasm_s 
import Gcc = x86_printGcc_s

datatype AsmTarget = MASM | GCC
datatype PlatformTarget = Win | Linux | MacOS

function method procName(proc_name:seq<char>, suffix:seq<char>, asm:AsmTarget, platform:PlatformTarget):seq<char>
{
    match platform
        case Win => "_" + proc_name + (match asm case MASM => suffix case GCC => "")
        case Linux => proc_name
        case MacOS => "_" + proc_name
}

method printHeader(asm:AsmTarget)
{
    match asm
        case MASM => Masm.printHeader();
        case GCC  => Gcc.printHeader();
}

method printProc(proc_name:seq<char>, code:code, n:int, ret_count:uint32, suffix:seq<char>, asm:AsmTarget, platform:PlatformTarget)
{
    match asm
        case MASM => Masm.printProc(procName(proc_name, suffix, asm, platform), code, n, ret_count);
        case GCC  => Gcc.printProc(procName(proc_name, suffix, asm, platform), code, n, ret_count);
}

method printFooter(asm:AsmTarget)
{
    match asm
        case MASM => Masm.printFooter();
        case GCC  => Gcc.printFooter();
}

// runs constant time analysis
method checkConstantTimeAndPrintProc(proc_name:seq<char>, code:code, n:int, ret_count:uint32, ts:taintState, suffix:seq<char>, asm:AsmTarget, platform:PlatformTarget)
    decreases * 
{
    match asm
        case MASM => Masm.checkConstantTimeAndPrintProc(procName(proc_name, suffix, asm, platform), code, n, ret_count, ts);
        case GCC  => Gcc.checkConstantTimeAndPrintProc(procName(proc_name, suffix, asm, platform), code, n, ret_count, ts);
}

// runs both leakage analysis and constant time analysis
method checkConstantTimeAndLeakageBeforePrintProc(proc_name:seq<char>, code:code, n:int, ret_count:uint32, ts:taintState, tsExpected:taintState, suffix:seq<char>, asm:AsmTarget, platform:PlatformTarget)
    decreases * 
{
    match asm
        case MASM => Masm.checkConstantTimeAndLeakageBeforePrintProc(procName(proc_name, suffix, asm, platform), code, n, ret_count, ts, tsExpected);
        case GCC  => Gcc.checkConstantTimeAndLeakageBeforePrintProc(procName(proc_name, suffix, asm, platform), code, n, ret_count, ts, tsExpected);
}

}
