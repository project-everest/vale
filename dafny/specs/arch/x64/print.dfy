// Trusted printer for producing MASM code

include "printMasm.dfy"
include "printGcc.dfy"

module x64_print {

import opened x64_def

import Masm = x64_printMasm
import Gcc = x64_printGcc

datatype AsmTarget = MASM | GCC
datatype PlatformTarget = Win | Linux | MacOS

method printHeader(asm:AsmTarget)
{
    match asm
        case MASM => Masm.printHeader();
        case GCC  => Gcc.printHeader();
}

method printProc(proc_name:seq<char>, code:code, n:int, ret_count:uint32, asm:AsmTarget)
{
    match asm
        case MASM => Masm.printProc(proc_name, code, n, ret_count);
        case GCC  => Gcc.printProc(proc_name, code, n, ret_count);
}

method printProcPlatform(proc_name:seq<char>, code:code, n:int, ret_count:uint32, asm:AsmTarget, platform:PlatformTarget)
{
    printProc(match platform case Win => proc_name case Linux => proc_name case MacOS => "_" + proc_name,
        code, n, ret_count, asm);
}

method printFooter(asm:AsmTarget)
{
    match asm
        case MASM => Masm.printFooter();
        case GCC  => Gcc.printFooter();
}


}
