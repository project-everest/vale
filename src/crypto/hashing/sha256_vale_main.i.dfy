include "../../../obj/crypto/hashing/sha256.gen.dfy"
include "../../arch/x86/print.s.dfy"
include "../../lib/util/Io.s.dfy"

module SHA256ValeMain {

import opened sha256_vale
import opened x86_print_s
import opened Io_s

method {:main} Main(ghost env:HostEnvironment)
    requires env != null && allocated(env) && env.Valid();
    decreases *
{
    var argc := HostConstants.NumCommandLineArgs(env);
    if argc < 3 {
        print("Expected usage: ./[executable].exe [GCC|MASM] [Win|Linux|MacOS]\n");
        return;
    }

    var asm_choice_name := HostConstants.GetCommandLineArg(1, env);
    var platform_choice_name := HostConstants.GetCommandLineArg(2, env);
    var asm_choice;
    var platform_choice;

    if platform_choice_name[..] == "Win" {
        platform_choice := Win;
    } else if platform_choice_name[..] == "Linux" {
        platform_choice := Linux;
    } else if platform_choice_name[..] == "MacOS" {
        platform_choice := MacOS;
    } else {
        print("Please choose a correct assembler option: Win or Linux or MacOS\n");
        return;
    }

    if asm_choice_name[..] == "GCC" {
        asm_choice := GCC;
    } else if asm_choice_name[..] == "MASM" {
        asm_choice := MASM;
    } else {
        print("Please choose a correct assembler option: GCC or MASM\n");
        return;
    }

    var ts_SHA256_Compute64StepsH:taintState := TaintState(map[0 := Public, 1 := Public], map[], map[], Secret);
    var ts_SHA256_ComputeInitialWs := TaintState(map[0 := Public, 1 := Public, 2 := Public], map[], map[], Secret);

    printHeader(asm_choice);
    checkConstantTimeAndPrintProc("sha256_main_i_SHA256_Compute64Steps", va_code_SHA256_Compute64StepsH(Secret, Secret), 0, 76, ts_SHA256_Compute64StepsH, "@76", asm_choice, platform_choice);
    checkConstantTimeAndPrintProc("sha256_main_i_SHA256_ComputeInitialWs", va_code_SHA256_ComputeInitialWs(Secret), 0, 28, ts_SHA256_ComputeInitialWs, "@28", asm_choice, platform_choice);
    // printProc("_sha256_main_i_SHA256_Compute64Steps@76", va_code_SHA256_Compute64StepsH(Public, Public), 0, 76);
    // printProc("_sha256_main_i_SHA256_ComputeInitialWs@28", va_code_SHA256_ComputeInitialWs(Public), 0, 28);
    printFooter(asm_choice);
}

}
