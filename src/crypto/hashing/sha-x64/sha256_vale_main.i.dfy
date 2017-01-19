include "../../../../obj/crypto/hashing/sha-x64/sha256.gen.dfy"
include "../../../arch/x64/print.s.dfy"
include "../../../lib/util/Io.s.dfy"

module x64_SHA256ValeMain {

import opened x64_sha256_vale
import opened x64_print_s
import opened Io_s

method {:main} Main(ghost env:HostEnvironment)
    requires env != null && allocated(env) && env.Valid();
    decreases *
{
    var argc := HostConstants.NumCommandLineArgs(env);
    if argc < 2 {
        print("Expected usage: ./[executable].exe [GCC|MASM]\n");
        return;
    }

    var asm_choice_name := HostConstants.GetCommandLineArg(1, env);
    var asm_choice;
    if asm_choice_name[..] == "GCC" {
        asm_choice := GCC;
    } else if asm_choice_name[..] == "MASM" {
        asm_choice := MASM;
    } else {
        print("Please choose a correct assembler option: GCC or MASM\n");
        return;
    }

//    var ts_SHA256_Compute64StepsH:taintState := TaintState(map[0 := Public, 1 := Public], map[], map[], Secret);
//    var ts_SHA256_ComputeInitialWs := TaintState(map[0 := Public, 1 := Public, 2 := Public], map[], map[], Secret);

    printHeader(asm_choice);
    printProc("sha256_main_i_SHA256_Compute64Steps", va_code_SHA256_Compute64StepsH(Secret, Secret), 0, 112, asm_choice);
    printProc("sha256_main_i_SHA256_ComputeInitialWs", va_code_SHA256_ComputeInitialWs(Secret), 0, 0, asm_choice);
    printFooter(asm_choice);
}

}
