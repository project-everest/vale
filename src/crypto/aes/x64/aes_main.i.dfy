include "../../../../obj/crypto/aes/x64/aes.gen.dfy"
include "../../../arch/x64/print.s.dfy"
include "../../../lib/util/Io.s.dfy"

module AESMain {

import opened aes_vale
import opened x64_print_s
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

    printHeader(asm_choice);
    var win := (platform_choice == Win);

    printProcPlatform("KeyExpansionStdcall",
        va_code_KeyExpansionStdcall(Secret, win),
        0, 0, asm_choice, platform_choice);
    printProcPlatform("KeyExpansionAndInversionStdcall",
        va_code_KeyExpansionAndInversionStdcall(Secret, win),
        0, 0, asm_choice, platform_choice);

    printProcPlatform("AES128EncryptOneBlockStdcall",
        va_code_AES128EncryptOneBlockStdcall(win),
        0, 0, asm_choice, platform_choice);

    printFooter(asm_choice);
}

}
