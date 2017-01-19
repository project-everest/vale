include "def.s.dfy"
include "leakage.i.dfy"

module ARM_print_s {
import opened ARM_def_s
import opened ARM_leakage_i

function method user_continue_label(): string
{
    "usermode_return_continue"
}

method nl()
{
    print("\n");
}

function method cmpNot(c:ocmp):ocmp
{
    match c
        case OEq => ONe
        case ONe => OEq
        case OLe => OGt
        case OGe => OLt
        case OLt => OGe
        case OGt => OLe
}

method printBcc(c:ocmp)
{
    match c
        case OEq => print("  BEQ ");
        case ONe => print("  BNE ");
        case OLe => print("  BLE ");
        case OGe => print("  BGE ");
        case OLt => print("  BLT ");
        case OGt => print("  BGT ");
}

method printReg(r:ARMReg)
{
    match r
        case R0 => print("r0");
        case R1 => print("r1");
        case R2 => print("r2");
        case R3 => print("r3");
        case R4 => print("r4");
        case R5 => print("r5");
        case R6 => print("r6");
        case R7 => print("r7");
        case R8 => print("r8");
        case R9 => print("r9");
        case R10 => print("r10");
        case R11 => print("r11");
        case R12 => print("r12");
        case SP => print("sp_usr");
        case LR => print("lr_usr");
}

method printShift(s:Shift)
{
    match s
        case LSLShift(amount) => if amount == 0 { 
                                     print("Shifts cannot be 0!"); 
                                 } else { 
                                     print("lsl#"); 
                                     print(amount); 
                                 }
        case LSRShift(amount) => if amount == 0 { 
                                     print("Shifts cannot be 0!"); 
                                 } else { 
                                     print("lsr#"); 
                                     print(amount); 
                                 }
        case RORShift(amount) => if amount == 0 { 
                                     print("Shifts cannot be 0!"); 
                                 } else { 
                                     print("ror#"); 
                                     print(amount); 
                                 }
}

method printOperand(o:operand)
{
    match o
        case OConst(n) => print("#"); print(n);
        case OReg(r) => { printReg(r); }
        case OShift(r, s) => { printReg(r); print(","); printShift(s); }
        case OSP => print("sp");
        case OLR => print("lr");
        case OSymbol(sym) => print "="; print(sym);
}

method printIns3Op(instr:string, dest:operand, src1:operand, src2:operand)
{
    print("  ");
    print(instr);
    print(" ");
    printOperand(dest);
    print(", ");
    printOperand(src1);
    print(", ");
    printOperand(src2);
    nl();
}

method printIns2Op(instr:string, dest:operand, src:operand)
{
    print("  ");
    print(instr);
    print(" ");
    printOperand(dest);
    print(", ");
    printOperand(src);
    nl();
}

method printIns1Op(instr:string, op:operand)
{
    print("  ");
    print(instr);
    print(" ");
    printOperand(op);
    nl();
}

method printInsFixed(instr:string, ops:string)
{
    print("  ");
    print(instr);
    print(" ");
    print(ops);
    nl();
}

method printMcrMsr(instr:string,op:operand)
{
    print("  ");
    print(instr);
    print(" p15, 0, ");
    printOperand(op);
    print(", c1, c1, 0");
}

method printInsLdStr(instr:string, dest:operand, base:operand, offset:operand)
{
    print("  ");
    print(instr);
    print(" ");
    printOperand(dest);
    print(", [");
    printOperand(base);
    if (offset != OConst(0)) {
        print(", ");
        printOperand(offset);
    }
    print("]");
    nl();
}

method printIns(ins:ins)
{
    match ins
    {
        case ADD(dest, src1, src2) => printIns3Op("ADD", dest, src1, src2);
        case SUB(dest, src1, src2) => printIns3Op("SUB", dest, src1, src2);
        case AND(dest, src1, src2) => printIns3Op("AND", dest, src1, src2);
        case EOR(dest, src1, src2) => printIns3Op("EOR", dest, src1, src2);
        case REV(dest, src) => printIns2Op("REV", dest, src);
        case LDR(rd, base, ofs, taint) => printInsLdStr("LDR", rd, base, ofs);
        case LDR_global(rd, global, base, ofs) => printInsLdStr("LDR", rd, base, ofs);
        case LDR_reloc(rd, sym) => printIns2Op("LDR", rd, sym);
        case STR(rd, base, ofs, taint) => printInsLdStr("STR", rd, base, ofs);
        case STR_global(rd, global, base, ofs) => printInsLdStr("STR", rd, base, ofs);
        case MOV(dst, src) => printIns2Op("MOV", dst, src);
    }
}

method printBlock(b:codes, n:int) returns(n':int)
{
    n' := n;
    var i := b;
    while (i.va_CCons?)
        decreases i
    {
        n' := printCode(i.hd, n');
        i := i.tl;
    }
}

method printLabel(n:int)
{
    print("L");
    print(n);
}

method printCode(c:code, n:int) returns(n':int)
{
    match c
    {
        case Ins(ins) => printIns(ins); n':= n;
        case Block(block) => n' := printBlock(block, n);
        case IfElse(ifb, ift, iff) => {
            var false_branch := n;
            var end_of_block := n + 1;
            // Do comparison
            printIns2Op("CMP", ifb.o1, ifb.o2);
            // Branch to false branch if cond is false
            printBcc(cmpNot(ifb.cmp)); printLabel(false_branch); nl();
            // True branch
            n' := printCode(ift, n + 2);
            print("  B "); printLabel(end_of_block); nl();
            printLabel(false_branch); print(":"); nl();
            // False branch
            n' := printCode(iff, n');
            // Label end of block
            printLabel(end_of_block); print(":"); nl();
        } 
        case While(b, loop) =>
        {
          var n1 := n;
          var n2 := n + 1;
          print("  B "); printLabel(n2); nl();
          print(".LTORG"); nl();
          printLabel(n1); print(":"); nl();
          n' := printCode(loop, n + 2);
          printLabel(n2); print(":"); nl();
          printIns2Op("CMP", b.o1, b.o2);
          printBcc(b.cmp); printLabel(n1); nl();
        }
    }
}

method printFunction(symname:string, c:code, n:int) returns(n':int)
{
    nl();
    print(".global "); print(symname); nl();
    print(symname); print(":"); nl();
    n' := printCode(c, n);
}

method printHeader()
{
    print(".arm"); nl();
    print(".section .text"); nl();
}

method printKSHA256()
{
    print(".type g_k_sha256, %object"); nl();
    print(".align 5"); nl();
    print("g_k_sha256:"); nl();
    print(".word 0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5"); nl();
    print(".word 0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5"); nl();
    print(".word 0xd807aa98,0x12835b01,0x243185be,0x550c7dc3"); nl();
    print(".word 0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174"); nl();
    print(".word 0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc"); nl();
    print(".word 0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da"); nl();
    print(".word 0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7"); nl();
    print(".word 0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967"); nl();
    print(".word 0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13"); nl();
    print(".word 0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85"); nl();
    print(".word 0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3"); nl();
    print(".word 0xd192e819,0xd6990624,0xf40e3585,0x106aa070"); nl();
    print(".word 0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5"); nl();
    print(".word 0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3"); nl();
    print(".word 0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208"); nl();
    print(".word 0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2"); nl();
    print(".size g_k_sha256,.-g_k_sha256"); nl();
    print(".word 0   @ terminator"); nl();
}


method printGlobal(symname: string, bytes: int)
{
    if symname == "g_k_sha256" {
        printKSHA256();
    } else {
        print(".lcomm ");
        print(symname);
        print(", ");
        print(bytes);
        nl();
    }
}

function method SymbolName(o:operand): string
    requires o.OSymbol?
{
    match o case OSymbol(name) => name
}

method printBss(gdecls: globaldecls)
    requires ValidGlobalDecls(gdecls)
{
    nl();
    print(".section .bss"); nl();
    print(".align 2"); nl(); // 4-byte alignment
    var syms := (set k | k in gdecls :: k);
    while (|syms| > 0)
        invariant forall s :: s in syms ==> s in gdecls;
    {
        var s :| s in syms;
        printGlobal(SymbolName(s), gdecls[s]);
        syms := syms - {s};
    }
}

method printFooter()
{
}

// runs constant time analysis
method checkConstantTime(proc_name:seq<char>, code:code, ts:taintState) returns (b:bool)
    decreases * 
{
    var constTime, ts' := checkIfCodeConsumesFixedTime(code, ts);
    b := constTime;

    // print code only if the code is constant time and leakage free according to the checker
    if (constTime == false) {
        print(proc_name + ": Constant time check failed\n");
    } else {
        //printProc(proc_name, code, n, ret_count);
        //var n' := printCode(code, n);
    }
}

// runs both leakage analysis and constant time analysis
method checkLeakage(proc_name:seq<char>, code:code, ts:taintState, tsExpected:taintState) returns (b:bool)
    decreases * 
{
    b := checkIfCodeisLeakageFree(code, ts, tsExpected);

    // print code only if the code is constant time and leakage free according to the checker
    if (b == false) {
        print(proc_name + ": Leakage analysis failed\n");
    } else {
        // printProc(proc_name, code, n, ret_count);
        //var n' := printCode(code, n);
    }
}
}
