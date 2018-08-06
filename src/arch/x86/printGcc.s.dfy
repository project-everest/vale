// Trusted printer for producing AT&T/UNIX assembly code

include "def.s.dfy"
include "leakage.i.dfy"

module x86_printGcc_s {

import opened x86_def_s
import opened x86_const_time_i

method printReg(r:x86reg)
{
    print("%");
    match r
        case X86Eax => print("eax");
        case X86Ebx => print("ebx");
        case X86Ecx => print("ecx");
        case X86Edx => print("edx");
        case X86Esi => print("esi");
        case X86Edi => print("edi");
        case X86Ebp => print("ebp");
        case X86Xmm(xmm) => print("xmm"); print(xmm);
}

method printSmallReg(r:x86reg)
{
    print("%");
    match r
        case X86Eax => print("al");
        case X86Ebx => print("bl");
        case X86Ecx => print("cl");
        case X86Edx => print("dl");
        case X86Esi => print(" !!!INVALID small operand!!!  Expected al, bl, cl, or dl."); 
        case X86Edi => print(" !!!INVALID small operand!!!  Expected al, bl, cl, or dl."); 
        case X86Ebp => print(" !!!INVALID small operand!!!  Expected al, bl, cl, or dl."); 
        case X86Xmm(_) => print(" !!!INVALID small operand!!!  Expected al, bl, cl, or dl."); 
}

method printMAddr(addr:maddr)
{
    match addr
        case MConst(c) => print("$"); print(c);
        case MReg(r, offset) => print(offset);
                                print("(");
                                printReg(r);
                                print(")");
        case MIndex(base, scale, index, offset) =>
            print(offset);
            print(" (");
            printReg(base);
            print(", ");
            print(scale);
            print(", ");
            printReg(index);
            print(")");
}

method printOprnd(o:operand)
{
    match o
        case OConst(n) =>
            if 0 <= n as int < 0x1_0000_0000 { print("$"); print(n); }
            else { print(" !!!NOT IMPLEMENTED!!!"); }
        case OReg(r) => printReg(r);
        case OStack(i) => print(4+4*i); print("(%esp)"); 
        case OHeap(addr, taint) => printMAddr(addr);
}

method printSmallOprnd(o:operand)
{
    if o.OConst? { 
      if 0 <= o.n as int < 32 {
        print("$"); print(o.n); 
      } else { 
        print(o.n, " is too large for a small operand"); 
      }
    } else if o.OReg? { printSmallReg(o.r); }
    else { print(" !!!INVALID small operand!!!  Expected al, bl, cl, or dl."); }
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

method printJcc(c:ocmp)
{
    match c
        case OEq => print("  je ");
        case ONe => print("  jne ");
        case OLe => print("  jbe ");
        case OGe => print("  jae ");
        case OLt => print("  jb ");
        case OGt => print("  ja ");
}

method printName1(name:string, o:operand)
{
    print(name);
    if o.OStack? || o.OHeap? {
        print("l");
    }
    print(" ");
}

method printName2(name:string, o1:operand, o2:operand)
{
    print(name);
    if o1.OStack? || o1.OHeap? 
    || o2.OStack? || o2.OHeap? {
        print("l");
    }
    print(" ");
}

method printIns(ins:ins)
{
    match ins
        case Rand(o)            => printName1("  rdrand", o);     printOprnd(o); print("\n");
        case Mov32(dst, src)    => printName2("  mov", dst, src); printOprnd(src); print(", "); printOprnd(dst); print("\n");
        case Add32(dst, src)    => printName2("  add", dst, src); printOprnd(src); print(", "); printOprnd(dst); print("\n");
        case Sub32(dst, src)    => printName2("  sub", dst, src); printOprnd(src); print(", "); printOprnd(dst); print("\n");
        case Mul32(src)         => printName1("  mul", src);      printOprnd(src); print("\n");
        case AddCarry(dst, src) => printName2("  add", dst, src); printOprnd(src); print(", "); printOprnd(dst); print("\n");
        case BSwap32(dst)       => printName1("  bswap", dst);    printOprnd(dst); print("\n");
        case Xor32(dst, src)    => printName2("  xor", dst, src); printOprnd(src); print(", "); printOprnd(dst); print("\n");
        case And32(dst, src)    => printName2("  and", dst, src); printOprnd(src); print(", "); printOprnd(dst); print("\n");
        case Not32(dst)         => printName1("  not", dst);      printOprnd(dst); print("\n");
        case GetCf(dst)         => printName1("  setc", dst);     printSmallOprnd(dst); print("\n");

        case Rol32(dst, amount)  =>
            printName1("  rol", dst);
            if amount.OConst? {
                printOprnd(amount);
            }
            else {
                printSmallOprnd(amount);
            }
            print ", ";
            printOprnd(dst);
            print("\n");

        case Ror32(dst, amount) =>
            printName1("  ror", dst);
            if amount.OConst? {
                printOprnd(amount);
            }
            else {
                printSmallOprnd(amount);
            }
            print ", ";
            printOprnd(dst);
            print("\n");

        case Shl32(dst, amount)  =>
            printName1("  shl", dst);
            if amount.OConst? {
                printOprnd(amount);
            }
            else {
                printSmallOprnd(amount);
            }
            print ", ";
            printOprnd(dst);
            print("\n");

        case Shr32(dst, amount) =>
            printName1("  shr", dst);
            if amount.OConst? {
                printSmallOprnd(amount);
            }
            else {
                print "cl";
            }
            print ", ";
            printOprnd(dst);
            print("\n");

        case Pxor(dst, src)                => print ("  pxor ");    printOprnd(src); print(", "); printOprnd(dst); print("\n");
        case MOVDQU(dst, src)              => print ("  movdqu ");  printOprnd(src); print(", "); printOprnd(dst); print("\n");
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

method printCode(c:code, n:int) returns(n':int)
{
    match c
        case Ins(ins) => printIns(ins); n' := n;
        case Block(block) => n' := printBlock(block, n);
        case IfElse(ifb, ift, iff) =>
        {
            var n1 := n;
            var n2 := n + 1;
            print("  cmp "); printOprnd(ifb.o2); print(", "); printOprnd(ifb.o1); print("\n");
            printJcc(cmpNot(ifb.cmp)); print("L"); print(n1); print("\n");
            n' := printCode(ift, n + 2);
            print("  jmp L"); print(n2); print("\n");
            print("L"); print(n1); print(":\n");
            n' := printCode(iff, n');
            print("L"); print(n2); print(":\n");
        }
        case While(b, loop) =>
        {
            var n1 := n;
            var n2 := n + 1;
            print("  jmp L"); print(n2); print("\n");
            print(".align 16\nL"); print(n1); print(":\n");
            n' := printCode(loop, n + 2);
            print(".align 16\nL"); print(n2); print(":\n");
            print("  cmp "); printOprnd(b.o2); print(", "); printOprnd(b.o1); print("\n");
            printJcc(b.cmp); print("L"); print(n1); print("\n");
        }
}

method printHeader()
{
  print(".text\n");
}

method printProc(proc_name:seq<char>, code:code, n:int, ret_count:uint32)
{
  //print("@valeMain@4 proc\n");
  print(".global "); print(proc_name); print("\n");
  print(proc_name); print(":\n"); 

  var _ := printCode(code, n);

//  print("  sub $");
//  print(ret_count);
//  print(", %esp\n");
  print("  ret ");
  print("\n\n");
}

method printFooter()
{
    print("\n");
}

// runs constant time analysis
method checkConstantTimeAndPrintProc(proc_name:seq<char>, code:code, n:int, ret_count:uint32, ts:taintState)
    decreases * 
{
    var constTime, ts' := checkIfCodeConsumesFixedTime(code, ts);

    // print code only if the code is constant time and leakage free according to the checker
    if (constTime == false) {
        print(proc_name + ": Constant time check failed\n");
    } else {
        printProc(proc_name, code, n, ret_count);
    }
}

// runs both leakage analysis and constant time analysis
method checkConstantTimeAndLeakageBeforePrintProc(proc_name:seq<char>, code:code, n:int, ret_count:uint32, ts:taintState, tsExpected:taintState)
    decreases * 
{
    var b := checkIfCodeisLeakageFree(code, ts, tsExpected);

    // print code only if the code is constant time and leakage free according to the checker
    if (b == false) {
        print(proc_name + ": Constant time check or leakage analysis failed\n");
    } else {
        printProc(proc_name, code, n, ret_count);
    }
}

}
