// Trusted printer for producing MASM code

include "def.s.dfy"
include "leakage.i.dfy"

module x86_printMasm_s {

import opened x86_def_s
import opened x86_const_time_i

method printReg(r:x86reg)
{
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

method printMAddr(addr:maddr, ptr_type:string)
{
    print(ptr_type);
    match addr
        case MConst(c) => print(" ptr "); print(c);
        case MReg(r, offset) => print(" ptr [");
                                printReg(r);
                                print(" + ");
                                print(offset);
                                print("]");
        case MIndex(base, scale, index, offset) =>
            print(" ptr [");
            printReg(base);
            print(" + ");
            print(scale);
            print(" * ");
            printReg(index);
            print(" + ");
            print(offset);
            print("]");
}

method printGenericOprnd(o:operand, ptr_type:string)
{
    match o
        case OConst(n) =>
            if 0 <= n as int < 0x1_0000_0000 { print(n); }
            else { print(" !!!NOT IMPLEMENTED!!!"); }
        case OReg(r) => printReg(r);
        case OStack(i) => print(ptr_type); print(" ptr [esp + "); print(4+4*i); print("]");
        case OHeap(addr, taint) => printMAddr(addr, ptr_type);
}
method printOprnd(o:operand)
{
    printGenericOprnd(o, "dword");
}

method printXmmOprnd(o:operand)
{
    printGenericOprnd(o, "xmmword");
}

method printSmallOprnd(o:operand)
{
    if o.OConst? { 
      if 0 <= o.n as int < 32 {
        print(o.n); 
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

method printIns(ins:ins)
{
    match ins
        case Rand(o) => print("  rdrand "); printOprnd(o); print("\n");
        case Mov32(dst, src) => print ("  mov "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
        case Add32(dst, src) => print ("  add "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
        case Sub32(dst, src) => print ("  sub "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
        case Mul32(src)      => print ("  mul "); printOprnd(src); print("\n");
        case AddCarry(dst, src) => print ("  add "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
        case BSwap32(dst)    => print ("  bswap "); printOprnd(dst); print("\n");
        case Xor32(dst, src) => print ("  xor "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
        case And32(dst, src) => print ("  and "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
        case Not32(dst)      => print ("  not "); printOprnd(dst); print("\n");
        case GetCf(dst)      => print ("  setc "); printSmallOprnd(dst); print("\n");

        case Rol32(dst, amount)  =>
            print ("  rol ");
            printOprnd(dst);
            print ", ";
            if amount.OConst? {
                printOprnd(amount);
            }
            else {
                printSmallOprnd(amount);
            }
            print("\n");

        case Ror32(dst, amount) =>
            print ("  ror ");
            printOprnd(dst);
            print ", ";
            if amount.OConst? {
                printOprnd(amount);
            }
            else {
                printSmallOprnd(amount);
            }
            print("\n");

        case Shl32(dst, amount)  =>
            print ("  shl ");
            printOprnd(dst);
            print ", ";
            if amount.OConst? {
                printOprnd(amount);
            }
            else {
                printSmallOprnd(amount);
            }
            print("\n");

        case Shr32(dst, amount) =>
            print ("  shr ");
            printOprnd(dst);
            print ", ";
            if amount.OConst? {
                printSmallOprnd(amount);
            }
            else {
                print "cl";
            }
            print("\n");

        case Pxor(dst, src) => print ("  pxor "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
        case MOVDQU(dst, src) => print ("  movdqu "); printXmmOprnd(dst); print(", "); printXmmOprnd(src); print("\n");
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
            print("  cmp "); printOprnd(ifb.o1); print(", "); printOprnd(ifb.o2); print("\n");
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
            print("ALIGN 16\nL"); print(n1); print(":\n");
            n' := printCode(loop, n + 2);
            print("ALIGN 16\nL"); print(n2); print(":\n");
            print("  cmp "); printOprnd(b.o1); print(", "); printOprnd(b.o2); print("\n");
            printJcc(b.cmp); print("L"); print(n1); print("\n");
        }
}

method printHeader()
{
  print(".686p\n");
  print(".model flat\n");
  print(".code\n");
}

method printProc(proc_name:seq<char>, code:code, n:int, ret_count:uint32)
{
  //print("@valeMain@4 proc\n");
  print("ALIGN 16\n");
  print(proc_name);
  print(" proc\n");

  var _ := printCode(code, n);

  print("  ret ");
  print(ret_count);
  print("\n");
  print(proc_name);
  print(" endp\n");
}

method printFooter()
{
    print("end\n");
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
