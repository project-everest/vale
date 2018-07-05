module X64.Machine_s

irreducible let va_qattr = ()
unfold let pow2_32 = Words_s.pow2_32
unfold let pow2_64 = Words_s.pow2_64
unfold let pow2_128 = Words_s.pow2_128

unfold let nat64 = Types_s.nat64
let int_to_nat64 (i:int) : n:nat64{0 <= i && i < pow2_64 ==> i == n} =
  Words_s.int_to_natN pow2_64 i
unfold let nat128 = Words_s.nat128
unfold let quad32 = Types_s.quad32

type reg = i:int{ 0 <= i /\ i < 16 }
type xmm = i:int{ 0 <= i /\ i < 16 }
type imm8 = i:int{ 0 <= i /\ i < 256 }

[@va_qattr] unfold let rax =  0
[@va_qattr] unfold let rbx =  1
[@va_qattr] unfold let rcx =  2
[@va_qattr] unfold let rdx =  3
[@va_qattr] unfold let rsi =  4
[@va_qattr] unfold let rdi =  5
[@va_qattr] unfold let rbp =  6
[@va_qattr] unfold let rsp =  7
[@va_qattr] unfold let r8  =  8
[@va_qattr] unfold let r9  =  9
[@va_qattr] unfold let r10 = 10
[@va_qattr] unfold let r11 = 11
[@va_qattr] unfold let r12 = 12
[@va_qattr] unfold let r13 = 13
[@va_qattr] unfold let r14 = 14
[@va_qattr] unfold let r15 = 15

type maddr =
  | MConst: n:int -> maddr
  | MReg: r:reg -> offset:int -> maddr
  | MIndex: base:reg -> scale:int -> index:reg -> offset:int -> maddr

[@va_qattr]
type operand =
  | OConst: n:int -> operand
  | OReg: r:reg -> operand
  | OMem: m:maddr -> operand

type mov128_op =   
  | Mov128Xmm: x:xmm -> mov128_op
  | Mov128Mem: m:maddr -> mov128_op

type precode (t_ins:Type0) (t_ocmp:Type0) =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
  | IfElse: ifCond:t_ocmp -> ifTrue:precode t_ins t_ocmp -> ifFalse:precode t_ins t_ocmp -> precode t_ins t_ocmp
  | While: whileCond:t_ocmp -> whileBody:precode t_ins t_ocmp -> precode t_ins t_ocmp

let valid_dst (o:operand) : bool =
  not (OConst? o || (OReg? o && OReg?.r o = rsp))
