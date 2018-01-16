module Machine

let nat64_max = 0x10000000000000000
unfold let nat64 = x:nat{x < nat64_max}

type reg =
  | Rax
  | Rbx

type maddr =
  | MConst: n:int -> maddr
  | MReg: r:reg -> offset:int -> maddr

type operand =
  | OConst: n:nat64 -> operand
  | OReg: r:reg -> operand
  | OMem: m:maddr -> operand

type dst_op = o:operand{not (OConst? o)}

type code =
   | Mov : dst:dst_op -> src:operand -> code
   | Add : dst:dst_op -> src:operand -> code
