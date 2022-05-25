module PPC64LE.Machine_s
open Defs_s

unfold let pow2_64 = Words_s.pow2_64

unfold let nat8 = Words_s.nat8
unfold let nat16 = Words_s.nat16
unfold let nat32 = Words_s.nat32
unfold let nat64 = Words_s.nat64
let int_to_nat64 (i:int) : n:nat64{0 <= i && i < pow2_64 ==> i == n} =
  Words_s.int_to_natN pow2_64 i
unfold let quad32 = Types_s.quad32

type reg =
  | R0
  | R1
  | R2
  | R3
  | R4
  | R5
  | R6
  | R7
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | R16
  | R17
  | R18
  | R19
  | R20
  | R21
  | R22
  | R23
  | R24
  | R25
  | R26
  | R27
  | R28
  | R29
  | R30
  | R31

type vec =
  | V0
  | V1
  | V2
  | V3
  | V4
  | V5
  | V6
  | V7
  | V8
  | V9
  | V10
  | V11
  | V12
  | V13
  | V14
  | V15
  | V16
  | V17
  | V18
  | V19
  | V20
  | V21
  | V22
  | V23
  | V24
  | V25
  | V26
  | V27
  | V28
  | V29
  | V30
  | V31

// Immediate operand of logical compare, and, or, and xor instructions
type imm16 = i:int{0 <= i && i <= 65535}
// Immediate operand of compare, add (with signed immediate) instructions
type simm16 = i:int{-32768 <= i && i <= 32767}
// Immediate operand of sub (with negative signed immediate) instruction
type nsimm16 = i:int{-32767 <= i && i <= 32768}
// Immediate operand of rotate, shift, and clear for 64-bit instructions
type bits64 = i:int{0 <= i && i < 64}
// Immediate operand of rotate, shift, and clear for 32-bit instructions
type bits32 = i:int{0 <= i && i < 32}
// Immediate operand of vector shift left double by octet
type quad32bytes = i:int{0 <= i && i < 16}

type mem_entry =
| Mem8: v:nat8 -> mem_entry
| Mem16: v:nat16 -> mem_entry
| Mem32: v:nat32 -> mem_entry
| Mem64: v:nat64 -> mem_entry

type memory = Map.t int mem_entry

let regs_t = FStar.FunctionalExtensionality.restricted_t reg (fun _ -> nat64)
let vecs_t = FStar.FunctionalExtensionality.restricted_t vec (fun _ -> quad32)
[@va_qattr] unfold let regs_make (f:reg -> nat64) : regs_t = FStar.FunctionalExtensionality.on_dom reg f
[@va_qattr] unfold let vecs_make (f:vec -> quad32) : vecs_t = FStar.FunctionalExtensionality.on_dom vec f

// Condition Register (CR) Field 0 is interpreted as individual 4-bits that can be set as the implicit
// results of certain fixed-point instructions.
// Fixed-point compare instructions in which CR field operand is default or 0 and fixed-point arithmetic
// instructions that have "." suffix in the instruction mnemonic (Rc=1) alter the CR Field 0 (CR0) fields.
// The fourth bit of CR0 reflects the Summary Overflow (SO) field of Fixed-Point Exception Register (XER).
type cr0_t = {
  lt:bool;      // negative result
  gt:bool;      // positive result
  eq:bool;      // zero result
}

// Fixed-Point Exception Register (XER) stores the status of overflow and carry occurrences of
// instructions that can overflow with OE=1 and carry. Compare instructions don't alter XER.
type xer_t = {
  ov:bool;     // Overflow
  ca:bool;     // Carry
}

noeq type state = {
  ok: bool;
  regs: regs_t;
  vecs: vecs_t;
  cr0: cr0_t;
  xer: xer_t;
  mem: memory;
}

let get_cr0 (r:nat64) =
  { lt = r >= 0x8000000000000000; gt = r < 0x8000000000000000; eq = r = 0 }

let valid_mem64 (addr:int) (m:memory) : bool =
  match Map.sel m addr with Mem64 _ -> true | _ -> false

assume val load_mem64 (addr:int) (m:memory) : Pure nat64
  (requires True)
  (ensures fun n -> match Map.sel m addr with Mem64 v -> v == n | _ -> True)

let store_mem64 (addr:int) (v:nat64) (m:memory) : memory =
  Map.upd m addr (Mem64 v)

type maddr = {
  address: reg;
  offset: int
}

// Memory offset bound of 32-bit, 16-bit, and 8-bit load/store instructions
let valid_maddr_offset (n:int) : bool =
  n >= -32768 && n <= 32767

// Memory offset bound of 64-bit load/store instructions
let valid_maddr_offset64 (n:int) : bool =
  n >= -32768 && n <= 32764 && n % 4 = 0

// Memory offset bound of 128-bit load/store instructions
let valid_maddr_offset128 (n:int) : bool =
  n >= -32768 && n <= 32752 && n % 16 = 0

type cmp_opr =
  | CReg: r:reg -> cmp_opr
  | CImm: n:imm16 -> cmp_opr

let valid_first_cmp_opr (o:cmp_opr) : bool =
  CReg? o

type precode (t_ins:Type0) (t_ocmp:Type0) =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
  | IfElse: ifCond:t_ocmp -> ifTrue:precode t_ins t_ocmp -> ifFalse:precode t_ins t_ocmp -> precode t_ins t_ocmp
  | While: whileCond:t_ocmp -> whileBody:precode t_ins t_ocmp -> precode t_ins t_ocmp
