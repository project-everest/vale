module X64.Vale.Regs_i
// This interface should not refer to Semantics_s

open X64.Machine_s

type t = Map16_i.map nat64

[@va_qattr]
let reg_to_int (r:reg) : int =
  match r with
  | Rax -> 0
  | Rbx -> 1
  | Rcx -> 2
  | Rdx -> 3
  | Rsi -> 4
  | Rdi -> 5
  | Rbp -> 6
  | Rsp -> 7
  | R8 -> 8
  | R9 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15

val equal : regs1:t -> regs2:t -> Type0

val lemma_equal_intro : regs1:t -> regs2:t -> Lemma
  (requires forall r. Map16_i.sel regs1 (reg_to_int r) == Map16_i.sel regs2 (reg_to_int r))
  (ensures equal regs1 regs2)
  [SMTPat (equal regs1 regs2)]

val lemma_equal_elim : regs1:t -> regs2:t -> Lemma
  (requires equal regs1 regs2)
  (ensures regs1 == regs2)
  [SMTPat (equal regs1 regs2)]

