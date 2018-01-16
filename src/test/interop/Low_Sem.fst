module Low_Sem

module HS = FStar.HyperStack
open Machine

type mem = HS.mem

noeq type state = {
  ok:bool;
  regs : reg -> nat64;
  mem: mem;
}

let eval_reg (r:reg) (s:state) : nat64 = s.regs r

let eval_maddr (m:maddr) (s:state) : int =
  match m with
  | MConst n -> n
  | MReg r offset -> (eval_reg r s) + offset
