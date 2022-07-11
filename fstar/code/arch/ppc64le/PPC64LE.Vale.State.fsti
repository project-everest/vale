module PPC64LE.Vale.State
// This interface should not refer to Semantics_s

open Defs_s
open Prop_s
open PPC64LE.Machine_s

unfold let state = PPC64LE.Machine_s.state

[@va_qattr]
unfold let eval_reg (r:reg) (s:state) : nat64 = s.regs r
[@va_qattr]
unfold let eval_vec (v:vec) (s:state) : quad32 = s.vecs v
[@va_qattr]
unfold let eval_mem64 (ptr:int) (s:state) : nat64 = load_mem64 ptr s.mem

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  eval_reg m.address s + m.offset

[@va_qattr]
let eval_cmp_opr (o:cmp_opr) (s:state) : nat64 =
  match o with
  | CReg r -> eval_reg r s
  | CImm n -> int_to_nat64 n

[@va_qattr]
let update_reg (r:reg) (v:nat64) (s:state) : state =
  { s with regs = regs_make (fun (r':reg) -> if r = r' then v else s.regs r') }

[@va_qattr]
let update_vec (vr:vec) (v:quad32) (s:state) : state =
  { s with vecs = vecs_make (fun (vr':vec) -> if vr' = vr then v else s.vecs vr') }

[@va_qattr]
let update_mem64 (ptr:int) (v:nat64) (s:state) : state = { s with mem = store_mem64 ptr v s.mem }

[@va_qattr]
let valid_maddr64 (m:maddr) (s:state) : prop0 = 
  valid_maddr_offset64 m.offset && valid_mem64 (eval_maddr m s) s.mem

[@va_qattr]
let state_eq (s0:state) (s1:state) : prop0 =
  s0.ok == s1.ok /\
  Regs.equal s0.regs s1.regs /\
  //vecs.equal s0.vecs s1.vecs /\
  s0.cr0 == s1.cr0 /\
  s0.xer == s1.xer /\
  s0.mem == s1.mem

