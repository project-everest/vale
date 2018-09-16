module X64.Vale.State
// This interface should not refer to Semantics_s

open Prop_s
open X64.Machine_s

unfold let state = X64.Machine_s.state

[@va_qattr]
unfold let eval_reg (r:reg) (s:state) : nat64 = s.regs r
[@va_qattr]
unfold let eval_xmm (x:xmm) (s:state) : Types_s.quad32 = s.xmms x
[@va_qattr]
unfold let eval_mem (ptr:int) (s:state) : nat64 = load_mem64 ptr s.mem

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> eval_reg reg s + offset
    | MIndex base scale index offset -> eval_reg base s + scale * (eval_reg index s) + offset

[@va_qattr]
let to_nat64 (i:int) : nat64 =
  if 0 <= i && i < 0x10000000000000000 then i else int_to_nat64 i

[@va_qattr]
let eval_operand (o:operand) (s:state) : nat64 =
  match o with
  | OConst n -> to_nat64 n
  | OReg r -> eval_reg r s
  | OMem m -> eval_mem (eval_maddr m s) s

[@va_qattr]
let update_reg (r:reg) (v:nat64) (s:state) : state =
  { s with regs = fun r' -> if r = r' then v else s.regs r' }

[@va_qattr]
let update_xmm (x:xmm) (v:Types_s.quad32) (s:state) : state =
  { s with xmms = fun x' -> if x = x' then v else s.xmms x' }

[@va_qattr]
let update_mem (ptr:int) (v:nat64) (s:state) : state = { s with mem = store_mem64 ptr v s.mem }

[@va_qattr]
let update_operand (o:operand) (v:nat64) (sM:state) : state =
  match o with
  | OConst n -> sM
  | OReg r -> update_reg r v sM
  | OMem m -> update_mem (eval_maddr m sM) v sM

[@va_qattr]
let valid_maddr (m:maddr) (s:state) : prop0 = valid_mem64 (eval_maddr m s) s.mem

[@va_qattr]
let valid_operand (o:operand) (s:state) : prop0 =
  match o with
  | OConst n -> 0 <= n /\ n < pow2_64
  | OReg r -> True
  | OMem m -> valid_maddr m s

[@va_qattr]
let state_eq (s0:state) (s1:state) : prop0 =
  s0.ok == s1.ok /\
  Regs.equal s0.regs s1.regs /\
  Xmms.equal s0.xmms s1.xmms /\
  s0.flags == s1.flags /\
  s0.mem == s1.mem

