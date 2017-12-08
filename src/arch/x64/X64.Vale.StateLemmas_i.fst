module X64.Vale.StateLemmas_i
open X64.Machine_s
open X64.Vale.State_i
open FStar.UInt
module S = X64.Semantics_s
module TS = X64.Taint_Semantics_s
module M = TransparentMap

#reset-options "--initial_fuel 2 --max_fuel 2"

let lemma_to_ok s = ()
let lemma_to_flags s = ()
let lemma_to_mem s = ()
let lemma_to_reg s r = ()
let lemma_to_trace s = ()
let lemma_to_memTaint s = ()
let lemma_to_eval_operand s o = ()
let lemma_to_valid_operand s o = ()
let lemma_to_valid_taint s o t = ()

let lemma_of_to s =
  assert (state_eq s (state_of_S (state_to_S s)));
  ()

let lemma_to_of s =
  let s' = state_of_S s in
  let s'' = state_to_S s' in
  let { S.ok = ok; S.regs = regs; S.flags = flags; S.mem = mem } = s.TS.state in
  let { S.ok = ok''; S.regs = regs''; S.flags = flags''; S.mem = mem'' } = s''.TS.state in
  assert (feq regs regs'');
  ()

let lemma_regs_inv s1 s2 =
  let s1' = state_to_S s1 in
  let s2' = state_to_S s2 in
  let regs1 = s1'.TS.state.S.regs in
  let regs2 = s2'.TS.state.S.regs in
  assert (s1.regs == s2.regs ==> feq regs1 regs2);
  ()
