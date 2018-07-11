module X64.Vale.StateLemmas_i
open X64.Machine_s
open X64.Vale.State_i
module S = X64.Semantics_s
module M = TransparentMap
module BS = X64.Bytes_Semantics_s
module ME = X64.Memory_i_s
module TS = X64.Taint_Semantics_s

#reset-options "--initial_fuel 2 --max_fuel 2"

let state_to_S (s:state) : GTot TS.traceState = 
  {
  TS.state = (let s' = {
    BS.ok = s.ok;
    BS.regs = (fun r -> Map16_i.sel s.regs r);
    BS.xmms = (fun x -> Map16_i.sel s.xmms x);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = ME.get_heap s.mem
  } in
  { ME.state = s'; ME.mem = s.mem});
  TS.trace = s.trace;
  TS.memTaint = s.memTaint;
  }

let regs_of_S (#a:Type0) (m:reg -> a) : Pure (Map16_i.map a)
  (requires True)
  (ensures fun m' ->
    (forall (r:reg).{:pattern (m r) \/ (Map16_i.sel m' r)} m r == Map16_i.sel m' r)
  )
  =
  let m0_3 = ((m 0, m 1), (m 2, m 3)) in
  let m4_7 = ((m 4, m 5), (m 6, m 7)) in
  let m8_11 = ((m 8, m 9), (m 10, m 11)) in
  let m12_15 = ((m 12, m 13), (m 14, m 15)) in
  let m' = ((m0_3, m4_7), (m8_11, m12_15)) in
  assert_norm (m  0 == Map16_i.sel m'  0);
  assert_norm (m  1 == Map16_i.sel m'  1);
  assert_norm (m  2 == Map16_i.sel m'  2);
  assert_norm (m  3 == Map16_i.sel m'  3);
  assert_norm (m  4 == Map16_i.sel m'  4);
  assert_norm (m  5 == Map16_i.sel m'  5);
  assert_norm (m  6 == Map16_i.sel m'  6);
  assert_norm (m  7 == Map16_i.sel m'  7);
  assert_norm (m  8 == Map16_i.sel m'  8);
  assert_norm (m  9 == Map16_i.sel m'  9);
  assert_norm (m 10 == Map16_i.sel m' 10);
  assert_norm (m 11 == Map16_i.sel m' 11);
  assert_norm (m 12 == Map16_i.sel m' 12);
  assert_norm (m 13 == Map16_i.sel m' 13);
  assert_norm (m 14 == Map16_i.sel m' 14);
  assert_norm (m 15 == Map16_i.sel m' 15);
  m'

let state_of_S (s:TS.traceState) : GTot state =
  let { ME.state = st; ME.mem = mem } = s.TS.state in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = _} = st in
  {
    ok = ok;
    regs = regs_of_S regs;
    xmms = regs_of_S xmms;
    flags = flags;
    mem = mem;
    trace = s.TS.trace;
    memTaint = s.TS.memTaint;
  }

let lemma_to_ok s = ()
let lemma_to_flags s = ()
let lemma_to_mem s = ()
let lemma_to_reg s r = ()
let lemma_to_xmm s x = ()
let lemma_to_trace s = ()
let lemma_to_memTaint s = ()
let lemma_to_eval_operand s o = ()
let lemma_to_eval_xmm s x = ()
let lemma_to_valid_operand s o = ()
let lemma_to_valid_taint s o t = ()

let lemma_of_to s =
  assert (state_eq s (state_of_S (state_to_S s)));
  ()

let lemma_to_of s =
  let s' = state_of_S s in
  let s'' = state_to_S s' in
  let { ME.state = st; ME.mem = mem } = s.TS.state in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = heap} = st in
  let { ME.state = st''; ME.mem = mem'' } = s''.TS.state in
  let { BS.ok = ok''; BS.regs = regs''; BS.xmms = xmms''; BS.flags = flags''; BS.mem = heap''} = st'' in
  assert (feq regs regs'');
  assert (feq xmms xmms'');
  ME.same_heap s.TS.state s''.TS.state;
  ()

let lemma_valid_taint64 = ME.lemma_valid_taint64
let lemma_valid_taint128  = ME.lemma_valid_taint128

let modify_trace s0 b =
  let s1 = {s0 with trace = BranchPredicate(b)::s0.trace} in
  let s0' = state_to_S s0 in
  let s1' = state_to_S s1 in
  assert (FunctionalExtensionality.feq s0'.TS.state.ME.state.BS.regs s1'.TS.state.ME.state.BS.regs);
  assert (FunctionalExtensionality.feq s0'.TS.state.ME.state.BS.xmms s1'.TS.state.ME.state.BS.xmms)  

let same_memTaint64 = ME.same_memTaint64
let same_memTaint128 = ME.same_memTaint128
