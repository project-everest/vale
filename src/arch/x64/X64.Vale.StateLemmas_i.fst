module X64.Vale.StateLemmas_i
open X64.Machine_s
open X64.Vale.State_i
module S = X64.Semantics_s
module M = TransparentMap
module BS = X64.Bytes_Semantics_s
module ME = X64.Memory_i_s

#reset-options "--initial_fuel 2 --max_fuel 2"

let state_to_S (s:state) : GTot ME.state = 
  let s' = {
    BS.ok = s.ok;
    BS.regs = (fun r -> Map16_i.sel s.regs (reg_to_int r));
    BS.xmms = (fun x -> Map16_i.sel s.xmms x);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = ME.get_heap s.mem
  } in
  { ME.state = s'; ME.mem = s.mem}

let regs_of_S (m:reg -> nat64) : Pure (Map16_i.map nat64)
  (requires True)
  (ensures fun m' ->
    (forall (r:reg).{:pattern (m r) \/ (Map16_i.sel m' (reg_to_int r))} m r == Map16_i.sel m' (reg_to_int r))
  )
  =
  let m0_3 = ((m Rax, m Rbx), (m Rcx, m Rdx)) in
  let m4_7 = ((m Rsi, m Rdi), (m Rbp, m Rsp)) in
  let m8_11 = ((m R8, m R9), (m R10, m R11)) in
  let m12_15 = ((m R12, m R13), (m R14, m R15)) in
  let m' = ((m0_3, m4_7), (m8_11, m12_15)) in
  assert_norm (m Rax == Map16_i.sel m'  0);
  assert_norm (m Rbx == Map16_i.sel m'  1);
  assert_norm (m Rcx == Map16_i.sel m'  2);
  assert_norm (m Rdx == Map16_i.sel m'  3);
  assert_norm (m Rsi == Map16_i.sel m'  4);
  assert_norm (m Rdi == Map16_i.sel m'  5);
  assert_norm (m Rbp == Map16_i.sel m'  6);
  assert_norm (m Rsp == Map16_i.sel m'  7);
  assert_norm (m R8  == Map16_i.sel m'  8);
  assert_norm (m R9  == Map16_i.sel m'  9);
  assert_norm (m R10 == Map16_i.sel m' 10);
  assert_norm (m R11 == Map16_i.sel m' 11);
  assert_norm (m R12 == Map16_i.sel m' 12);
  assert_norm (m R13 == Map16_i.sel m' 13);
  assert_norm (m R14 == Map16_i.sel m' 14);
  assert_norm (m R15 == Map16_i.sel m' 15);
  m'

let xmms_of_S (m:xmm -> quad32) : Pure (Map16_i.map quad32)
  (requires True)
  (ensures fun m' ->
    (forall (x:xmm).{:pattern (m x) \/ (Map16_i.sel m' x)} m x == Map16_i.sel m' x)
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

let state_of_S (s:ME.state) : state =
  let { ME.state = st; ME.mem = mem } = s in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = _} = st in
  {
    ok = ok;
    regs = regs_of_S regs;
    xmms = xmms_of_S xmms;
    flags = flags;
    mem = mem;
  }

let lemma_to_ok s = ()
let lemma_to_flags s = ()
let lemma_to_mem s = ()
let lemma_to_reg s r = ()
let lemma_to_xmm s x = ()
let lemma_to_eval_operand s o = ()
let lemma_to_eval_xmm s x = ()
let lemma_to_valid_operand s o = ()

let lemma_of_to s =
  assert (state_eq s (state_of_S (state_to_S s)));
  ()

let lemma_to_of s =
  let s' = state_of_S s in
  let s'' = state_to_S s' in
  let { ME.state = st; ME.mem = mem } = s in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = heap} = st in
  let { ME.state = st''; ME.mem = mem'' } = s'' in
  let { BS.ok = ok''; BS.regs = regs''; BS.xmms = xmms''; BS.flags = flags''; BS.mem = heap''} = st'' in
  assert (feq regs regs'');
  assert (feq xmms xmms'');
  ME.same_heap s s'';
  ()
