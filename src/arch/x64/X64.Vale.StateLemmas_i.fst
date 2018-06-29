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
    BS.regs = (fun r -> s.regs r);
    BS.xmms = (fun x -> s.xmms x);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = ME.get_heap s.mem
  } in
  { ME.state = s'; ME.mem = s.mem}

let state_of_S (s:ME.state) : state =
  let { ME.state = st; ME.mem = mem } = s in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = _} = st in
  {
    ok = ok;
    regs = (fun r -> regs r);
    xmms = (fun x -> xmms x);
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
