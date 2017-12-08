module X64.Vale.StateLemmas_i
open X64.Machine_s
open X64.Vale.State_i
open FStar.UInt
module S = X64.Semantics_s
module M = TransparentMap

#reset-options "--initial_fuel 2 --max_fuel 2"

let state_to_S (s:state) : S.state = {
  S.ok = s.ok;
  S.regs = (fun r -> s.regs r);
  S.xmms = (fun x -> s.xmms x);
  S.flags = int_to_nat64 s.flags;
  S.mem = s.mem;
}

let state_of_S (s:S.state) : state =
  let { S.ok = ok; S.regs = regs; S.xmms = xmms; S.flags = flags; S.mem = mem } = s in {
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
  let { S.ok = ok; S.regs = regs; S.xmms = xmms; S.flags = flags; S.mem = mem } = s in
  let { S.ok = ok''; S.regs = regs''; S.xmms = xmms''; S.flags = flags''; S.mem = mem'' } = s'' in
  assert (feq regs regs'');
  assert (feq xmms xmms'');
  ()
