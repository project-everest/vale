module X64.Vale.StateLemmas_i
open X64.Machine_s
open X64.Vale.State_i
open FStar.UInt
open FStar.FunctionalExtensionality
module S = X64.Semantics_s
module TS = X64.Taint_Semantics_s
module M = TransparentMap

unfold let ok' = S.Mkstate?.ok
unfold let regs' = S.Mkstate?.regs
unfold let flags' = S.Mkstate?.flags
unfold let mem' = S.Mkstate?.mem
unfold let trace' = TS.MktraceState?.trace
unfold let memTaint' = TS.MktraceState?.memTaint

let state_to_S (s:state) : TS.traceState = {
  TS.state = {
    S.ok = s.ok;
    S.regs = (fun r -> s.regs r);
    S.flags = int_to_nat64 s.flags;
    S.mem = s.mem;
  };
  TS.trace = s.trace;
  TS.memTaint = s.memTaint;
}

let state_of_S (s:TS.traceState) : state =
  let { S.ok = ok; S.regs = regs; S.flags = flags; S.mem = mem } = s.TS.state in {
    ok = ok;
    regs = (fun r -> regs r);
    flags = flags;
    mem = mem;
    trace = s.TS.trace;
    memTaint = s.TS.memTaint
  }

val lemma_to_ok : s:state -> Lemma
  (ensures s.ok == ok' ((state_to_S s).TS.state))
  [SMTPat s.ok]

val lemma_to_flags : s:state -> Lemma
  (ensures s.flags == flags' ((state_to_S s).TS.state))
  [SMTPat s.flags]

val lemma_to_mem : s:state -> Lemma
  (ensures s.mem == mem' ((state_to_S s).TS.state))
  [SMTPat s.mem]
  
val lemma_to_reg : s:state -> r:reg -> Lemma
  (ensures s.regs r == regs' ((state_to_S s).TS.state) r)
  [SMTPat (s.regs r)]

val lemma_to_trace : s:state -> Lemma
  (ensures s.trace == trace' (state_to_S s))
  [SMTPat s.trace]

val lemma_to_memTaint : s:state -> Lemma
  (ensures s.memTaint == memTaint' (state_to_S s))
  [SMTPat s.memTaint]

val lemma_to_eval_operand : s:state -> o:operand -> Lemma
  (ensures eval_operand o s == S.eval_operand o ((state_to_S s).TS.state))
  [SMTPat (eval_operand o s)]

val lemma_to_valid_operand : s:state -> o:operand -> t:taint -> Lemma
  (ensures valid_operand o s t ==> S.valid_operand o ((state_to_S s).TS.state) /\ TS.taint_match o t (state_to_S s).TS.memTaint (state_to_S s).TS.state)
  [SMTPat (valid_operand o s t)]

val lemma_of_to : s:state -> Lemma
  (ensures s == state_of_S (state_to_S s))
  [SMTPat (state_of_S (state_to_S s))]

val lemma_to_of : s:TS.traceState -> Lemma
  (ensures s == state_to_S (state_of_S s))
  [SMTPat (state_to_S (state_of_S s))]

val lemma_regs_inv : s1:state -> s2:state -> Lemma
  (ensures s1.regs == s2.regs ==> regs' ((state_to_S s1).TS.state) == regs' ((state_to_S s2).TS.state))
  [SMTPat ((state_to_S s1).TS.state.S.regs == (state_to_S s2).TS.state.S.regs)]
