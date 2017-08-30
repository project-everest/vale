module X64.Vale.StateLemmas_i
open X64.Machine_s
open X64.Vale.State_i
open FStar.UInt
open FStar.FunctionalExtensionality
module S = X64.Semantics_s
module M = TransparentMap

unfold let ok' = S.Mkstate?.ok
unfold let regs' = S.Mkstate?.regs
unfold let flags' = S.Mkstate?.flags
unfold let mem' = S.Mkstate?.mem

val state_to_S : s:state -> S.state
val state_of_S : s:S.state -> state

val lemma_to_ok : s:state -> Lemma
  (ensures s.ok == ok' (state_to_S s))
  [SMTPat s.ok]

val lemma_to_flags : s:state -> Lemma
  (ensures s.flags == UInt64.v (flags' (state_to_S s)))
  [SMTPat s.flags]

val lemma_to_mem : s:state -> Lemma
  (ensures s.mem == mem' (state_to_S s))
  [SMTPat s.mem]
  
val lemma_to_reg : s:state -> r:reg -> Lemma
  (ensures s.regs r == UInt64.v (regs' (state_to_S s) r))
  [SMTPat (s.regs r)]

val lemma_to_eval_operand : s:state -> o:operand -> Lemma
  (ensures eval_operand o s == UInt64.v (S.eval_operand o (state_to_S s)))
  [SMTPat (eval_operand o s)]

val lemma_to_valid_operand : s:state -> o:operand -> Lemma
  (ensures valid_operand o s ==> S.valid_operand o (state_to_S s))
  [SMTPat (valid_operand o s)]

val lemma_of_to : s:state -> Lemma
  (ensures s == state_of_S (state_to_S s))
  [SMTPat (state_of_S (state_to_S s))]

val lemma_to_of : s:S.state -> Lemma
  (ensures s == state_to_S (state_of_S s))
  [SMTPat (state_to_S (state_of_S s))]

