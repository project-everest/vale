module X64.Vale.StateLemmas_i
open X64.Machine_s
open X64.Vale.State_i
open FStar.FunctionalExtensionality
module S = X64.Semantics_s

val lemma_to_eval_operand : s:state -> o:operand -> Lemma
  (ensures eval_operand o s == S.eval_operand o s)
  [SMTPat (eval_operand o s)]

val lemma_to_eval_xmm : s:state -> x:xmm -> Lemma
  (ensures eval_xmm x s == S.eval_xmm x s)
  [SMTPat (eval_xmm x s)]

val lemma_to_valid_operand : s:state -> o:operand -> Lemma
  (ensures valid_operand o s ==> S.valid_operand o s)
  [SMTPat (valid_operand o s)]

