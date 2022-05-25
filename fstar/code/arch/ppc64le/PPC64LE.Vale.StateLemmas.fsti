module PPC64LE.Vale.StateLemmas
open PPC64LE.Machine_s
open PPC64LE.Vale.State
module S = PPC64LE.Semantics_s

val lemma_to_eval_reg : s:state -> r:reg -> Lemma
  (ensures eval_reg r s == S.eval_reg r s)
  [SMTPat (eval_reg r s)]

val lemma_to_eval_vec : s:state -> v:vec -> Lemma
  (ensures eval_vec v s == S.eval_vec v s)
  [SMTPat (eval_vec v s)]

val lemma_to_eval_maddr : s:state -> m:maddr -> Lemma
  (ensures eval_maddr m s == S.eval_maddr m s)
  [SMTPat (eval_maddr m s)]

val lemma_to_eval_cmp_opr : s:state -> o:cmp_opr -> Lemma
  (ensures eval_cmp_opr o s == S.eval_cmp_opr o s)
  [SMTPat (eval_cmp_opr o s)]

val lemma_to_valid_maddr64 : s:state -> m:maddr -> Lemma
  (ensures valid_maddr64 m s ==> S.valid_maddr64 m s)
  [SMTPat (valid_maddr64 m s)]

