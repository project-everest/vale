module StateUpdateTest
(*
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open X64.Vale.InsBasic
open FStar.Tactics

val va_code_state_update_test : va_dummy:unit -> Tot va_code
let va_code_state_update_test () =
  (va_Block (va_CCons (va_code_Mov64 (va_op_dst_operand_reg rdx) (va_op_operand_reg rax)) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg rcx) (va_op_operand_reg rdx)) (va_CNil ()))))

irreducible val va_lemma_state_update_test : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_state_update_test ()) va_s0 va_sN) /\ (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_state_eq va_sM (va_update_reg rcx va_sM (va_update_reg rdx va_sM
    (va_update_ok va_sM va_s0)))))))
irreducible let va_lemma_state_update_test va_b0 va_s0 va_sN =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  let (va_b2, va_s2) = (va_lemma_Mov64 va_b1 va_s0 va_sM (va_op_dst_operand_reg rdx)
    (va_op_operand_reg rax)) in

  // let upd_lemma (m : tmap int uint64) : Lemma
  //   (ensures (m.[reg_to_int rax] == 
  // 			 (m.[reg_to_int rdx] <- m.[reg_to_int rax]).[reg_to_int rax])) =
  //   assert_by_tactic (norm[Simpl;Delta;Primops];; dump "before trefl";; trivial;; dump "after trivial")
  // 		   (m.[reg_to_int rax] == (m.[reg_to_int rdx] <- (m.[reg_to_int rax])).[reg_to_int rax])
  // in
  //   upd_lemma (va_s0.regs);

 (* The following won't work because the normalizer does not destruct va_s0 and gets stuck in the match statement trying to project the record fields, part of the output:
 (match va_s0 with
        | (Mkstate _ __fname__regs#1094345 _ _)  -> __fname__regs@2) 0)*)

  // assert_by_tactic (norm[Simpl;Delta;Primops];; dump "before trivial";; trivial;; dump "trivial")
  //   (va_s0.regs0.[reg_to_int rax] == (va_s0.regs.[reg_to_int rdx] <- va_s0.regs.[reg_to_int rax]).[reg_to_int rax]);

 (* We can destruct va_s0 without tactics *)
  let (Mkstate ok0 regs0 flags0 mem0 :va_state) = va_s0 in
  // and now this works.
  let s1 = update_reg rdx (regs0 rax) (Mkstate ok0 regs0 flags0 mem0) in
  assert_by_tactic (regs0 rax == s1.regs rax) (norm[simplify;delta;primops];; dump "before trefl";; trivial;; dump "trivial");

  let (va_b4, va_s4) = (va_lemma_Mov64 va_b2 va_s2 va_sM (va_op_dst_operand_reg rcx)
    (va_op_operand_reg rdx)) in

  assert ((va_get_reg rax va_s4) == (va_get_reg rax va_old_s));
  let va_sM = (va_lemma_empty va_s4 va_sM) in
  (va_bM, va_sM)
*)

