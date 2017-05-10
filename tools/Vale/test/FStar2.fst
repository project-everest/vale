
module FStar2

open Vale
open Semantics
open FStar.UInt

#reset-options "--z3rlimit 200"


val va_code_Mov64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_code_Mov64 dst src =
  (Ins (Mov64 dst src))

irreducible val va_lemma_Mov64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Mov64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (va_eval_operand_uint64 va_s0
    src) /\ (va_state_eq va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0))))))
irreducible let va_lemma_Mov64 va_b0 va_s0 va_sN dst src =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)

val va_code_Add64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_code_Add64Wrap dst src =
  (Ins (Add64 dst src))

irreducible val va_lemma_Add64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Add64Wrap dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == ((va_eval_dst_operand_uint64
    va_s0 dst) + (va_eval_operand_uint64 va_s0 src)) `op_Modulus` nat64_max /\ (va_state_eq va_sM
    (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_lemma_Add64Wrap va_b0 va_s0 va_sN dst src =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (va_sM == eval_ins (Add64 dst src) va_s0);
  (va_bM, va_sM)

val va_code_AddLea64 : dst:va_dst_operand -> src1:va_operand -> src2:va_operand -> Tot va_code
let va_code_AddLea64 dst src1 src2 =
  (Ins (AddLea64 dst src1 src2))

irreducible val va_lemma_AddLea64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src1:va_operand -> src2:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_AddLea64 dst src1 src2) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src1 va_s0) /\
    (va_is_src_operand_uint64 src2 va_s0) /\ (va_get_ok va_s0) /\ (va_eval_operand_uint64 va_s0
    src1) + (va_eval_operand_uint64 va_s0 src2) < nat64_max))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (va_eval_operand_uint64 va_s0
    src1) + (va_eval_operand_uint64 va_s0 src2) /\ (va_state_eq va_sM (va_update_ok va_sM
    (va_update_dst_operand dst va_sM va_s0))))))
irreducible let va_lemma_AddLea64 va_b0 va_s0 va_sN dst src1 src2 =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)

val va_code_Adc64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_code_Adc64Wrap dst src =
  (Ins (AddCarry64 dst src))

irreducible val va_lemma_Adc64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Adc64Wrap dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (((va_eval_dst_operand_uint64
    va_s0 dst) + (va_eval_operand_uint64 va_s0 src)) + (if (cf (va_get_flags va_s0)) then 1 else
    0)) `op_Modulus` nat64_max /\ (cf (va_get_flags va_sM)) == (((va_eval_dst_operand_uint64 va_s0
    dst) + (va_eval_operand_uint64 va_s0 src)) + (if (cf (va_get_flags va_s0)) then 1 else 0) >=
    18446744073709551616) /\ (va_state_eq va_sM (va_update_flags va_sM (va_update_ok va_sM
    (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_lemma_Adc64Wrap va_b0 va_s0 va_sN dst src =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (va_sM == eval_ins (AddCarry64 dst src) va_s0);
  (va_bM, va_sM)

val va_code_Sub64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_code_Sub64 dst src =
  (Ins (Sub64 dst src))

irreducible val va_lemma_Sub64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Sub64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0) /\ 0 <= (va_eval_dst_operand_uint64 va_s0 dst) - (va_eval_operand_uint64 va_s0 src)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (va_eval_dst_operand_uint64
    va_s0 dst) - (va_eval_operand_uint64 va_s0 src) /\ (va_state_eq va_sM (va_update_flags va_sM
    (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_lemma_Sub64 va_b0 va_s0 va_sN dst src =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (va_sM == eval_ins (Sub64 dst src) va_s0);
  (va_bM, va_sM)

val va_code_Sub64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_code_Sub64Wrap dst src =
  (Ins (Sub64 dst src))

irreducible val va_lemma_Sub64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Sub64Wrap dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == ((va_eval_dst_operand_uint64
    va_s0 dst) - (va_eval_operand_uint64 va_s0 src)) `op_Modulus` nat64_max /\ (va_state_eq va_sM
    (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_lemma_Sub64Wrap va_b0 va_s0 va_sN dst src =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (va_sM == eval_ins (Sub64 dst src) va_s0);
  (va_bM, va_sM)

val va_code_Mul64Wrap : src:va_operand -> Tot va_code
let va_code_Mul64Wrap src =
  (Ins (Mul64 src))

irreducible val va_lemma_Mul64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Mul64Wrap src) va_s0 va_sN) /\ (va_is_src_operand_uint64
    src va_s0) /\ (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_get_reg Rax va_sM) == ((va_get_reg Rax va_s0) `op_Multiply`
    (va_eval_operand_uint64 va_s0 src)) `op_Modulus` nat64_max /\ (va_get_reg Rdx va_sM) ==
    ((va_get_reg Rax va_s0) `op_Multiply` (va_eval_operand_uint64 va_s0 src)) `op_Division`
    nat64_max /\ (va_state_eq va_sM (va_update_reg Rdx va_sM (va_update_reg Rax va_sM
    (va_update_flags va_sM (va_update_ok va_sM va_s0))))))))
irreducible let va_lemma_Mul64Wrap va_b0 va_s0 va_sN src =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)

val va_code_IMul64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_code_IMul64Wrap dst src =
  (Ins (IMul64 dst src))

irreducible val va_lemma_IMul64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_IMul64Wrap dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == ((va_eval_dst_operand_uint64
    va_s0 dst) `op_Multiply` (va_eval_operand_uint64 va_s0 src)) `op_Modulus` nat64_max /\
    (va_state_eq va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM
    va_s0)))))))
irreducible let va_lemma_IMul64Wrap va_b0 va_s0 va_sN dst src =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (va_sM == eval_ins (IMul64 dst src) va_s0);
  (va_bM, va_sM)


let logxor64 (x:nat64) (y:nat64) :nat64 =
  logxor #64 x y

let shift_left64 (x:nat64) (amt:nat64) :nat64 =
  shift_left #64 x amt

let shift_right64 (x:nat64) (amt:nat64) :nat64 =
  shift_right #64 x amt


val va_code_Xor64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_code_Xor64 dst src =
  (Ins (Xor64 dst src))

irreducible val va_lemma_Xor64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Xor64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (logxor64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_operand_uint64 va_s0 src)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_lemma_Xor64 va_b0 va_s0 va_sN dst src =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (va_sM == eval_ins (Xor64 dst src) va_s0);
  (va_bM, va_sM)

val va_code_Shl64 : dst:va_dst_operand -> amt:va_shift_amt -> Tot va_code
let va_code_Shl64 dst amt =
  (Ins (Shl64 dst amt))

irreducible val va_lemma_Shl64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> amt:va_shift_amt
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Shl64 dst amt) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_shift_amt_uint64 amt va_s0) /\
    (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (shift_left64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_shift_amt_uint64 va_s0 amt)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_lemma_Shl64 va_b0 va_s0 va_sN dst amt =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (va_sM == eval_ins (Shl64 dst amt) va_s0);
  (va_bM, va_sM)

val va_code_Shr64 : dst:va_dst_operand -> amt:va_shift_amt -> Tot va_code
let va_code_Shr64 dst amt =
  (Ins (Shr64 dst amt))

irreducible val va_lemma_Shr64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> amt:va_shift_amt
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Shr64 dst amt) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_shift_amt_uint64 amt va_s0) /\
    (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (shift_right64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_shift_amt_uint64 va_s0 amt)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_lemma_Shr64 va_b0 va_s0 va_sN dst amt =
  ();
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (va_sM == eval_ins (Shr64 dst amt) va_s0);
  (va_bM, va_sM)
