module Vale_memcpy

open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open X64.Vale.InsBasic
open X64.Vale.InsMem
#set-options "--z3rlimit 20"

val va_transparent_code_memcpy : va_dummy:unit -> Tot va_code
let va_transparent_code_memcpy () =
  (va_Block (va_CCons (va_code_Load64_buffer (va_op_dst_opr64_reg Rax) (va_op_reg_opr64_reg Rdi) 0)
    (va_CCons (va_code_Store64_buffer (va_op_reg_opr64_reg Rsi) (va_op_opr64_reg Rax) 0) (va_CNil
    ()))))
let va_code_memcpy () =
  (va_make_opaque (va_transparent_code_memcpy ()))

[@"opaque_to_smt"]
let va_lemma_memcpy va_b0 va_s0 src dest =
  (va_reveal_opaque (va_transparent_code_memcpy ()));
  let (va_old_s:va_state) = va_s0 in
  let (va_b1:va_codes) = (va_get_block va_b0) in
  let (va_s2, va_fc2) = (va_lemma_Load64_buffer (va_hd va_b1) va_s0 (va_op_dst_opr64_reg Rax)
    (va_op_reg_opr64_reg Rdi) 0 src 0) in
  let va_b2 = (va_tl va_b1) in
  let (va_s3, va_fc3) = (va_lemma_Store64_buffer (va_hd va_b2) va_s2 (va_op_reg_opr64_reg Rsi)
    (va_op_opr64_reg Rax) 0 dest 0) in
  let va_b3 = (va_tl va_b2) in
  let (va_sM, va_f3) = (va_lemma_empty_total va_s3 va_b3) in
  let va_f2 = (va_lemma_merge_total va_b2 va_s2 va_fc3 va_s3 va_f3 va_sM) in
  let va_fM = (va_lemma_merge_total va_b1 va_s0 va_fc2 va_s2 va_f2 va_sM) in
  (va_sM, va_fM)
