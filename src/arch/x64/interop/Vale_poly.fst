module Vale_poly

open X64.Machine_s
open X64.Memory_i
open X64.Vale.State_i
open X64.Vale.Decls_i
open Poly1305.Spec_s
open X64.Poly1305.Math_i
open X64.Poly1305.Util_i
open X64.Poly1305

let va_code_poly = fun () -> va_code_poly1305 false

val va_lemma_poly : va_b0:va_code -> va_s0:va_state -> ctx_b:buffer64 -> inp_b:buffer64 -> len:nat64
  -> Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires ((va_require_total va_b0 (va_code_poly ()) va_s0) /\ (va_get_ok va_s0) /\ (let
    ctx_in = (va_get_reg rdi va_s0) in let inp_in = (va_get_reg rsi va_s0) in let len_in = (va_get_reg rdx va_s0) in let n = 18446744073709551616 in let p = n
    `op_Multiply` n `op_Multiply` 4 - 5 in len == len_in /\ (buffers_disjoint ctx_b inp_b) /\ (validSrcAddrs64
    (va_get_mem va_s0) ctx_in ctx_b 24 (va_get_memTaint va_s0) Public) /\ (validSrcAddrs64 (va_get_mem va_s0) inp_in inp_b
    (readable_words len_in) (va_get_memTaint va_s0) Public) /\ inp_in + len_in < pow2_64)))
  (ensures (fun (va_sM, va_fM) -> ((va_ensure_total va_b0 va_s0 va_sM va_fM) /\ 
    (va_get_ok va_sM) /\
    (let ctx_in = (va_get_reg rdi va_s0) in 
    let inp_in = (va_get_reg rsi va_s0) in
    let len_in = (va_get_reg rdx va_s0) in
    let n = 18446744073709551616 in
    let p = n `op_Multiply` n `op_Multiply` 4 - 5 in 
    let key_r0 = (buffer64_read ctx_b 3 (va_get_mem va_s0)) in 
    let key_r1 = (buffer64_read ctx_b 4 (va_get_mem va_s0)) in
    let key_s0 = (buffer64_read ctx_b 5 (va_get_mem va_s0)) in 
    let key_s1 = (buffer64_read ctx_b 6 (va_get_mem va_s0)) in
    let key_r = (lowerUpper128_opaque key_r0 key_r1) in
    let key_s = (lowerUpper128_opaque key_s0 key_s1) in
    
    (validSrcAddrs64 (va_get_mem va_sM) ctx_in
    ctx_b 24 (va_get_memTaint va_sM) Public) /\ (validSrcAddrs64 (va_get_mem va_sM) inp_in inp_b (readable_words len_in) (va_get_memTaint va_sM) Public) /\
    (modifies_buffer ctx_b (va_get_mem va_s0) (va_get_mem va_sM)) /\ (let h0_out = (buffer64_read
    ctx_b 0 (va_get_mem va_sM)) in let h1_out = (buffer64_read ctx_b 1 (va_get_mem va_sM)) in
    let h = (lowerUpper128_opaque h0_out h1_out) in (let inp_mem = (seqTo128 (buffer64_as_seq (va_get_mem
    va_sM) inp_b)) in h == (poly1305_hash key_r key_s inp_mem len_in) /\ (va_get_reg rbx va_sM) ==
    (va_get_reg rbx va_s0) /\ (va_get_reg rbp va_sM) == (va_get_reg rbp va_s0) /\ (va_get_reg rdi
    va_sM) == (va_get_reg rdi va_s0) /\ (va_get_reg rsi va_sM) == (va_get_reg rsi va_s0) /\
    (va_get_reg r12 va_sM) == (va_get_reg r12 va_s0) /\ (va_get_reg r13 va_sM) == (va_get_reg r13
    va_s0) /\ (va_get_reg r14 va_sM) == (va_get_reg r14 va_s0) /\ (va_get_reg r15 va_sM) ==
    (va_get_reg r15 va_s0)))) /\ (va_state_eq va_sM (va_update_trace va_sM (va_update_mem va_sM (va_update_flags va_sM
    (va_update_reg rbp va_sM (va_update_reg rbx va_sM (va_update_reg r14 va_sM (va_update_reg r12
    va_sM (va_update_reg r11 va_sM (va_update_reg rdx va_sM (va_update_reg rsi va_sM (va_update_reg
    rdi va_sM (va_update_reg r15 va_sM (va_update_reg r13 va_sM (va_update_reg r10 va_sM
    (va_update_reg r9 va_sM (va_update_reg r8 va_sM (va_update_reg rcx va_sM (va_update_reg rax
    va_sM (va_update_ok va_sM va_s0)))))))))))))))))))))))

let va_lemma_poly va_b0 va_s0 ctx_b inp_b len =
  let key_r0 = buffer64_read ctx_b 3 (va_get_mem va_s0) in
  let key_r1 = (buffer64_read ctx_b 4 (va_get_mem va_s0)) in
  let key_s0 = (buffer64_read ctx_b 5 (va_get_mem va_s0)) in
  let key_s1 = (buffer64_read ctx_b 6 (va_get_mem va_s0)) in
  let key_r = lowerUpper128_opaque key_r0 key_r1 in
  let key_s = lowerUpper128_opaque key_s0 key_s1 in
  let va_sM, va_fM, _ = va_lemma_poly1305 va_b0 va_s0 false key_r key_s ctx_b inp_b in
  va_sM, va_fM
