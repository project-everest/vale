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
    ctx_in = (va_get_reg Rdi va_s0) in let inp_in = (va_get_reg Rsi va_s0) in let len_in = (va_get_reg Rdx va_s0) in let n = 18446744073709551616 in let p = n
    `op_Multiply` n `op_Multiply` 4 - 5 in len == len_in /\ (buffers_disjoint ctx_b inp_b) /\ (validSrcAddrs64
    (va_get_mem va_s0) ctx_in ctx_b 24) /\ (validSrcAddrs64 (va_get_mem va_s0) inp_in inp_b
    (readable_words len_in)) /\ inp_in + len_in < pow2_64)))
  (ensures (fun (va_sM, va_fM) -> ((va_ensure_total va_b0 va_s0 va_sM va_fM) /\ 
    (va_get_ok va_sM) /\
    (let ctx_in = (va_get_reg Rdi va_s0) in 
    let inp_in = (va_get_reg Rsi va_s0) in
    let len_in = (va_get_reg Rdx va_s0) in
    let n = 18446744073709551616 in
    let p = n `op_Multiply` n `op_Multiply` 4 - 5 in 
    let key_r0 = (buffer64_read ctx_b 3 (va_get_mem va_s0)) in 
    let key_r1 = (buffer64_read ctx_b 4 (va_get_mem va_s0)) in
    let key_s0 = (buffer64_read ctx_b 5 (va_get_mem va_s0)) in 
    let key_s1 = (buffer64_read ctx_b 6 (va_get_mem va_s0)) in
    let key_r = (lowerUpper128_opaque key_r0 key_r1) in
    let key_s = (lowerUpper128_opaque key_s0 key_s1) in
    
    (validSrcAddrs64 (va_get_mem va_sM) ctx_in
    ctx_b 24) /\ (validSrcAddrs64 (va_get_mem va_sM) inp_in inp_b (readable_words len_in)) /\
    (modifies_buffer ctx_b (va_get_mem va_s0) (va_get_mem va_sM)) /\ (let h0_out = (buffer64_read
    ctx_b 0 (va_get_mem va_sM)) in let h1_out = (buffer64_read ctx_b 1 (va_get_mem va_sM)) in
    let h = (lowerUpper128_opaque h0_out h1_out) in (let inp_mem = (seqTo128 (buffer64_as_seq (va_get_mem
    va_sM) inp_b)) in h == (poly1305_hash key_r key_s inp_mem len_in) /\ (va_get_reg Rbx va_sM) ==
    (va_get_reg Rbx va_s0) /\ (va_get_reg Rbp va_sM) == (va_get_reg Rbp va_s0) /\ (va_get_reg Rdi
    va_sM) == (va_get_reg Rdi va_s0) /\ (va_get_reg Rsi va_sM) == (va_get_reg Rsi va_s0) /\
    (va_get_reg R12 va_sM) == (va_get_reg R12 va_s0) /\ (va_get_reg R13 va_sM) == (va_get_reg R13
    va_s0) /\ (va_get_reg R14 va_sM) == (va_get_reg R14 va_s0) /\ (va_get_reg R15 va_sM) ==
    (va_get_reg R15 va_s0)))) /\ (va_state_eq va_sM (va_update_mem va_sM (va_update_flags va_sM
    (va_update_reg Rbp va_sM (va_update_reg Rbx va_sM (va_update_reg R14 va_sM (va_update_reg R12
    va_sM (va_update_reg R11 va_sM (va_update_reg Rdx va_sM (va_update_reg Rsi va_sM (va_update_reg
    Rdi va_sM (va_update_reg R15 va_sM (va_update_reg R13 va_sM (va_update_reg R10 va_sM
    (va_update_reg R9 va_sM (va_update_reg R8 va_sM (va_update_reg Rcx va_sM (va_update_reg Rax
    va_sM (va_update_ok va_sM va_s0))))))))))))))))))))))

let va_lemma_poly va_b0 va_s0 ctx_b inp_b len =
  let key_r0 = buffer64_read ctx_b 3 (va_get_mem va_s0) in
  let key_r1 = (buffer64_read ctx_b 4 (va_get_mem va_s0)) in
  let key_s0 = (buffer64_read ctx_b 5 (va_get_mem va_s0)) in
  let key_s1 = (buffer64_read ctx_b 6 (va_get_mem va_s0)) in
  let key_r = lowerUpper128_opaque key_r0 key_r1 in
  let key_s = lowerUpper128_opaque key_s0 key_s1 in
  let va_sM, va_fM, _ = va_lemma_poly1305 va_b0 va_s0 false key_r key_s ctx_b inp_b in
  va_sM, va_fM
