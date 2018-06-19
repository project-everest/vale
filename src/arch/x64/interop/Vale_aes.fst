module Vale_aes

open Types_s
open Types_i
open FStar.Seq
open X64.Machine_s
open X64.Memory_i
open X64.Vale.State_i
open X64.Vale.Decls_i
open AES_s
open AES_helpers_i
open X64.AES


let va_code_aes = fun () -> va_code_KeyExpansionStdcall false

val va_lemma_aes: va_b0:va_code -> va_s0:va_state ->
  input_key_b:buffer128 -> output_key_expansion_b:buffer128 ->
  Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires ((va_require_total va_b0 (va_code_KeyExpansionStdcall false) va_s0) /\ (va_get_ok va_s0)
    /\ (let key_ptr = ((va_get_reg Rdi va_s0)) in let
    key_expansion_ptr = ((va_get_reg Rsi va_s0)) in let key
    = (quad32_to_seq (buffer128_read input_key_b 0 (va_get_mem va_s0))) in (buffers_disjoint128
    input_key_b output_key_expansion_b) /\ (validSrcAddrs128 (va_get_mem va_s0) key_ptr input_key_b
    1) /\ (validDstAddrs128 (va_get_mem va_s0) key_expansion_ptr output_key_expansion_b 11))))
  (ensures (fun (va_sM, va_fM) -> ((va_ensure_total va_b0 va_s0 va_sM va_fM) /\ (va_get_ok va_sM)
    /\ (let key_ptr = ((va_get_reg Rdi va_s0)) in let
    key_expansion_ptr = ((va_get_reg Rsi va_s0)) in let key
    = (quad32_to_seq (buffer128_read input_key_b 0 (va_get_mem va_s0))) in (buffers_disjoint128
    input_key_b output_key_expansion_b) /\ (validSrcAddrs128 (va_get_mem va_sM) key_ptr input_key_b
    1) /\ (validDstAddrs128 (va_get_mem va_sM) key_expansion_ptr output_key_expansion_b 11)) /\
    (let key_ptr = ((va_get_reg Rdi va_s0)) in let
    key_expansion_ptr = ((va_get_reg Rsi va_s0)) in let key
    = (quad32_to_seq (buffer128_read input_key_b 0 (va_get_mem va_s0))) in (modifies_buffer128
    output_key_expansion_b (va_get_mem va_s0) (va_get_mem va_sM)) /\ (forall j .
    {:pattern(buffer128_read output_key_expansion_b j (va_get_mem va_sM))}(0 <= j && j <= 10) ==>
    (buffer128_read output_key_expansion_b j (va_get_mem va_sM)) == (index (key_to_round_keys_LE
    AES_128 key) j))) /\ (va_state_eq va_sM (va_update_flags va_sM (va_update_xmm 3 va_sM
    (va_update_xmm 2 va_sM (va_update_xmm 1 va_sM (va_update_mem va_sM (va_update_reg Rdx va_sM
    (va_update_ok va_sM va_s0)))))))))))

#set-options "--z3rlimit 20"

let va_lemma_aes va_b0 va_s0 input_key output_key =
  va_lemma_KeyExpansionStdcall va_b0 va_s0 false input_key output_key

