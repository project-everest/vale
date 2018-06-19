module Vale_memcpy

open X64.Machine_s
open X64.Memory_i
open X64.Vale.State_i
open X64.Vale.Decls_i
open X64.Vale.InsBasic
open X64.Vale.InsMem
#set-options "--z3rlimit 20"

val va_code_memcpy : va_dummy:unit -> Tot va_code

val va_lemma_memcpy : va_b0:va_code -> va_s0:va_state -> src:buffer64 -> dest:buffer64
  -> Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires ((va_require_total va_b0 (va_code_memcpy ()) va_s0) /\ (va_get_ok va_s0) /\
    (locs_disjoint [(loc_buffer src); (loc_buffer dest)]) /\ (buffer_readable (va_get_mem va_s0)
    src) /\ (buffer_readable (va_get_mem va_s0) dest) /\ (va_get_reg Rdi va_s0) == (buffer_addr src
    (va_get_mem va_s0)) /\ (va_get_reg Rsi va_s0) == (buffer_addr dest (va_get_mem va_s0)) /\
    (buffer_length src) == 1 /\ (buffer_length dest) == 1))
  (ensures (fun (va_sM, va_fM) -> ((va_ensure_total va_b0 va_s0 va_sM va_fM) /\ (va_get_ok va_sM)
    /\ (locs_disjoint [(loc_buffer src); (loc_buffer dest)]) /\ (buffer_readable (va_get_mem va_sM)
    src) /\ (buffer_readable (va_get_mem va_sM) dest) /\ (va_get_reg Rdi va_sM) == (buffer_addr src
    (va_get_mem va_sM)) /\ (va_get_reg Rsi va_sM) == (buffer_addr dest (va_get_mem va_sM)) /\
    (buffer_length src) == 1 /\ (buffer_length dest) == 1 /\ (va_get_reg Rbx va_sM) == (va_get_reg
    Rbx va_s0) /\ (va_get_reg Rbp va_sM) == (va_get_reg Rbp va_s0) /\ (va_get_reg R12 va_sM) ==
    (va_get_reg R12 va_s0) /\ (va_get_reg R13 va_sM) == (va_get_reg R13 va_s0) /\ (va_get_reg R14
    va_sM) == (va_get_reg R14 va_s0) /\ (va_get_reg R15 va_sM) == (va_get_reg R15 va_s0) /\
    (modifies_mem (loc_buffer dest) (va_get_mem va_s0) (va_get_mem va_sM)) /\ (forall i . 0 <= i &&
    i < 1 ==> (buffer64_read dest i (va_get_mem va_sM)) == (buffer64_read src i (va_get_mem
    va_sM))) /\ (va_state_eq va_sM (va_update_mem va_sM (va_update_reg R15 va_sM (va_update_reg R14
    va_sM (va_update_reg R13 va_sM (va_update_reg R12 va_sM (va_update_reg R11 va_sM (va_update_reg
    R10 va_sM (va_update_reg R9 va_sM (va_update_reg R8 va_sM (va_update_reg Rsp va_sM
    (va_update_reg Rbp va_sM (va_update_reg Rdi va_sM (va_update_reg Rsi va_sM (va_update_reg Rdx
    va_sM (va_update_reg Rcx va_sM (va_update_reg Rbx va_sM (va_update_reg Rax va_sM (va_update_ok
    va_sM va_s0))))))))))))))))))))))
