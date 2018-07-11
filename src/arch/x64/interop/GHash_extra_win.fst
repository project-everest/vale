module GHash_extra_win

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module S8 = SecretByte
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open BufferViewHelpers
open Interop_assumptions
#set-options "--z3rlimit 40"

open Vale_ghash_incremental_extra_stdcall_win

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
let implies_pre (h0:HS.mem) (in_b:s8) (hash_b:s8) (h_b:s8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32))  (stack_b:b8) : Lemma
  (requires pre_cond h0 in_b hash_b h_b num_bytes orig_hash /\ B.length stack_b == 72 /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b])
  (ensures (
B.length stack_b == 72 /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == hash_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == h_b) then Secret else
    Public in
  let buffers = stack_b::in_b::hash_b::h_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_in_b = addrs in_b in
  let addr_hash_b = addrs hash_b in
  let addr_h_b = addrs h_b in
  let addr_stack:nat64 = addrs stack_b + 32 in
  let regs = fun r -> begin match r with
    | rsp -> addr_stack
    | rcx -> addr_in_b
    | rdx -> addr_hash_b
    | r8 -> addr_h_b
    | r9 -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace = []; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  va_pre (va_code_ghash_incremental_extra_stdcall_win ()) s0 stack_b in_b hash_b h_b num_bytes (Ghost.reveal orig_hash) ))) =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == hash_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == h_b) then Secret else
    Public in
  let buffers = stack_b::in_b::hash_b::h_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_in_b = addrs in_b in
  let addr_hash_b = addrs hash_b in
  let addr_h_b = addrs h_b in
  let addr_stack:nat64 = addrs stack_b + 32 in
  let regs = fun r -> begin match r with
    | rsp -> addr_stack
    | rcx -> addr_in_b
    | rdx -> addr_hash_b
    | r8 -> addr_h_b
    | r9 -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace = []; memTaint = create_valid_memtaint mem buffers taint_func} in  
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  assert (Seq.equal (buffer_to_seq_quad32 in_b h0) (buffer128_as_seq (va_get_mem s0) in_b));
  let h128_b = BV.mk_buffer_view h_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem s0) h_b) (BV.as_seq h0 h128_b));
  BV.as_seq_sel h0 h128_b 0;  
  let hash128_b = BV.mk_buffer_view hash_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem s0) hash_b) (BV.as_seq h0 hash128_b));
  BV.as_seq_sel h0 hash128_b 0;   
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (in_b:s8) (hash_b:s8) (h_b:s8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32))  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs in_b hash_b h_b num_bytes orig_hash /\ B.length stack_b == 72 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b]/\
    va_post (va_code_ghash_incremental_extra_stdcall_win ()) va_s0 va_sM va_fM stack_b in_b hash_b h_b num_bytes (Ghost.reveal orig_hash) )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs in_b hash_b h_b num_bytes orig_hash ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  assert (Seq.equal (buffer_to_seq_quad32 in_b va_sM.mem.hs) (buffer128_as_seq (va_get_mem va_sM) in_b));
  let hash128_b = BV.mk_buffer_view hash_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) hash_b) (BV.as_seq va_s0.mem.hs hash128_b));
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) hash_b) (BV.as_seq va_sM.mem.hs hash128_b));
  BV.as_seq_sel va_s0.mem.hs hash128_b 0;
  BV.as_seq_sel va_sM.mem.hs hash128_b 0;
  let h128_b = BV.mk_buffer_view h_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) h_b) (BV.as_seq va_s0.mem.hs h128_b));
  BV.as_seq_sel va_s0.mem.hs h128_b 0;   
  ()

val ghost_ghash_incremental_extra_stdcall_win: in_b:s8 -> hash_b:s8 -> h_b:s8 -> num_bytes:nat64 -> orig_hash:Ghost.erased (quad32) ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 in_b hash_b h_b num_bytes orig_hash /\ B.length stack_b == 72 /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b]}) -> GTot (h1:HS.mem{post_cond h0 h1 in_b hash_b h_b num_bytes orig_hash /\ M.modifies (M.loc_union (M.loc_buffer hash_b) (M.loc_buffer stack_b)) h0 h1 })

let ghost_ghash_incremental_extra_stdcall_win in_b hash_b h_b num_bytes orig_hash stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == hash_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == h_b) then Secret else
    Public in
  let buffers = stack_b::in_b::hash_b::h_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_in_b = addrs in_b in
  let addr_hash_b = addrs hash_b in
  let addr_h_b = addrs h_b in
  let addr_stack:nat64 = addrs stack_b + 32 in
  let regs = fun r -> begin match r with
    | rsp -> addr_stack
    | rcx -> addr_in_b
    | rdx -> addr_hash_b
    | r8 -> addr_h_b
    | r9 -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace = []; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  implies_pre h0 in_b hash_b h_b num_bytes orig_hash stack_b ;
  let s1, f1 = va_lemma_ghash_incremental_extra_stdcall_win (va_code_ghash_incremental_extra_stdcall_win ()) s0 stack_b in_b hash_b h_b num_bytes (Ghost.reveal orig_hash)  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs rbx == s1.regs rbx);
  assert(s0.regs rbp == s1.regs rbp);
  assert(s0.regs rdi == s1.regs rdi);
  assert(s0.regs rsi == s1.regs rsi);
  assert(s0.regs rsp == s1.regs rsp);
  assert(s0.regs r12 == s1.regs r12);
  assert(s0.regs r13 == s1.regs r13);
  assert(s0.regs r14 == s1.regs r14);
  assert(s0.regs r15 == s1.regs r15);
  assert(s0.xmms 6 == s1.xmms 6);
  assert(s0.xmms 7 == s1.xmms 7);
  assert(s0.xmms 8 == s1.xmms 8);
  assert(s0.xmms 9 == s1.xmms 9);
  assert(s0.xmms 10 == s1.xmms 10);
  assert(s0.xmms 11 == s1.xmms 11);
  assert(s0.xmms 12 == s1.xmms 12);
  assert(s0.xmms 13 == s1.xmms 13);
  assert(s0.xmms 14 == s1.xmms 14);
  assert(s0.xmms 15 == s1.xmms 15);
  // Ensures that va_code_ghash_incremental_extra_stdcall_win is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_ghash_incremental_extra_stdcall_win ()) s0 s1 f1);
  implies_post s0 s1 f1 in_b hash_b h_b num_bytes orig_hash stack_b ;
  s1.mem.hs

let ghash_incremental_extra_stdcall_win in_b hash_b h_b num_bytes orig_hash  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 72) in
  st_put (fun h -> pre_cond h in_b hash_b h_b (UInt64.v num_bytes) orig_hash /\ B.length stack_b == 72 /\ live h stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b]) (ghost_ghash_incremental_extra_stdcall_win in_b hash_b h_b (UInt64.v num_bytes) orig_hash stack_b);
  pop_frame()
