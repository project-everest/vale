module Memcpy

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

open Vale_memcpy

#set-options "--initial_fuel 5 --max_fuel 5 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let win_implies_pre (h0:HS.mem) (dst:s8) (src:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src])
  (ensures (
B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = stack_b::dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_dst
    | Rdx -> addr_src
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  va_pre (va_code_memcpy true) s0 true stack_b dst src ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  assert(B.disjoint stack_b dst);
  assert(B.disjoint stack_b src);
  ()

let win_implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (dst:s8) (src:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs dst src /\ B.length stack_b == 24 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [dst;src]/\
    va_post (va_code_memcpy true) va_s0 va_sM va_fM true stack_b dst src )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs dst src ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  ()

val win_ghost_memcpy: dst:s8 -> src:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) -> GTot (h1:HS.mem{post_cond h0 h1 dst src })

let win_ghost_memcpy dst src stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = stack_b::dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_dst
    | Rdx -> addr_src
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  win_implies_pre h0 dst src stack_b ;
  let s1, f1 = va_lemma_memcpy (va_code_memcpy true) s0 true stack_b dst src  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs Rdi == s1.regs Rdi);
  assert(s0.regs Rsi == s1.regs Rsi);
  assert(s0.regs Rsp == s1.regs Rsp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
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
  // Ensures that va_code_memcpy is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_memcpy true) s0 s1 f1);
  win_implies_post s0 s1 f1 dst src stack_b ;
  s1.mem.hs

// TODO: Prove these two lemmas if they are not proven automatically
let lin_implies_pre (h0:HS.mem) (dst:s8) (src:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src])
  (ensures (
B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = stack_b::dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  va_pre (va_code_memcpy false) s0 false stack_b dst src ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  assert(B.disjoint stack_b dst);
  assert(B.disjoint stack_b src);
  ()

let lin_implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (dst:s8) (src:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs dst src /\ B.length stack_b == 24 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [dst;src]/\
    va_post (va_code_memcpy false) va_s0 va_sM va_fM false stack_b dst src )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs dst src ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  ()

val lin_ghost_memcpy: dst:s8 -> src:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) -> GTot (h1:HS.mem{post_cond h0 h1 dst src })

let lin_ghost_memcpy dst src stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = stack_b::dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  lin_implies_pre h0 dst src stack_b ;
  let s1, f1 = va_lemma_memcpy (va_code_memcpy false) s0 false stack_b dst src  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_memcpy is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_memcpy false) s0 s1 f1);
  lin_implies_post s0 s1 f1 dst src stack_b ;
  s1.mem.hs

let ghost_memcpy dst src stack_b h0 =
  if win then win_ghost_memcpy dst src stack_b h0
  else lin_ghost_memcpy dst src stack_b h0

let memcpy dst src  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
  st_put (fun h -> pre_cond h dst src /\ B.length stack_b == 24 /\ live h stack_b /\ buf_disjoint_from stack_b [dst;src]) (ghost_memcpy dst src stack_b);
  pop_frame()
