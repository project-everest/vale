module Quad32_xor

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
#set-options "--z3rlimit 40"

open Vale_quad32_xor_buffer

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

let b8 = B.buffer UInt8.t

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map


//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (src1:b8) (src2:b8) (dst:b8) : Lemma
  (requires pre_cond h0 src1 src2 dst )
  (ensures (
(  let buffers = src1::src2::dst::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_src1 = addrs src1 in
  let addr_src2 = addrs src2 in
  let addr_dst = addrs dst in
  let regs = fun r -> begin match r with
    | rdi -> addr_src1
    | rsi -> addr_src2
    | rdx -> addr_dst
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  va_pre (va_code_quad32_xor_buffer ()) s0 src1 src2 dst ))) =
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (src1:b8) (src2:b8) (dst:b8)  : Lemma
  (requires pre_cond va_s0.mem.hs src1 src2 dst /\
    va_post (va_code_quad32_xor_buffer ()) va_s0 va_sM va_fM src1 src2 dst )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs src1 src2 dst ) =
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  let src1_128 = BV.mk_buffer_view src1 Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) src1) (BV.as_seq va_s0.mem.hs src1_128));
  BV.as_seq_sel va_s0.mem.hs src1_128 0;
  let src2_128 = BV.mk_buffer_view src2 Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) src2) (BV.as_seq va_s0.mem.hs src2_128));
  BV.as_seq_sel va_s0.mem.hs src2_128 0;
  let dst128 = BV.mk_buffer_view dst Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) dst) (BV.as_seq va_sM.mem.hs dst128));
  BV.as_seq_sel va_sM.mem.hs dst128 0;
  ()

val ghost_quad32_xor_buffer: src1:b8 -> src2:b8 -> dst:b8 -> (h0:HS.mem{pre_cond h0 src1 src2 dst }) -> GTot (h1:HS.mem{post_cond h0 h1 src1 src2 dst })

let ghost_quad32_xor_buffer src1 src2 dst h0 =
  let buffers = src1::src2::dst::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_src1 = addrs src1 in
  let addr_src2 = addrs src2 in
  let addr_dst = addrs dst in
  let regs = fun r -> begin match r with
    | rdi -> addr_src1
    | rsi -> addr_src2
    | rdx -> addr_dst
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  implies_pre h0 src1 src2 dst ;
  let s1, f1 = va_lemma_quad32_xor_buffer (va_code_quad32_xor_buffer ()) s0 src1 src2 dst  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs rbx == s1.regs rbx);
  assert(s0.regs rbp == s1.regs rbp);
  assert(s0.regs r12 == s1.regs r12);
  assert(s0.regs r13 == s1.regs r13);
  assert(s0.regs r14 == s1.regs r14);
  assert(s0.regs r15 == s1.regs r15);
  // Ensures that va_code_quad32_xor_buffer is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_quad32_xor_buffer ()) s0 s1 f1);
  implies_post s0 s1 f1 src1 src2 dst ;
  s1.mem.hs

let quad32_xor_buffer src1 src2 dst  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h src1 src2 dst ) (ghost_quad32_xor_buffer src1 src2 dst )
