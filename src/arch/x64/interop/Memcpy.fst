module Memcpy

open LowStar.Buffer
module B = LowStar.Buffer
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

open Vale_memcpy

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : ST unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (dst:B.buffer UInt8.t) (src:B.buffer UInt8.t) = live h dst /\ live h src /\ disjoint dst src /\ length dst % 8 == 0 /\ length src % 8 == 0 /\ length src == 8 /\ length dst == 1
let post_cond (h0:HS.mem) (h1:HS.mem) (dst:B.buffer UInt8.t) (src:B.buffer UInt8.t) = live h0 dst /\ live h0 src /\ live h1 dst /\ live h1 src /\ length dst % 8 == 0 /\ length src % 8 == 0 /\
  length src == 1 /\ length dst == 1 /\ Seq.equal (B.as_seq h1 src) (B.as_seq h1 dst)

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

val memcpy: dst:B.buffer UInt8.t -> src:B.buffer UInt8.t -> ST unit
	(requires (fun h -> pre_cond h dst src ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 dst src ))

val ghost_memcpy: dst:B.buffer UInt8.t -> src:B.buffer UInt8.t -> (h0:HS.mem{pre_cond h0 dst src }) -> GTot (h1:HS.mem{post_cond h0 h1 dst src })

#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
let ghost_memcpy dst src h0 =
  let buffers = dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let regs = fun r -> begin match r with
    | rdi -> addr_dst
    | rsi -> addr_src
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  let s1, f1 = va_lemma_memcpy (va_code_memcpy ()) s0 dst src  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs rbx == s1.regs rbx);
  assert(s0.regs rbp == s1.regs rbp);
  assert(s0.regs r12 == s1.regs r12);
  assert(s0.regs r13 == s1.regs r13);
  assert(s0.regs r14 == s1.regs r14);
  assert(s0.regs r15 == s1.regs r15);
  // Ensures that va_code_memcpy is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_memcpy ()) s0 s1 f1);
  s1.mem.hs

let memcpy dst src  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h dst src ) (ghost_memcpy dst src )
