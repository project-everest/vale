module Memcpy

open FStar.Buffer
module B = FStar.Buffer
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop64
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
#set-options "--z3rlimit 40"

open Vale_memcpy

assume val st_put (h:HS.mem) (f:HS.mem -> GTot HS.mem) : ST unit (fun h0 -> True) (fun h0 _ h1 -> h == h1 /\ f h0 == h)

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (src:B.buffer UInt64.t) (dest:B.buffer UInt64.t) = live #UInt64.t h src /\ live #UInt64.t h dest /\ disjoint src dest
  /\ length src == 1 /\ length dest == 1
let post_cond (h0:HS.mem) (h1:HS.mem) (src:B.buffer UInt64.t) (dest:B.buffer UInt64.t) = live #UInt64.t h0 src /\ live #UInt64.t h0 dest /\ live #UInt64.t h1 src /\ live #UInt64.t h1 dest
  /\ length src == 1 /\ length dest == 1 /\ Seq.equal (as_seq h1 src) (as_seq h1 dest)

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

val memcpy: src:B.buffer UInt64.t -> dest:B.buffer UInt64.t -> STL unit
	(requires (fun h -> pre_cond h src dest ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 src dest ))

val ghost_memcpy: src:B.buffer UInt64.t -> dest:B.buffer UInt64.t -> (h0:HS.mem{pre_cond h0 src dest }) -> GTot (h1:HS.mem{post_cond h0 h1 src dest })

#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
let ghost_memcpy src dest h0 =
  let buffers = src::dest::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let n:nat64 = 0 in
  let addr_src = addrs.[(as_addr src, idx src, length src)] in
  let addr_dest = addrs.[(as_addr dest, idx dest, length dest)] in
  let regs = fun r -> begin match r with
    | Rdi -> addr_src
    | Rsi -> addr_dest
    | _ -> n end in
  let n:nat32 = 0 in
  let xmms = fun x -> Mkfour n n n n in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  let s1, f1 = va_lemma_memcpy (va_code_memcpy ()) s0 src dest  in
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
  assert (va_ensure_total (va_code_memcpy ()) s0 s1 f1);
  s1.mem.hs

let memcpy src dest  =
  let h0 = get() in
  st_put h0 (fun h -> if FStar.StrongExcludedMiddle.strong_excluded_middle (pre_cond h src dest ) then ghost_memcpy src dest h else h)
