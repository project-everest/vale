module Poly

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open Poly1305.Spec_s
open X64.Poly1305.Math_i
open X64.Poly1305.Util_i
open X64.Poly1305
#set-options "--z3rlimit 40"

open Vale_poly

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : ST unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

let readable_words (len:nat) =
((len + 15) / 16) `op_Multiply` 2 // 2 == 16 for rounding /8 for 8-byte words


let seq_uint_to_nat (s:Seq.seq UInt64.t) =
  let len = Seq.length s in
  let contents (i:nat{i < len}) : nat64 = UInt64.v (Seq.index s i) in
  Seq.init len contents

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (ctx:B.buffer UInt8.t) (inp:B.buffer UInt8.t) (len:nat64) = live h ctx /\ live h inp /\ disjoint ctx inp /\ length ctx % 8 == 0 /\ length inp % 8 == 0 /\ length inp == (readable_words len) `op_Multiply` 8  /\ length ctx == 192 /\ addrs inp + len < pow2_64
let post_cond (h0:HS.mem) (h1:HS.mem) (ctx:B.buffer UInt8.t) (inp:B.buffer UInt8.t) (len:nat64) = live h0 ctx /\ live h0 inp /\ live h1 ctx /\ live h1 inp /\ length ctx % 8 == 0 /\ length inp % 8 == 0
/\ length ctx == 192 /\ length inp == (readable_words len) `op_Multiply` 8 /\
  (let ctx_b = BV.mk_buffer_view ctx Views.view64 in
 let inp_b = BV.mk_buffer_view inp Views.view64 in
 length_t_eq (TBase TUInt64) ctx;
 length_t_eq (TBase TUInt64) ctx;
 let h0_out = UInt64.v (Seq.index (BV.as_seq h1 ctx_b) 0) in
 let h1_out = UInt64.v (Seq.index (BV.as_seq h1 ctx_b) 1) in
 let h = lowerUpper128_opaque h0_out h1_out in
 let key_r0 = UInt64.v (Seq.index (BV.as_seq h0 ctx_b) 3) in 
 let key_r1 = UInt64.v (Seq.index (BV.as_seq h0 ctx_b) 4) in
 let key_s0 = UInt64.v (Seq.index (BV.as_seq h0 ctx_b) 5) in 
 let key_s1 = UInt64.v (Seq.index (BV.as_seq h0 ctx_b) 6) in
 let key_r = (lowerUpper128_opaque key_r0 key_r1) in
 let key_s = (lowerUpper128_opaque key_s0 key_s1) in
 let inp_mem = seqTo128 (seq_uint_to_nat (BV.as_seq h1 inp_b)) in
 h == poly1305_hash key_r key_s inp_mem len)
  

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

val poly: ctx:B.buffer UInt8.t -> inp:B.buffer UInt8.t -> len:nat64 -> ST unit
	(requires (fun h -> pre_cond h ctx inp len ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 ctx inp len ))

val ghost_poly: ctx:B.buffer UInt8.t -> inp:B.buffer UInt8.t -> len:nat64 -> (h0:HS.mem{pre_cond h0 ctx inp len }) -> GTot (h1:HS.mem{post_cond h0 h1 ctx inp len })

#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
let ghost_poly ctx inp len h0 =
  let buffers = ctx::inp::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_ctx = addrs ctx in
  let addr_inp = addrs inp in
  let regs = fun r -> begin match r with
    | rdi -> addr_ctx
    | rsi -> addr_inp
    | rdx -> len
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let taint_t b = if StrongExcludedMiddle.strong_excluded_middle (b == ctx) then(fun (i:nat) -> if i < B.length ctx then Public else Public) else
      if StrongExcludedMiddle.strong_excluded_middle (b==inp) then (fun (i:nat) -> if i < B.length inp then Public else Public) else default_of_taint in
  let memTaint = {buffs = buffers; t = taint_t} in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace=[]; memTaint = memTaint} in
  length_t_eq (TBase TUInt64) ctx;
  length_t_eq (TBase TUInt64) inp;
  let s1, f1 = va_lemma_poly (va_code_poly ()) s0 ctx inp len  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs rbx == s1.regs rbx);
  assert(s0.regs rbp == s1.regs rbp);
  assert(s0.regs r12 == s1.regs r12);
  assert(s0.regs r13 == s1.regs r13);
  assert(s0.regs r14 == s1.regs r14);
  assert(s0.regs r15 == s1.regs r15);
  // Ensures that the output taint is correct
  assert (valid_taint_buf64 ctx s1.memTaint Public);
  assert (valid_taint_buf64 inp s1.memTaint Public);
  // Ensures that va_code_poly is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_poly ()) s0 s1 f1);
  // This assertion was manually added
  assert (FStar.FunctionalExtensionality.feq 
    (seqTo128 (buffer64_as_seq s1.mem inp)) 
    (seqTo128 (seq_uint_to_nat (BV.as_seq s1.mem.hs (BV.mk_buffer_view inp Views.view64)))));   
  s1.mem.hs

let poly ctx inp len  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h ctx inp len ) (ghost_poly ctx inp len )
