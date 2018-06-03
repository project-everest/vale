module Poly

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
open Poly1305.Spec_s
open X64.Poly1305.Math_i
open X64.Poly1305.Util_i
open X64.Poly1305
#set-options "--z3rlimit 40"

open Vale_poly

assume val st_put (h:HS.mem) (f:HS.mem -> GTot HS.mem) : ST unit (fun h0 -> True) (fun h0 _ h1 -> h == h1 /\ f h0 == h)

let readable_words (len:nat) =
    ((len + 15) / 16) `op_Multiply` 2 // 2 == 16 for rounding /8 for 8-byte words

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

let seq_uint_to_nat (s:Seq.seq UInt64.t) =
  let len = Seq.length s in
  let contents (i:nat{i < len}) : nat64 = UInt64.v (Seq.index s i) in
  Seq.init len contents
  

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (ctx:B.buffer UInt64.t) (inp:B.buffer UInt64.t) (len:nat64) = live #UInt64.t h ctx /\ live #UInt64.t h inp /\ disjoint ctx inp /\ length inp == readable_words len /\ length ctx == 24 /\ addrs.[(as_addr inp, idx inp, length inp)] + len < pow2_64
let post_cond (h0:HS.mem) (h1:HS.mem) (ctx:B.buffer UInt64.t) (inp:B.buffer UInt64.t) (len:nat64) = live #UInt64.t h0 ctx /\ live #UInt64.t h0 inp /\ live #UInt64.t h1 ctx /\ live #UInt64.t h1 inp /\
length ctx == 24 /\ length inp == readable_words len /\
(let h0_out = UInt64.v (Seq.index (as_seq h1 ctx) 0) in
 let h1_out = UInt64.v (Seq.index (as_seq h1 ctx) 1) in
 let h = lowerUpper128_opaque h0_out h1_out in
 let key_r0 = UInt64.v (Seq.index (as_seq h0 ctx) 3) in 
 let key_r1 = UInt64.v (Seq.index (as_seq h0 ctx) 4) in
 let key_s0 = UInt64.v (Seq.index (as_seq h0 ctx) 5) in 
 let key_s1 = UInt64.v (Seq.index (as_seq h0 ctx) 6) in
 let key_r = (lowerUpper128_opaque key_r0 key_r1) in
 let key_s = (lowerUpper128_opaque key_s0 key_s1) in
 let inp_mem = seqTo128 (seq_uint_to_nat (as_seq h1 inp)) in
 h == poly1305_hash key_r key_s inp_mem len)
 

val poly: ctx:B.buffer UInt64.t -> inp:B.buffer UInt64.t -> len:nat64 -> STL unit
	(requires (fun h -> pre_cond h ctx inp len ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 ctx inp len ))

val ghost_poly: ctx:B.buffer UInt64.t -> inp:B.buffer UInt64.t -> len:nat64 -> (h0:HS.mem{pre_cond h0 ctx inp len }) -> GTot (h1:HS.mem{post_cond h0 h1 ctx inp len })

#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
let ghost_poly ctx inp len h0 =
  let buffers = ctx::inp::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let n:nat64 = 0 in
  let addr_ctx = addrs.[(as_addr ctx, idx ctx, length ctx)] in
  let addr_inp = addrs.[(as_addr inp, idx inp, length inp)] in
  let regs = fun r -> begin match r with
    | Rdi -> addr_ctx
    | Rsi -> addr_inp
    | Rdx -> len
    | _ -> n end in
  let n:nat32 = 0 in
  let xmms = fun x -> Mkfour n n n n in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  let s1, f1 = va_lemma_poly (va_code_poly ()) s0 ctx inp len  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_poly is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_poly ()) s0 s1 f1);
  // This assertion was manually added
  assert (FStar.FunctionalExtensionality.feq 
    (seqTo128 (buffer64_as_seq s1.mem inp)) 
    (seqTo128 (seq_uint_to_nat (as_seq s1.mem.hs inp))));
  s1.mem.hs

let poly ctx inp len  =
  let h0 = get() in
  st_put h0 (fun h -> if FStar.StrongExcludedMiddle.strong_excluded_middle (pre_cond h ctx inp len ) then ghost_poly ctx inp len h else h)
