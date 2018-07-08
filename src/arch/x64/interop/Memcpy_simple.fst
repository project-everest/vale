module Memcpy_simple

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

open Vale_memcpy_simple

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

let b8 = B.buffer UInt8.t

open FStar.Mul

let same_underlying_buffers (b1 b2:B.buffer UInt8.t) (len:nat) (h:HS.mem) : Lemma
  (requires B.length b1 == B.length b2 /\ B.length b1 == len * 8 /\ len % 8 == 0 /\ B.live h b1 /\ B.live h b2 /\ (
  let b128_1 = (BV.mk_buffer_view b1 Views.view64) in
  let b128_2 = (BV.mk_buffer_view b2 Views.view64) in
  Seq.equal (BV.as_seq h b128_1) (BV.as_seq h b128_2)))
  (ensures B.as_seq h b1 == B.as_seq h b2) = admit()

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

let rec loc_locs_disjoint_rec (l:b8) (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let locs_disjoint (ls:list b8) : Type0 = normalize (locs_disjoint_rec ls)

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (dst:b8) (src:b8) (len:nat64) = live h dst /\ live h src /\ locs_disjoint [dst;src] /\ length dst % 8 == 0 /\ length src % 8 == 0
  /\ B.length src == len * 8 /\ B.length dst == len * 8


let post_cond (h:HS.mem) (h':HS.mem) (dst:b8) (src:b8) (len:nat64) = length dst % 8 == 0 /\ length src % 8 == 0 /\ B.length src == len /\ B.length dst == len /\
    B.live h' dst /\ B.live h' src /\
    M.modifies (M.loc_buffer dst) h h' /\
    B.as_seq h' dst == B.as_seq h src


//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 5 --max_fuel 5 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (dst:b8) (src:b8) (len:nat64) : Lemma
  (requires pre_cond h0 dst src len )
  (ensures (
(  let buffers = dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let regs = fun r -> begin match r with
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | Rdx -> len
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  va_pre (va_code_memcpy_simple ()) s0 dst src len ))) =
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (dst:b8) (src:b8) (len:nat64)  : Lemma
  (requires pre_cond va_s0.mem.hs dst src len /\
    va_post (va_code_memcpy_simple ()) va_s0 va_sM va_fM dst src len )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs dst src len ) =
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  let dst64 = BV.mk_buffer_view dst Views.view64 in
  let src64 = BV.mk_buffer_view src Views.view64 in
  assert (Seq.equal
    (buffer64_as_seq (va_get_mem va_sM) dst)
    (BV.as_seq va_sM.mem.hs dst64));
  assert (Seq.equal
    (buffer64_as_seq (va_get_mem va_sM) src)
    (BV.as_seq va_sM.mem.hs src64));
  same_underlying_buffers dst src len va_sM.mem.hs;
  ()

val memcpy_simple: dst:b8 -> src:b8 -> len:nat64 -> Stack unit
	(requires (fun h -> pre_cond h dst src len ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 dst src len ))

val ghost_memcpy_simple: dst:b8 -> src:b8 -> len:nat64 -> (h0:HS.mem{pre_cond h0 dst src len }) -> GTot (h1:HS.mem{post_cond h0 h1 dst src len })

let ghost_memcpy_simple dst src len h0 =
  let buffers = dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let regs = fun r -> begin match r with
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | Rdx -> len
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  implies_pre h0 dst src len ;
  let s1, f1 = va_lemma_memcpy_simple (va_code_memcpy_simple ()) s0 dst src len  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_memcpy_simple is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_memcpy_simple ()) s0 s1 f1);
  implies_post s0 s1 f1 dst src len ;
  s1.mem.hs

let memcpy_simple dst src len  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h dst src len ) (ghost_memcpy_simple dst src len )
