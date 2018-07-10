module Memcpy_s

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

open Vale_memcpy

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

let b8 = B.buffer UInt8.t

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
let pre_cond (h:HS.mem) (dst:b8) (src:b8) = live h dst /\ live h src /\ locs_disjoint [dst;src] /\ length dst % 8 == 0 /\ length src % 8 == 0 /\ B.length src == 16 /\ B.length dst == 16
let post_cond (h0:HS.mem) (h1:HS.mem) (dst:b8) (src:b8) = live h0 dst /\ live h0 src /\ live h1 dst /\ live h1 src /\ length dst % 8 == 0 /\ length src % 8 == 0

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 5 --max_fuel 5 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (dst:b8) (src:b8) : Lemma
  (requires pre_cond h0 dst src )
  (ensures (
(  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let regs = fun r -> begin match r with
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace = []; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  va_pre (va_code_memcpy ()) s0 dst src ))) =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let regs = fun r -> begin match r with
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace = []; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;  
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (dst:b8) (src:b8)  : Lemma
  (requires pre_cond va_s0.mem.hs dst src /\
    va_post (va_code_memcpy ()) va_s0 va_sM va_fM dst src )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs dst src ) =
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  ()

val memcpy: dst:b8 -> src:b8 -> Stack unit
	(requires (fun h -> pre_cond h dst src ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 dst src ))

val ghost_memcpy: dst:b8 -> src:b8 -> (h0:HS.mem{pre_cond h0 dst src }) -> GTot (h1:HS.mem{post_cond h0 h1 dst src })

let ghost_memcpy dst src h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let regs = fun r -> begin match r with
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace = []; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  implies_pre h0 dst src ;
  let s1, f1 = va_lemma_memcpy (va_code_memcpy ()) s0 dst src  in
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
  implies_post s0 s1 f1 dst src ;
  s1.mem.hs

let memcpy dst src  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h dst src ) (ghost_memcpy dst src )
