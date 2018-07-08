module Zero_quad32

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

open Vale_zero_quad32_buffer

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

let buffer_to_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (b:b8) =    B.live h b /\
    B.length b == 16

let post_cond (h:HS.mem) (h':HS.mem) (b:b8) = length b == 16 /\
    M.modifies (M.loc_buffer b) h h' /\
    (let new_b = buffer_to_quad32 b h' in
     new_b == Mkfour 0 0 0 0)


//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (b:b8) : Lemma
  (requires pre_cond h0 b )
  (ensures (
(  let buffers = b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_b = addrs b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) b;
  va_pre (va_code_zero_quad32_buffer ()) s0 b ))) =
  length_t_eq (TBase TUInt128) b;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (b:b8)  : Lemma
  (requires pre_cond va_s0.mem.hs b /\
    va_post (va_code_zero_quad32_buffer ()) va_s0 va_sM va_fM b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs b ) =
  length_t_eq (TBase TUInt128) b;
  let b128 = BV.mk_buffer_view b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) b) (BV.as_seq va_sM.mem.hs b128));
  BV.as_seq_sel va_sM.mem.hs b128 0;
  ()

val zero_quad32_buffer: b:b8 -> Stack unit
	(requires (fun h -> pre_cond h b ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 b ))

val ghost_zero_quad32_buffer: b:b8 -> (h0:HS.mem{pre_cond h0 b }) -> GTot (h1:HS.mem{post_cond h0 h1 b })

let ghost_zero_quad32_buffer b h0 =
  let buffers = b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_b = addrs b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) b;
  implies_pre h0 b ;
  let s1, f1 = va_lemma_zero_quad32_buffer (va_code_zero_quad32_buffer ()) s0 b  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_zero_quad32_buffer is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_zero_quad32_buffer ()) s0 s1 f1);
  implies_post s0 s1 f1 b ;
  s1.mem.hs

let zero_quad32_buffer b  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h b ) (ghost_zero_quad32_buffer b )
