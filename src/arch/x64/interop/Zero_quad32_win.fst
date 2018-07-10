module Zero_quad32_win

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
open BufferViewHelpers
#set-options "--z3rlimit 40"

open Vale_zero_quad32_buffer_win

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32


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



#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (b:b8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 b /\ B.length stack_b == 16 /\ live h0 stack_b /\ locs_disjoint [stack_b;b])
  (ensures (
B.length stack_b == 16 /\ live h0 stack_b /\ locs_disjoint [stack_b;b] /\ (  let buffers = stack_b::b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_b = addrs b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) b;
  length_t_eq (TBase TUInt64) stack_b;
  va_pre (va_code_zero_quad32_buffer_win ()) s0 stack_b b ))) =
  length_t_eq (TBase TUInt128) b;
  length_t_eq (TBase TUInt64) stack_b;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (b:b8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs b /\ B.length stack_b == 16 /\ live va_s0.mem.hs stack_b /\ locs_disjoint [stack_b;b] /\
    va_post (va_code_zero_quad32_buffer_win ()) va_s0 va_sM va_fM stack_b b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs b ) =
  length_t_eq (TBase TUInt128) b;
  length_t_eq (TBase TUInt64) stack_b;
  let b128 = BV.mk_buffer_view b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) b) (BV.as_seq va_sM.mem.hs b128));
  BV.as_seq_sel va_sM.mem.hs b128 0;  
  ()

val ghost_zero_quad32_buffer: b:b8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 b /\ B.length stack_b == 16 /\ live h0 stack_b /\ locs_disjoint [stack_b;b]}) -> GTot (h1:HS.mem{post_cond h0 h1 b })

let ghost_zero_quad32_buffer b stack_b h0 =
  let buffers = stack_b::b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_b = addrs b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) b;
  length_t_eq (TBase TUInt64) stack_b;
  implies_pre h0 b stack_b ;
  let s1, f1 = va_lemma_zero_quad32_buffer_win (va_code_zero_quad32_buffer_win ()) s0 stack_b b  in
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
  // Ensures that va_code_zero_quad32_buffer is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_zero_quad32_buffer_win ()) s0 s1 f1);
  implies_post s0 s1 f1 b stack_b ;
  s1.mem.hs

let zero_quad32_buffer b  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 16) in
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h b /\ B.length stack_b == 16 /\ live h stack_b /\ locs_disjoint [stack_b;b]) (ghost_zero_quad32_buffer b stack_b);
  pop_frame()
