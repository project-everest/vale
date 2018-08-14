module Memcpy

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
open Interop_assumptions
open X64.Vale.StateLemmas_i
open X64.Vale.Lemmas_i
module TS = X64.Taint_Semantics_s
module ME = X64.Memory_i_s
module BS = X64.Bytes_Semantics_s
#set-options "--z3rlimit 60"

open Vale_memcpy

#set-options "--initial_fuel 5 --max_fuel 5 --initial_ifuel 2 --max_ifuel 2"
let create_initial_trusted_state is_win dst src stack_b (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) : GTot TS.traceState =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = stack_b::dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_dst
    | Rdx -> addr_src
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end)
  in let xmms = init_xmms in
  let (s_b:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  let s0:X64.Memory_i_s.state = {ME.state = s_b; ME.mem = mem} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

let create_initial_vale_state is_win dst src stack_b (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) : GTot va_state =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = stack_b::dst::src::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_dst
    | Rdx -> addr_src
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end)
  in let xmms = init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win dst src stack_b (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) : Lemma
  (state_of_S (create_initial_trusted_state is_win dst src stack_b h0) == create_initial_vale_state is_win dst src stack_b h0) =
    let s_init = create_initial_trusted_state is_win dst src stack_b h0 in
    let s0 = state_of_S s_init in
    let s1 = create_initial_vale_state is_win dst src stack_b h0 in
    assert (FunctionalExtensionality.feq s1.regs (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq s1.xmms (xmms' s_init.TS.state));
    lemma_of_ok s_init;
    lemma_of_regs s_init;
    lemma_of_flags s_init;
    lemma_of_xmms s_init;
    lemma_of_mem s_init;
    lemma_of_memTaint s_init;
    ()

// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (is_win:bool) (h0:HS.mem) (dst:s8) (src:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src])
  (ensures (
B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src] /\ (
  let s0 = create_initial_vale_state is_win dst src stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  va_pre (va_code_memcpy is_win) s0 is_win stack_b dst src ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  assert(Interop.disjoint stack_b dst);
  assert(Interop.disjoint stack_b src);
  ()

let seq_nat64_to_seq_U64 (b:Seq.seq nat64) : (Seq.seq UInt64.t) =
Seq.init (Seq.length b) (fun (i:nat { i < Seq.length b }) -> UInt64.uint_to_t (Seq.index b i))

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (dst:s8) (src:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs dst src /\ B.length stack_b == 24 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [dst;src]/\
    va_post (va_code_memcpy is_win) va_s0 va_sM va_fM is_win stack_b dst src )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs dst src ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  let dst_b = BV.mk_buffer_view dst Views.view64 in
  let src_b = BV.mk_buffer_view src Views.view64 in
  let t = TBase TUInt64 in
  assert (Seq.equal (seq_nat64_to_seq_U64 (buffer_as_seq #t (va_get_mem va_sM) src)) (BV.as_seq va_sM.mem.hs src_b));  
  assert (Seq.equal (seq_nat64_to_seq_U64 (buffer_as_seq #t (va_get_mem va_sM) dst)) (BV.as_seq va_sM.mem.hs dst_b));    
  ()

val lemma_ghost_memcpy: is_win:bool -> dst:s8 -> src:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) ->
  Ghost (TS.traceState * nat * HS.mem)
    (requires True)
    (ensures (fun (s1, f1, h1) ->
      (let s0 = create_initial_trusted_state is_win dst src stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_memcpy is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b;dst;src] s1.TS.state.ME.state.BS.mem /\
      post_cond h0 h1 dst src  /\
      calling_conventions is_win s0 s1)
    ))

let lemma_ghost_memcpy is_win dst src stack_b h0 =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  implies_pre is_win h0 dst src stack_b;
  let s0 = create_initial_trusted_state is_win dst src stack_b h0 in
  create_lemma is_win dst src stack_b h0;
  let s_v, f_v = va_lemma_memcpy (va_code_memcpy is_win) (state_of_S s0) is_win stack_b dst src  in
  implies_post is_win (state_of_S s0) s_v f_v dst src stack_b;
  Some?.v (TS.taint_eval_code (va_code_memcpy is_win) f_v s0), f_v, s_v.mem.hs

#set-options "--max_fuel 0 --max_ifuel 0"

let memcpy dst src  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
  st_put
    (fun h -> pre_cond h dst src /\ B.length stack_b == 24 /\ live h stack_b /\ buf_disjoint_from stack_b [dst;src])
  (fun h -> let _, _, h1 =
    if win then lemma_ghost_memcpy true dst src stack_b h
    else lemma_ghost_memcpy false dst src stack_b h
  in h1);
  pop_frame()
