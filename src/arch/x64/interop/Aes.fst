module Aes

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
module M = LowStar.Modifies
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open AES_s
open Types_i
#set-options "--z3rlimit 40"

open Vale_aes

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : ST unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (input_key:B.buffer UInt8.t) (output_key:B.buffer UInt8.t) = live h input_key /\ live h output_key /\ disjoint input_key output_key /\ length input_key % 16 == 0 /\ length output_key % 16 == 0 /\
  length input_key == 16 /\ length output_key == 176
let post_cond (h0:HS.mem) (h1:HS.mem) (input_key:B.buffer UInt8.t) (output_key:B.buffer UInt8.t) = live h0 input_key /\ live h0 output_key /\ live h1 input_key /\ live h1 output_key /\ length input_key % 16 == 0 /\ length output_key % 16 == 0 /\   
length input_key == 16 /\ length output_key == 176 /\
M.modifies (M.loc_buffer output_key) h0 h1 /\
  (let output_b = BV.mk_buffer_view output_key Views.view128 in
  let input_b = BV.mk_buffer_view input_key Views.view128 in
  length_t_eq (TBase TUInt128) output_key;
  length_t_eq (TBase TUInt128) input_key;
  let key = quad32_to_seq (Seq.index (BV.as_seq h0 input_b) 0) in
  let result = key_to_round_keys_LE AES_128 key in
  (forall j. 0 <= j /\ j <= 10 ==>
    Seq.index (BV.as_seq h1 output_b) j ==
    Seq.index result j))

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (input_key:B.buffer UInt8.t) (output_key:B.buffer UInt8.t) : Lemma
  (requires pre_cond h0 input_key output_key )
  (ensures (
  let buffers = input_key::output_key::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_input_key = addrs input_key in
  let addr_output_key = addrs output_key in
  let regs = fun r -> begin match r with
    | Rdi -> addr_input_key
    | Rsi -> addr_output_key
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) input_key;
  length_t_eq (TBase TUInt128) output_key;
  va_pre (va_code_aes ()) s0 input_key output_key )) =
  length_t_eq (TBase TUInt128) input_key;
  length_t_eq (TBase TUInt128) output_key;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (input_key:B.buffer UInt8.t) (output_key:B.buffer UInt8.t)  : Lemma
  (requires pre_cond va_s0.mem.hs input_key output_key /\
    va_post (va_code_aes ()) va_s0 va_sM va_fM input_key output_key )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs input_key output_key ) =
  length_t_eq (TBase TUInt128) input_key;
  length_t_eq (TBase TUInt128) output_key;
  assert (forall j. 0 <= j /\ j <= 10 ==>
    Seq.index (BV.as_seq va_sM.mem.hs (BV.mk_buffer_view output_key Views.view128)) j == buffer128_read output_key j va_sM.mem);    
  ()

val aes: input_key:B.buffer UInt8.t -> output_key:B.buffer UInt8.t -> ST unit
	(requires (fun h -> pre_cond h input_key output_key ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 input_key output_key ))

val ghost_aes: input_key:B.buffer UInt8.t -> output_key:B.buffer UInt8.t -> (h0:HS.mem{pre_cond h0 input_key output_key }) -> GTot (h1:HS.mem{post_cond h0 h1 input_key output_key })

let ghost_aes input_key output_key h0 =
  let buffers = input_key::output_key::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_input_key = addrs input_key in
  let addr_output_key = addrs output_key in
  let regs = fun r -> begin match r with
    | Rdi -> addr_input_key
    | Rsi -> addr_output_key
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) input_key;
  length_t_eq (TBase TUInt128) output_key;
  implies_pre h0 input_key output_key ;
  let s1, f1 = va_lemma_aes (va_code_aes ()) s0 input_key output_key  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_aes is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_aes ()) s0 s1 f1);
  implies_post s0 s1 f1 input_key output_key ;
  s1.mem.hs

let aes input_key output_key  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h input_key output_key ) (ghost_aes input_key output_key )
