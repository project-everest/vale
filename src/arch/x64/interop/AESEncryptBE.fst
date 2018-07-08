module AESEncryptBE

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
open AES_s
open GCTR_i
#set-options "--z3rlimit 40"

open Vale_aes128_encrypt_block_be

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


let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer UInt8.t { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

open FStar.Mul

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (output_b:b8) (input_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) =
live h output_b /\ live h input_b /\ live h keys_b /\ locs_disjoint [output_b;input_b;keys_b] /\ length output_b % 16 == 0 /\ length input_b % 16 == 0 /\ length keys_b % 16 == 0 /\ B.length keys_b == (nr AES_128 + 1) * 16 /\
  keys_match key keys_b h
  /\ B.length output_b >= 1 /\ B.length input_b >= 1


let post_cond (h0:HS.mem) (h1:HS.mem) (output_b:b8) (input_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) =
  length input_b % 16 == 0 /\ length output_b % 16 == 0 /\ length keys_b % 16 == 0 /\
    B.live h1 input_b /\ B.live h1 keys_b /\
    M.modifies (M.loc_buffer output_b) h0 h1 /\
    (let  input128_b = BV.mk_buffer_view  input_b Views.view128 in
     let output128_b = BV.mk_buffer_view output_b Views.view128 in
     BV.length input128_b >= 1 /\ BV.length output128_b >= 1 /\
    (let  input_q = Seq.index (BV.as_seq h0 input128_b) 0 in 
     let output_q = Seq.index (BV.as_seq h1 output128_b) 0 in
     output_q == aes_encrypt_BE AES_128 (Ghost.reveal key) input_q))



//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (output_b:b8) (input_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) : Lemma
  (requires pre_cond h0 output_b input_b key keys_b )
  (ensures (
(  let buffers = output_b::input_b::keys_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_output_b = addrs output_b in
  let addr_input_b = addrs input_b in
  let addr_keys_b = addrs keys_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_output_b
    | Rsi -> addr_input_b
    | Rdx -> addr_keys_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  va_pre (va_code_aes128_encrypt_block_be ()) s0 output_b input_b (Ghost.reveal key) keys_b ))) =
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (output_b:b8) (input_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8)  : Lemma
  (requires pre_cond va_s0.mem.hs output_b input_b key keys_b /\
    va_post (va_code_aes128_encrypt_block_be ()) va_s0 va_sM va_fM output_b input_b (Ghost.reveal key) keys_b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs output_b input_b key keys_b ) =
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  ()

val aes128_encrypt_block_be: output_b:b8 -> input_b:b8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:b8 -> Stack unit
	(requires (fun h -> pre_cond h output_b input_b key keys_b ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 output_b input_b key keys_b ))

val ghost_aes128_encrypt_block_be: output_b:b8 -> input_b:b8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:b8 -> (h0:HS.mem{pre_cond h0 output_b input_b key keys_b }) -> GTot (h1:HS.mem{post_cond h0 h1 output_b input_b key keys_b })

let ghost_aes128_encrypt_block_be output_b input_b key keys_b h0 =
  let buffers = output_b::input_b::keys_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_output_b = addrs output_b in
  let addr_input_b = addrs input_b in
  let addr_keys_b = addrs keys_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_output_b
    | Rsi -> addr_input_b
    | Rdx -> addr_keys_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  implies_pre h0 output_b input_b key keys_b ;
  let s1, f1 = va_lemma_aes128_encrypt_block_be (va_code_aes128_encrypt_block_be ()) s0 output_b input_b (Ghost.reveal key) keys_b  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_aes128_encrypt_block_be is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_aes128_encrypt_block_be ()) s0 s1 f1);
  implies_post s0 s1 f1 output_b input_b key keys_b ;
  s1.mem.hs

let aes128_encrypt_block_be output_b input_b key keys_b  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h output_b input_b key keys_b ) (ghost_aes128_encrypt_block_be output_b input_b key keys_b )
