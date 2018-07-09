module GCMEncrypt

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Opaque_s
open Words_s
open Words.Seq_s
open Types_i
open Types_s
open FStar.Seq
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open AES_s
open GCM_s
open GCM_helpers_i
module U8 = FStar.UInt8
module U64 = FStar.UInt64
#set-options "--z3rlimit 40"

open Vale_gcmencrypt

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

let b8 = B.buffer UInt8.t

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

let equal_seqs_vale (b:b8) (num_bytes:nat) (mem:mem) : Lemma (requires B.length b % 16 = 0 /\ num_bytes <= B.length b)
(ensures
(   
  let s = seq_U8_to_seq_nat8 (slice (B.as_seq mem.hs b) 0 num_bytes) in
  let s_vale = slice_work_around (le_seq_quad32_to_bytes (buffer128_as_seq mem b)) num_bytes in
  Seq.equal s s_vale
  )) =
  Opaque_s.reveal_opaque le_seq_quad32_to_bytes_def;
  admit()


//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 9 --max_fuel 9 --initial_ifuel 2 --max_ifuel 2"

// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (plain_b:b8) (plain_num_bytes:nat64) (auth_b:b8) (auth_num_bytes:nat64) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) (tag_b:b8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b /\ B.length stack_b == 216 /\ live h0 stack_b /\ locs_disjoint [stack_b;plain_b;auth_b;iv_b;keys_b;cipher_b;tag_b])
  (ensures (
B.length stack_b == 216 /\ live h0 stack_b /\ locs_disjoint [stack_b;plain_b;auth_b;iv_b;keys_b;cipher_b;tag_b] /\ (  let buffers = stack_b::plain_b::auth_b::iv_b::keys_b::cipher_b::tag_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_auth_b = addrs auth_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_tag_b = addrs tag_b in
  let addr_stack:nat64 = addrs stack_b + 144 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> plain_num_bytes
    | R8 -> addr_auth_b
    | R9 -> auth_num_bytes
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 23 (addrs iv_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 24 (addrs keys_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 25 (addrs cipher_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 26 (addrs tag_b) mem in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) auth_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  length_t_eq (TBase TUInt128) tag_b;
  length_t_eq (TBase TUInt64) stack_b;
  va_pre (va_code_gcmencrypt ()) s0 plain_b plain_num_bytes auth_b auth_num_bytes iv_b (Ghost.reveal key) keys_b cipher_b tag_b stack_b))) =
let buffers = stack_b::plain_b::auth_b::iv_b::keys_b::cipher_b::tag_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_auth_b = addrs auth_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_tag_b = addrs tag_b in
  let addr_stack:nat64 = addrs stack_b + 144 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> plain_num_bytes
    | R8 -> addr_auth_b
    | R9 -> auth_num_bytes
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 23 (addrs iv_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 24 (addrs keys_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 25 (addrs cipher_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 26 (addrs tag_b) mem in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in  
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) auth_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  length_t_eq (TBase TUInt128) tag_b;
  length_t_eq (TBase TUInt64) stack_b;
  BV.as_buffer_mk_buffer_view keys_b Views.view128;
  BV.get_view_mk_buffer_view keys_b Views.view128;
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in  
  assert (Seq.equal
    (buffer128_as_seq mem keys_b)
    (BV.as_seq h0 keys128_b));
  ()

#set-options "--z3rlimit 120"

let implies_post (h0:HS.mem) (va_sM:va_state) (va_fM:va_fuel) (plain_b:b8) (plain_num_bytes:nat64) (auth_b:b8) (auth_num_bytes:nat64) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) (tag_b:b8)  (stack_b:b8) : Lemma
  (requires
  pre_cond h0 plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b /\ B.length stack_b == 216 /\ live h0 stack_b /\ locs_disjoint [stack_b;plain_b;auth_b;iv_b;keys_b;cipher_b;tag_b] /\ (
let buffers = stack_b::plain_b::auth_b::iv_b::keys_b::cipher_b::tag_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_auth_b = addrs auth_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_tag_b = addrs tag_b in
  let addr_stack:nat64 = addrs stack_b + 144 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> plain_num_bytes
    | R8 -> addr_auth_b
    | R9 -> auth_num_bytes
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 23 (addrs iv_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 24 (addrs keys_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 25 (addrs cipher_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 26 (addrs tag_b) mem in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) auth_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  length_t_eq (TBase TUInt128) tag_b;
  length_t_eq (TBase TUInt64) stack_b;
    va_post (va_code_gcmencrypt ()) s0 va_sM va_fM plain_b plain_num_bytes auth_b auth_num_bytes iv_b (Ghost.reveal key) keys_b cipher_b tag_b stack_b))
  (ensures post_cond h0 va_sM.mem.hs plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b ) =
  let buffers = stack_b::plain_b::auth_b::iv_b::keys_b::cipher_b::tag_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_auth_b = addrs auth_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_tag_b = addrs tag_b in
  let addr_stack:nat64 = addrs stack_b + 144 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> plain_num_bytes
    | R8 -> addr_auth_b
    | R9 -> auth_num_bytes
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 23 (addrs iv_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 24 (addrs keys_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 25 (addrs cipher_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 26 (addrs tag_b) mem in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in  
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) auth_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  length_t_eq (TBase TUInt128) tag_b;
  length_t_eq (TBase TUInt64) stack_b;
  let iv128_b  = BV.mk_buffer_view iv_b  Views.view128 in
  let tag128_b = BV.mk_buffer_view tag_b Views.view128 in  
  assert (Seq.equal (buffer128_as_seq s0.mem iv_b)
		    (BV.as_seq s0.mem.hs iv128_b));
  assert (Seq.equal (buffer128_as_seq va_sM.mem tag_b)
		    (BV.as_seq va_sM.mem.hs tag128_b));
  equal_seqs_vale plain_b plain_num_bytes (va_get_mem s0);
  equal_seqs_vale cipher_b plain_num_bytes (va_get_mem va_sM);
  equal_seqs_vale auth_b auth_num_bytes (va_get_mem s0);
  ()

#set-options "--z3rlimit 60 --initial_fuel 9 --max_fuel 9 --initial_ifuel 2 --max_ifuel 2"


val ghost_gcmencrypt: plain_b:b8 -> plain_num_bytes:nat64 -> auth_b:b8 -> auth_num_bytes:nat64 -> iv_b:b8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:b8 -> cipher_b:b8 -> tag_b:b8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b /\ B.length stack_b == 216 /\ live h0 stack_b /\ locs_disjoint [stack_b;plain_b;auth_b;iv_b;keys_b;cipher_b;tag_b]}) -> GTot (h1:HS.mem{post_cond h0 h1 plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b
 /\ M.modifies (M.loc_union
    (M.loc_union (M.loc_buffer stack_b) (M.loc_buffer cipher_b)) (M.loc_buffer tag_b)) h0 h1})

let ghost_gcmencrypt plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b stack_b h0 =
  let buffers = stack_b::plain_b::auth_b::iv_b::keys_b::cipher_b::tag_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_auth_b = addrs auth_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_tag_b = addrs tag_b in
  let addr_stack:nat64 = addrs stack_b + 144 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> plain_num_bytes
    | R8 -> addr_auth_b
    | R9 -> auth_num_bytes
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 23 (addrs iv_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 24 (addrs keys_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 25 (addrs cipher_b) mem in
  let mem = buffer_write #(TBase TUInt64) stack_b 26 (addrs tag_b) mem in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) auth_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  length_t_eq (TBase TUInt128) tag_b;
  length_t_eq (TBase TUInt64) stack_b;
  implies_pre h0 plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b stack_b ;
  let s1, f1 = va_lemma_gcmencrypt (va_code_gcmencrypt ()) s0 plain_b plain_num_bytes auth_b auth_num_bytes iv_b (Ghost.reveal key) keys_b cipher_b tag_b stack_b in
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
  // Ensures that va_code_gcmencrypt is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_gcmencrypt ()) s0 s1 f1);
  implies_post h0 s1 f1 plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b stack_b ;
  s1.mem.hs


let gcmencrypt plain_b plain_num_bytes auth_b auth_num_bytes iv_b key keys_b cipher_b tag_b  =
  let init_h0 = get () in
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 216) in
  let h0 = get() in
  assume (let keys128_b = BV.mk_buffer_view keys_b Views.view128 in BV.as_seq init_h0 keys128_b == BV.as_seq h0 keys128_b);
  st_put h0 (fun h -> pre_cond h plain_b (UInt64.v plain_num_bytes) auth_b (UInt64.v auth_num_bytes) iv_b key keys_b cipher_b tag_b /\ B.length stack_b == 216 /\ live h stack_b /\ locs_disjoint [stack_b;plain_b;auth_b;iv_b;keys_b;cipher_b;tag_b]) (ghost_gcmencrypt plain_b (UInt64.v plain_num_bytes) auth_b (UInt64.v auth_num_bytes) iv_b key keys_b cipher_b tag_b stack_b);
  let h1 = get() in
  pop_frame();
  let h1_final = get() in
  assume (
    let iv128_b  = BV.mk_buffer_view iv_b  Views.view128 in
    let tag128_b = BV.mk_buffer_view tag_b Views.view128 in
    BV.as_seq h1 tag128_b == BV.as_seq h1_final tag128_b /\
    BV.as_seq h0 iv128_b == BV.as_seq init_h0 iv128_b)
