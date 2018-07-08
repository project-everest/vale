module Gcm_load_xor

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
open GCTR_s
open GCTR_i
#set-options "--z3rlimit 40"

open Vale_gcm_load_xor_store_buffer

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
  //index (BV.as_seq h b128) 0

let buffer_to_seq_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

open FStar.Mul

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (plain_b:b8) (mask_b:b8) (cipher_b:b8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32)) = live h plain_b /\ live h mask_b /\ live h cipher_b /\ locs_disjoint [plain_b;mask_b;cipher_b] /\ length plain_b % 16 == 0 /\ length mask_b % 16 == 0 /\ length cipher_b % 16 == 0
 /\  ( let mods = M.loc_buffer cipher_b in  
    B.live h plain_b /\ B.live h mask_b /\ B.live h cipher_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer mask_b)  mods /\
    B.length plain_b  >= (Ghost.reveal num_blocks) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length mask_b == 16 /\
    B.length plain_b % 16 == 0 /\
    (let num_blocks = (Ghost.reveal num_blocks) in
     let mask   = buffer_to_quad32       mask_b h in
     let plain  = buffer_to_seq_quad32  plain_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h in
     let key = Ghost.reveal key in
     let iv = Ghost.reveal iv in

     // gcm_body specific
     offset < num_blocks /\
     mask == aes_encrypt_BE AES_128 key (inc32 iv offset) /\
     gctr_partial AES_128 offset plain cipher key iv
    )
  )

let post_cond (h:HS.mem) (h':HS.mem) (plain_b:b8) (mask_b:b8) (cipher_b:b8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32)) = length plain_b % 16 == 0 /\ length mask_b % 16 == 0 /\ length cipher_b % 16 == 0 /\
    B.length plain_b  >= (Ghost.reveal num_blocks) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length mask_b == 16 /\
   (   let mods = M.loc_buffer cipher_b in
    M.modifies mods h h' /\
    B.live h plain_b /\ B.live h mask_b /\ B.live h cipher_b /\
    (let num_blocks = (Ghost.reveal num_blocks) in
     let mask   = buffer_to_quad32  mask_b h in
     let plain  = buffer_to_seq_quad32  plain_b h' in
     let old_cipher = buffer_to_seq_quad32 cipher_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h' in
     let key = Ghost.reveal key in
     let iv = Ghost.reveal iv in
     offset < num_blocks /\
     gctr_partial AES_128 (offset + 1) plain cipher key iv /\
     Seq.slice cipher 0 offset == Seq.slice old_cipher 0 offset  // We didn't disrupt earlier slots
    )
    )

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (plain_b:b8) (mask_b:b8) (cipher_b:b8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32)) : Lemma
  (requires pre_cond h0 plain_b mask_b cipher_b offset num_blocks key iv )
  (ensures (
(  let buffers = plain_b::mask_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_mask_b = addrs mask_b in
  let addr_cipher_b = addrs cipher_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_plain_b
    | Rsi -> addr_mask_b
    | Rdx -> addr_cipher_b
    | Rcx -> offset
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  va_pre (va_code_gcm_load_xor_store_buffer ()) s0 plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv) ))) =
  let buffers = plain_b::mask_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_mask_b = addrs mask_b in
  let addr_cipher_b = addrs cipher_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_plain_b
    | Rsi -> addr_mask_b
    | Rdx -> addr_cipher_b
    | Rcx -> offset
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let va_s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in  
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_s0) plain_b)
    (buffer_to_seq_quad32 plain_b va_s0.mem.hs));
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_s0) cipher_b)
    (buffer_to_seq_quad32 cipher_b va_s0.mem.hs));
  let mask128 = BV.mk_buffer_view mask_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) mask_b) (BV.as_seq va_s0.mem.hs mask128));
  BV.as_seq_sel h0 mask128 0;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (plain_b:b8) (mask_b:b8) (cipher_b:b8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32))  : Lemma
  (requires pre_cond va_s0.mem.hs plain_b mask_b cipher_b offset num_blocks key iv /\
    va_post (va_code_gcm_load_xor_store_buffer ()) va_s0 va_sM va_fM plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv) )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs plain_b mask_b cipher_b offset num_blocks key iv ) =
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_s0) cipher_b)
    (buffer_to_seq_quad32 cipher_b va_s0.mem.hs));
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_sM) cipher_b)
    (buffer_to_seq_quad32 cipher_b va_sM.mem.hs));
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_sM) plain_b)
    (buffer_to_seq_quad32 plain_b va_sM.mem.hs));    
  let mask128 = BV.mk_buffer_view mask_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) mask_b) (BV.as_seq va_s0.mem.hs mask128));
  BV.as_seq_sel va_s0.mem.hs mask128 0;    
  ()

val gcm_load_xor_store_buffer: plain_b:b8 -> mask_b:b8 -> cipher_b:b8 -> offset:nat64 -> num_blocks:Ghost.erased (nat64) -> key:Ghost.erased (aes_key_LE AES_128) -> iv:Ghost.erased (quad32) -> Stack unit
	(requires (fun h -> pre_cond h plain_b mask_b cipher_b offset num_blocks key iv ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 plain_b mask_b cipher_b offset num_blocks key iv ))

val ghost_gcm_load_xor_store_buffer: plain_b:b8 -> mask_b:b8 -> cipher_b:b8 -> offset:nat64 -> num_blocks:Ghost.erased (nat64) -> key:Ghost.erased (aes_key_LE AES_128) -> iv:Ghost.erased (quad32) -> (h0:HS.mem{pre_cond h0 plain_b mask_b cipher_b offset num_blocks key iv }) -> GTot (h1:HS.mem{post_cond h0 h1 plain_b mask_b cipher_b offset num_blocks key iv })

let ghost_gcm_load_xor_store_buffer plain_b mask_b cipher_b offset num_blocks key iv h0 =
  let buffers = plain_b::mask_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_mask_b = addrs mask_b in
  let addr_cipher_b = addrs cipher_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_plain_b
    | Rsi -> addr_mask_b
    | Rdx -> addr_cipher_b
    | Rcx -> offset
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  implies_pre h0 plain_b mask_b cipher_b offset num_blocks key iv ;
  let s1, f1 = va_lemma_gcm_load_xor_store_buffer (va_code_gcm_load_xor_store_buffer ()) s0 plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv)  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_gcm_load_xor_store_buffer is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_gcm_load_xor_store_buffer ()) s0 s1 f1);
  implies_post s0 s1 f1 plain_b mask_b cipher_b offset num_blocks key iv ;
  s1.mem.hs

let gcm_load_xor_store_buffer plain_b mask_b cipher_b offset num_blocks key iv  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h plain_b mask_b cipher_b offset num_blocks key iv ) (ghost_gcm_load_xor_store_buffer plain_b mask_b cipher_b offset num_blocks key iv )
