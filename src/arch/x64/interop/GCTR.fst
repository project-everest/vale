module GCTR

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open Types_s
open Types_i
open Words_s
open Words.Seq_s
open AES_s
open GCTR_s
open GCTR_i
open GCM_s
open GCM_helpers_i
open GHash_i
#set-options "--z3rlimit 40"

open Vale_gctr_bytes_extra_buffer

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

let buffer_to_seq_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let buffer_to_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer UInt8.t { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

open FStar.Mul

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (plain_b:b8) (num_bytes:nat32) (iv_old:Ghost.erased (quad32)) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) = live h plain_b /\ live h iv_b /\ live h keys_b /\ live h cipher_b /\ locs_disjoint [plain_b;iv_b;keys_b;cipher_b] /\ length plain_b % 16 == 0 /\ length iv_b % 16 == 0 /\ length keys_b % 16 == 0 /\ length cipher_b % 16 == 0
/\ (    let mods = M.loc_buffer cipher_b in 
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer keys_b)  mods /\
    
    B.length plain_b  == bytes_to_quad_size num_bytes * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length plain_b % 16 == 0 /\

    4096 * num_bytes < pow2_32 /\
    256 * bytes_to_quad_size num_bytes < pow2_32 /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h /\

    // Extra reqs
    (let num_bytes = num_bytes in
     let num_blocks = num_bytes / 16 in
     let iv = buffer_to_quad32 iv_b h in
     num_bytes % 16 <> 0 /\
     0 < num_bytes /\ num_bytes < 16 * bytes_to_quad_size num_bytes /\
     16 * (bytes_to_quad_size num_bytes - 1) < num_bytes /\
     gctr_partial AES_128 
                  num_blocks 
                  (buffer_to_seq_quad32 plain_b h) 
                  (buffer_to_seq_quad32  cipher_b h) 
                  (Ghost.reveal key) 
                  (Ghost.reveal iv_old) /\
     iv == inc32 (Ghost.reveal iv_old) num_blocks) 
     )

let post_cond (h:HS.mem) (h':HS.mem) (plain_b:b8) (num_bytes:nat32) (iv_old:Ghost.erased (quad32)) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) = length plain_b % 16 == 0 /\ length iv_b % 16 == 0 /\ length keys_b % 16 == 0 /\ length cipher_b % 16 == 0 /\ (let mods = M.loc_buffer cipher_b in
    M.modifies mods h h' /\
    B.live h' plain_b /\ B.live h' iv_b /\ B.live h' keys_b /\ B.live h' cipher_b /\
    
    B.length plain_b  == bytes_to_quad_size num_bytes * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length plain_b % 16 == 0 /\
    B.length keys_b == (nr AES_128 + 1) * 16 /\

    (let num_bytes = num_bytes in
     let num_blocks = num_bytes / 16 in
     let iv_new = buffer_to_quad32 iv_b h in

     // We modified cipher_b, but we didn't disrupt the work that was previously done
     let cipher_blocks  = Seq.slice (buffer_to_seq_quad32 cipher_b h)  0 num_blocks in
     let cipher_blocks' = Seq.slice (buffer_to_seq_quad32 cipher_b h') 0 num_blocks in
     cipher_blocks == cipher_blocks' /\
     
     // GCTR
     (let plain  = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 num_bytes in
      let cipher = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 num_bytes in     
      cipher == gctr_encrypt_LE (Ghost.reveal iv_old) (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key))
    )
  )

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 7 --max_fuel 7 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (plain_b:b8) (num_bytes:nat32) (iv_old:Ghost.erased (quad32)) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) : Lemma
  (requires pre_cond h0 plain_b num_bytes iv_old iv_b key keys_b cipher_b )
  (ensures (
(  let buffers = plain_b::iv_b::keys_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_plain_b
    | Rsi -> num_bytes
    | Rdx -> addr_iv_b
    | Rcx -> addr_keys_b
    | R8 -> addr_cipher_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  va_pre (va_code_gctr_bytes_extra_buffer ()) s0 plain_b num_bytes (Ghost.reveal iv_old) iv_b (Ghost.reveal key) keys_b cipher_b ))) =
  let buffers = plain_b::iv_b::keys_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_plain_b
    | Rsi -> num_bytes
    | Rdx -> addr_iv_b
    | Rcx -> addr_keys_b
    | R8 -> addr_cipher_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let va_s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in  
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert (Seq.equal (buffer_to_seq_quad32 cipher_b h0) (buffer128_as_seq (va_get_mem va_s0) cipher_b));
  assert (Seq.equal (buffer_to_seq_quad32 plain_b va_s0.mem.hs) (buffer128_as_seq (va_get_mem va_s0) plain_b));
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) iv_b) (buffer128_as_seq (va_get_mem va_s0) iv_b));
  let iv128_b = BV.mk_buffer_view iv_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) iv_b) (BV.as_seq h0 iv128_b));
  BV.as_seq_sel h0 iv128_b 0;
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) keys_b) (BV.as_seq h0 keys128_b));
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (plain_b:b8) (num_bytes:nat32) (iv_old:Ghost.erased (quad32)) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8)  : Lemma
  (requires pre_cond va_s0.mem.hs plain_b num_bytes iv_old iv_b key keys_b cipher_b /\
    va_post (va_code_gctr_bytes_extra_buffer ()) va_s0 va_sM va_fM plain_b num_bytes (Ghost.reveal iv_old) iv_b (Ghost.reveal key) keys_b cipher_b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs plain_b num_bytes iv_old iv_b key keys_b cipher_b ) =
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert (Seq.equal (buffer_to_seq_quad32 cipher_b va_s0.mem.hs) (buffer128_as_seq (va_get_mem va_s0) cipher_b));
  assert (Seq.equal (buffer_to_seq_quad32 cipher_b va_sM.mem.hs) (buffer128_as_seq (va_get_mem va_sM) cipher_b));
  assert (Seq.equal (buffer_to_seq_quad32 plain_b va_s0.mem.hs) (buffer128_as_seq (va_get_mem va_s0) plain_b));  
  ()

val gctr_bytes_extra_buffer: plain_b:b8 -> num_bytes:nat32 -> iv_old:Ghost.erased (quad32) -> iv_b:b8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:b8 -> cipher_b:b8 -> Stack unit
	(requires (fun h -> pre_cond h plain_b num_bytes iv_old iv_b key keys_b cipher_b ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 plain_b num_bytes iv_old iv_b key keys_b cipher_b ))

val ghost_gctr_bytes_extra_buffer: plain_b:b8 -> num_bytes:nat32 -> iv_old:Ghost.erased (quad32) -> iv_b:b8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:b8 -> cipher_b:b8 -> (h0:HS.mem{pre_cond h0 plain_b num_bytes iv_old iv_b key keys_b cipher_b }) -> GTot (h1:HS.mem{post_cond h0 h1 plain_b num_bytes iv_old iv_b key keys_b cipher_b })

let ghost_gctr_bytes_extra_buffer plain_b num_bytes iv_old iv_b key keys_b cipher_b h0 =
  let buffers = plain_b::iv_b::keys_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_plain_b
    | Rsi -> num_bytes
    | Rdx -> addr_iv_b
    | Rcx -> addr_keys_b
    | R8 -> addr_cipher_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  implies_pre h0 plain_b num_bytes iv_old iv_b key keys_b cipher_b ;
  let s1, f1 = va_lemma_gctr_bytes_extra_buffer (va_code_gctr_bytes_extra_buffer ()) s0 plain_b num_bytes (Ghost.reveal iv_old) iv_b (Ghost.reveal key) keys_b cipher_b  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_gctr_bytes_extra_buffer is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_gctr_bytes_extra_buffer ()) s0 s1 f1);
  implies_post s0 s1 f1 plain_b num_bytes iv_old iv_b key keys_b cipher_b ;
  s1.mem.hs

let gctr_bytes_extra_buffer plain_b num_bytes iv_old iv_b key keys_b cipher_b  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h plain_b num_bytes iv_old iv_b key keys_b cipher_b ) (ghost_gctr_bytes_extra_buffer plain_b num_bytes iv_old iv_b key keys_b cipher_b )
