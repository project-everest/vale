module GHash_extra

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
open Words.Seq_s
open Types_i
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open GCTR_s
open GCTR_i
open GCM_s
open GCM_helpers_i
open GHash_i
#set-options "--z3rlimit 40"

open Vale_ghash_incremental_extra_stdcall

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

let buffer_to_seq_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

open FStar.Mul

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (in_b:b8) (hash_b:b8) (h_b:b8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32)) = live h in_b /\ live h hash_b /\ live h h_b /\ locs_disjoint [in_b;hash_b;h_b] /\ length in_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length h_b % 16 == 0 /\
   ( let mods = M.loc_buffer hash_b in 
    B.live h in_b /\ B.live h hash_b /\ B.live h h_b /\ 
    M.loc_disjoint (M.loc_buffer in_b) mods /\
    M.loc_disjoint (M.loc_buffer h_b)  mods /\
    
    B.length in_b  == bytes_to_quad_size num_bytes * 16 /\
    B.length in_b % 16 == 0 /\

    B.length h_b == 16 /\
    B.length hash_b == 16 /\

    4096 * num_bytes < pow2_32 /\
    256 * bytes_to_quad_size num_bytes < pow2_32 /\
    
    (let num_blocks = num_bytes / 16 in    
     let old_hash = buffer_to_quad32 hash_b h in
     //let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     // GHash reqs
     let input = Seq.slice (buffer_to_seq_quad32 in_b h) 0 num_blocks in
     old_hash == ghash_incremental0 h_val (Ghost.reveal orig_hash) input /\
     
     // Extra reqs
     num_bytes % 16 <> 0 /\ 
     0 < num_bytes /\ num_bytes < 16 * bytes_to_quad_size num_bytes /\
     16 * (bytes_to_quad_size num_bytes - 1) < num_bytes /\

     True
    )
)

let post_cond (h:HS.mem) (h':HS.mem) (in_b:b8) (hash_b:b8) (h_b:b8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32)) = length in_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length h_b % 16 == 0 /\
    B.length in_b  == bytes_to_quad_size num_bytes * 16 /\
    B.length h_b == 16 /\
    B.length hash_b == 16 /\
    (let mods = M.loc_buffer hash_b in
    M.modifies mods h h' /\
    B.live h in_b /\ B.live h hash_b /\ B.live h h_b /\
    (let num_blocks = num_bytes / 16 in
     let old_hash = buffer_to_quad32 hash_b h in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     let input_bytes = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 in_b h')) 0 num_bytes in
     let padded_bytes = pad_to_128_bits input_bytes in
     let input_quads = le_bytes_to_seq_quad32 padded_bytes in
     (num_bytes > 0 ==> Seq.length input_quads > 0 /\ 
                       new_hash == ghash_incremental h_val (Ghost.reveal orig_hash) input_quads)
    )
  ) 


//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (in_b:b8) (hash_b:b8) (h_b:b8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32)) : Lemma
  (requires pre_cond h0 in_b hash_b h_b num_bytes orig_hash )
  (ensures (
(  let buffers = in_b::hash_b::h_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_in_b = addrs in_b in
  let addr_hash_b = addrs hash_b in
  let addr_h_b = addrs h_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_in_b
    | Rsi -> addr_hash_b
    | Rdx -> addr_h_b
    | Rcx -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  va_pre (va_code_ghash_incremental_extra_stdcall ()) s0 in_b hash_b h_b num_bytes (Ghost.reveal orig_hash) ))) =
  let buffers = in_b::hash_b::h_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_in_b = addrs in_b in
  let addr_hash_b = addrs hash_b in
  let addr_h_b = addrs h_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_in_b
    | Rsi -> addr_hash_b
    | Rdx -> addr_h_b
    | Rcx -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in  
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  assert (Seq.equal (buffer_to_seq_quad32 in_b h0) (buffer128_as_seq (va_get_mem s0) in_b));
  let h128_b = BV.mk_buffer_view h_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem s0) h_b) (BV.as_seq h0 h128_b));
  BV.as_seq_sel h0 h128_b 0;  
  let hash128_b = BV.mk_buffer_view hash_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem s0) hash_b) (BV.as_seq h0 hash128_b));
  BV.as_seq_sel h0 hash128_b 0;  
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (in_b:b8) (hash_b:b8) (h_b:b8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32))  : Lemma
  (requires pre_cond va_s0.mem.hs in_b hash_b h_b num_bytes orig_hash /\
    va_post (va_code_ghash_incremental_extra_stdcall ()) va_s0 va_sM va_fM in_b hash_b h_b num_bytes (Ghost.reveal orig_hash) )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs in_b hash_b h_b num_bytes orig_hash ) =
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  assert (Seq.equal (buffer_to_seq_quad32 in_b va_sM.mem.hs) (buffer128_as_seq (va_get_mem va_sM) in_b));
  let hash128_b = BV.mk_buffer_view hash_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) hash_b) (BV.as_seq va_s0.mem.hs hash128_b));
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) hash_b) (BV.as_seq va_sM.mem.hs hash128_b));
  BV.as_seq_sel va_s0.mem.hs hash128_b 0;
  BV.as_seq_sel va_sM.mem.hs hash128_b 0;
  let h128_b = BV.mk_buffer_view h_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) h_b) (BV.as_seq va_s0.mem.hs h128_b));
  BV.as_seq_sel va_s0.mem.hs h128_b 0;
  ()

val ghash_incremental_extra_stdcall: in_b:b8 -> hash_b:b8 -> h_b:b8 -> num_bytes:nat64 -> orig_hash:Ghost.erased (quad32) -> Stack unit
	(requires (fun h -> pre_cond h in_b hash_b h_b num_bytes orig_hash ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 in_b hash_b h_b num_bytes orig_hash ))

val ghost_ghash_incremental_extra_stdcall: in_b:b8 -> hash_b:b8 -> h_b:b8 -> num_bytes:nat64 -> orig_hash:Ghost.erased (quad32) -> (h0:HS.mem{pre_cond h0 in_b hash_b h_b num_bytes orig_hash }) -> GTot (h1:HS.mem{post_cond h0 h1 in_b hash_b h_b num_bytes orig_hash })

let ghost_ghash_incremental_extra_stdcall in_b hash_b h_b num_bytes orig_hash h0 =
  let buffers = in_b::hash_b::h_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_in_b = addrs in_b in
  let addr_hash_b = addrs hash_b in
  let addr_h_b = addrs h_b in
  let regs = fun r -> begin match r with
    | Rdi -> addr_in_b
    | Rsi -> addr_hash_b
    | Rdx -> addr_h_b
    | Rcx -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  implies_pre h0 in_b hash_b h_b num_bytes orig_hash ;
  let s1, f1 = va_lemma_ghash_incremental_extra_stdcall (va_code_ghash_incremental_extra_stdcall ()) s0 in_b hash_b h_b num_bytes (Ghost.reveal orig_hash)  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  // Ensures that va_code_ghash_incremental_extra_stdcall is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_ghash_incremental_extra_stdcall ()) s0 s1 f1);
  implies_post s0 s1 f1 in_b hash_b h_b num_bytes orig_hash ;
  s1.mem.hs

let ghash_incremental_extra_stdcall in_b hash_b h_b num_bytes orig_hash  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h in_b hash_b h_b num_bytes orig_hash ) (ghost_ghash_incremental_extra_stdcall in_b hash_b h_b num_bytes orig_hash )
