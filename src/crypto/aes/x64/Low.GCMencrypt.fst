module Low.GCMencrypt

open FStar.HyperStack.ST

module B = LowStar.Buffer
module BV = LowStar.BufferView
module M = LowStar.Modifies
open LowStar.ModifiesPat
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module HST = FStar.HyperStack.ST

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
open X64.Memory_i_s
open BufferViewHelpers
open FStar.Seq

// Not sure how to define this after we open FStar.Mul
let quad32x3 = quad32 * quad32 * quad32

open FStar.Mul

(*** Useful specification abbreviations ***)

let seq_U8_to_seq_nat8 (b:seq U8.t) : (seq nat8) =
  Seq.init (length b) (fun (i:nat { i < length b }) -> U8.v (index b i))

let buffer_to_nat32 (b:B.buffer U8.t { B.length b % 4 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot nat32 =
  let b32 = BV.mk_buffer_view b Views.view32 in
  BV.as_buffer_mk_buffer_view b Views.view32;
  BV.get_view_mk_buffer_view b Views.view32;
  BV.length_eq b32;
  //assert (B.length b >= 4);
  //assert (BV.length b32 > 0);
  U32.v (BV.sel h b32 0)
  //U32.v (index (BV.as_seq h b32) 0)

let buffer_to_quad32 (b:B.buffer U8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0
  //index (BV.as_seq h b128) 0

let buffer_to_seq_quad32 (b:B.buffer U8.t { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:seq quad32 {length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

(*** Functionality imported from Vale ***)

assume val memcpy_simple
    (dst:B.buffer U8.t{B.length dst % 8 == 0})
    (src:B.buffer U8.t{B.length src == B.length dst})
    (len:U32.t {B.length src == U32.v len}) 
    : Stack unit
  (requires fun h -> B.live h dst /\ B.live h src)
  (ensures fun h () h' -> 
    B.live h' dst /\ B.live h' src /\
    M.modifies (M.loc_buffer dst) h h' /\
    B.as_seq h' dst == B.as_seq h src)

assume val aes128_encrypt_block_buffer 
             (input_b output_b:B.buffer U8.t) 
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             : Stack unit 
  (requires fun h -> 
    B.live h input_b /\ B.live h keys_b /\ B.live h output_b /\
    B.length  input_b % 16 == 0 /\ B.length  input_b >= 16 /\
    B.length output_b % 16 == 0 /\ B.length output_b >= 16 /\    
    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h
  )
  (ensures fun h () h' -> 
    B.live h' input_b /\ B.live h' output_b /\ B.live h' keys_b /\
    M.modifies (M.loc_buffer output_b) h h' /\
    (let  input_q = buffer_to_quad32  input_b h in
     let output_q = buffer_to_quad32 output_b h' in
     output_q == aes_encrypt_LE AES_128 (Ghost.reveal key) input_q)
  )         

assume val gctr_bytes_extra_buffer
             (plain_b:B.buffer U8.t) (num_bytes:U32.t) 
             (iv_old:Ghost.erased quad32)
             (iv_b:B.buffer U8.t) 
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
           : Stack unit
  (requires fun h ->
    let mods = M.loc_buffer cipher_b in 
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer keys_b)  mods /\
    
    B.length plain_b  == bytes_to_quad_size (U32.v num_bytes) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length plain_b % 16 == 0 /\

    4096 * (U32.v num_bytes) < pow2_32 /\
    256 * bytes_to_quad_size (U32.v num_bytes) < pow2_32 /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h /\

    // Extra reqs
    (let num_bytes = U32.v num_bytes in
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
  (ensures fun h () h' ->
    let mods = M.loc_buffer cipher_b in
    M.modifies mods h h' /\
    B.live h' plain_b /\ B.live h' iv_b /\ B.live h' keys_b /\ B.live h' cipher_b /\

    (let num_bytes = U32.v num_bytes in
     let num_blocks = num_bytes / 16 in
     let iv_new = buffer_to_quad32 iv_b h in

     // We modified cipher_b, but we didn't disrupt the work that was previously done
     let cipher_blocks  = slice (buffer_to_seq_quad32 cipher_b h)  0 num_blocks in
     let cipher_blocks' = slice (buffer_to_seq_quad32 cipher_b h') 0 num_blocks in
     cipher_blocks == cipher_blocks' /\
     
     // GCTR
     (let plain  = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 num_bytes in
      let cipher = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 num_bytes in     
      cipher == gctr_encrypt_LE (Ghost.reveal iv_old) (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key))
    )
  ) 

assume val ghash_incremental_bytes_buffer (h_b hash_b input_b:B.buffer U8.t) (num_bytes:U64.t) : Stack unit
  (requires fun h -> 
    B.live h h_b  /\ B.live h hash_b /\ B.live h input_b /\
    B.length     h_b % 16 == 0 /\ B.length    h_b >= 16 /\ 
    B.length  hash_b % 16 == 0 /\ B.length hash_b >= 16 /\ 
    B.length input_b % 16 == 0 /\ 
    B.length input_b >= 16 * (bytes_to_quad_size (U64.v num_bytes)) /\
    True
  )
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer hash_b) h h' /\
    (let old_hash = buffer_to_quad32 hash_b h  in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_q      = buffer_to_quad32 h_b    h  in
     let num_bytes = U64.v num_bytes in 
     (num_bytes == 0 ==> new_hash == old_hash) /\
     (let input_bytes = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 input_b h)) 0 num_bytes in
      let padded_bytes = pad_to_128_bits input_bytes in
      let input_quads = le_bytes_to_seq_quad32 padded_bytes in
      num_bytes > 0 ==>  
        length input_quads > 0 /\
        new_hash == ghash_incremental h_q old_hash input_quads
     )
    )
  )

assume val ghash_incremental_one_block_buffer (h_b hash_b input_b:B.buffer U8.t) (offset:U64.t) : Stack unit
  (requires fun h -> 
    B.live h h_b  /\ B.live h hash_b /\ B.live h input_b /\
    B.length     h_b % 16 == 0 /\ B.length    h_b >= 16 /\ 
    B.length  hash_b % 16 == 0 /\ B.length hash_b >= 16 /\ 
    B.length input_b % 16 == 0 /\ 
    B.length input_b >= 16 * (U64.v offset + 1) /\
    True
  )
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer hash_b) h h' /\
    (let old_hash = buffer_to_quad32 hash_b h  in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_q      = buffer_to_quad32 h_b    h  in
     let offset   = U64.v offset in 
     let input    = buffer_to_seq_quad32 input_b h in
     let input_quad = index input offset in
     new_hash == ghash_incremental h_q old_hash (create 1 input_quad)
    )
  )

assume val ghash_incremental_bytes_extra_buffer
             (in_b hash_b h_b:B.buffer U8.t) (num_bytes:U32.t) 
             (orig_hash:Ghost.erased quad32)
           : Stack unit
  (requires fun h ->
    let mods = M.loc_buffer hash_b in 
    B.live h in_b /\ B.live h hash_b /\ B.live h h_b /\ 
    M.loc_disjoint (M.loc_buffer in_b) mods /\
    M.loc_disjoint (M.loc_buffer h_b)  mods /\
    
    B.length in_b  == bytes_to_quad_size (U32.v num_bytes) * 16 /\
    B.length in_b % 16 == 0 /\

    B.length h_b == 16 /\
    B.length hash_b == 16 /\

    4096 * (U32.v num_bytes) < pow2_32 /\
    256 * bytes_to_quad_size (U32.v num_bytes) < pow2_32 /\
    
    (let num_bytes = U32.v num_bytes in
     let num_blocks = num_bytes / 16 in    
     let old_hash = buffer_to_quad32 hash_b h in
     //let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     // GHash reqs
     let input = slice (buffer_to_seq_quad32 in_b h) 0 num_blocks in
     old_hash == ghash_incremental0 h_val (Ghost.reveal orig_hash) input /\
     
     // Extra reqs
     num_bytes % 16 <> 0 /\ 
     0 < num_bytes /\ num_bytes < 16 * bytes_to_quad_size num_bytes /\
     16 * (bytes_to_quad_size num_bytes - 1) < num_bytes /\

     True
    )
  )
  (ensures fun h () h' ->
    let mods = M.loc_buffer hash_b in
    M.modifies mods h h' /\
    B.live h in_b /\ B.live h hash_b /\ B.live h h_b /\
    (let num_bytes = U32.v num_bytes in
     let num_blocks = num_bytes / 16 in
     let old_hash = buffer_to_quad32 hash_b h in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     let input_bytes = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 in_b h')) 0 num_bytes in
     let padded_bytes = pad_to_128_bits input_bytes in
     let input_quads = le_bytes_to_seq_quad32 padded_bytes in
     (num_bytes > 0 ==> length input_quads > 0 /\ 
                       new_hash == ghash_incremental h_val (Ghost.reveal orig_hash) input_quads)
    )
  ) 

assume val gcm_load_xor_store_buffer
       (plain_b mask_b cipher_b:B.buffer U8.t) 
       (offset:U32.t) 
       (num_blocks:(Ghost.erased U32.t))
       (key:Ghost.erased (aes_key_LE AES_128))
       (iv:(Ghost.erased quad32))
       : Stack unit
  (requires fun h ->
    let mods = M.loc_buffer cipher_b in  
    B.live h plain_b /\ B.live h mask_b /\ B.live h cipher_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer mask_b)  mods /\
    B.length plain_b  >= (U32.v (Ghost.reveal num_blocks)) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length mask_b == 16 /\
    B.length plain_b % 16 == 0 /\
    (let offset = U32.v offset in
     let num_blocks = U32.v (Ghost.reveal num_blocks) in
     let mask   = buffer_to_quad32       mask_b h in
     let plain  = buffer_to_seq_quad32  plain_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h in
     let key = Ghost.reveal key in
     let iv = Ghost.reveal iv in

     // gcm_body specific
     offset < num_blocks /\
     mask == aes_encrypt_LE AES_128 key (inc32 iv offset) /\
     gctr_partial AES_128 offset plain cipher key iv
    )
  )
  (ensures fun h () h' -> 
    let mods = M.loc_buffer cipher_b in
    M.modifies mods h h' /\
    B.live h plain_b /\ B.live h mask_b /\ B.live h cipher_b /\
    (let offset = U32.v offset in
     let num_blocks = U32.v (Ghost.reveal num_blocks) in
     let mask   = buffer_to_quad32       mask_b h in
     let plain  = buffer_to_seq_quad32  plain_b h' in
     let old_cipher = buffer_to_seq_quad32 cipher_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h' in
     let key = Ghost.reveal key in
     let iv = Ghost.reveal iv in
     gctr_partial AES_128 (offset + 1) plain cipher key iv /\
     slice cipher 0 offset == slice old_cipher 0 offset  // We didn't disrupt earlier slots
    ) /\
  True) 

assume val inc32_buffer (iv_b:B.buffer U8.t) : Stack unit
  (requires fun h ->
    B.live h iv_b /\
    B.length iv_b == 16
  )
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer iv_b) h h' /\
    (let old_iv = buffer_to_quad32 iv_b h  in
     let new_iv = buffer_to_quad32 iv_b h' in
     new_iv == inc32 old_iv 1))

(*** Actual Low* code ***)

let inc32_twice (q:quad32) (i:int) :
  Lemma (inc32 (inc32 q i) 1 == inc32 q (i + 1))
  =
  ()

#reset-options "--z3rlimit 30"
let gcm128_one_pass_blocks 
             (plain_b:B.buffer U8.t) (num_blocks:U32.t)  
             (iv_b:B.buffer U8.t) 
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
             (h_b hash_b:B.buffer U8.t) 
           : Stack unit
  (requires fun h ->
    let mods = M.(loc_union (loc_buffer cipher_b) 
                 (loc_union (loc_buffer iv_b) 
                            (loc_buffer hash_b))) in  
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    B.live h h_b /\ B.live h hash_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer keys_b)  mods /\
    M.loc_disjoint (M.loc_buffer h_b)  mods /\
    M.(loc_disjoint (loc_buffer cipher_b) (loc_buffer   iv_b)) /\
    M.(loc_disjoint (loc_buffer cipher_b) (loc_buffer hash_b)) /\ 
    M.(loc_disjoint (loc_buffer iv_b)     (loc_buffer hash_b)) /\
    B.length plain_b  >= U32.v num_blocks * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length h_b == 16 /\
    B.length hash_b == 16 /\
    B.length plain_b % 16 == 0 /\
    
    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h
  )
  (ensures fun h () h' -> 
    let mods = M.(loc_union (loc_buffer cipher_b) 
                 (loc_union (loc_buffer iv_b) 
                            (loc_buffer hash_b))) in
    M.modifies mods h h' /\
    B.live h' plain_b /\ B.live h' iv_b /\ B.live h' keys_b /\ B.live h' cipher_b /\
    B.live h' h_b /\ B.live h' hash_b /\ 
    (let num_blocks = U32.v num_blocks in
      gctr_partial AES_128 num_blocks (buffer_to_seq_quad32 plain_b h') (buffer_to_seq_quad32 cipher_b h') (Ghost.reveal key) (buffer_to_quad32 iv_b h) /\
      buffer_to_quad32 iv_b h' == inc32 (buffer_to_quad32 iv_b h) num_blocks /\
      (let old_hash = buffer_to_quad32 hash_b h in
       let new_hash = buffer_to_quad32 hash_b h' in
       let h_val = buffer_to_quad32 h_b h in
       (num_blocks == 0 ==> old_hash == new_hash) /\
       (num_blocks > 0 ==> 
         (let out_s = buffer_to_seq_quad32 cipher_b h' in
           length out_s > 0 /\
           new_hash == ghash_incremental h_val old_hash (slice out_s 0 num_blocks)
         )
       )
      )
    )
  ) 
  =
  push_frame();
  let h0 = ST.get() in
  let enc_ctr_b = B.alloca 0uy 16ul in
  let inv h (i:nat) =
    i <= U32.v num_blocks /\
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    B.live h h_b /\ B.live h hash_b /\
    B.live h enc_ctr_b /\
    (let mods = M.(loc_union (loc_buffer cipher_b) 
                  (loc_union (loc_buffer iv_b) 
                  (loc_union (loc_buffer enc_ctr_b)
                             (loc_buffer hash_b)))) in 
                            
    M.modifies mods h0 h) /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h /\

    // Interesting loop invariants
    (let old_iv = buffer_to_quad32 iv_b h0 in
     let new_iv = buffer_to_quad32 iv_b h in
     let plain  = buffer_to_seq_quad32  plain_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h in
     let old_hash = buffer_to_quad32 hash_b h0 in
     let new_hash = buffer_to_quad32 hash_b h in
     let h_val = buffer_to_quad32 h_b h in
     let key = Ghost.reveal key in
     new_iv == inc32 old_iv i /\
     gctr_partial AES_128 i plain cipher key old_iv /\
     (i == 0 ==> new_hash == old_hash) /\
     (i  > 0 ==> new_hash == ghash_incremental h_val old_hash (slice cipher 0 i))     
    )
  in
  (* This is the preferred style and useful for debugging the body.
     However, there's a "unification/delta_depth issue" somewhere, so we have to inline it below
  let body (i:U32.t{ U32.v 0ul <= U32.v i /\ U32.v i < U32.v num_blocks }) : Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h () h' -> inv h (U32.v i) /\ inv h' (U32.v i + 1)))
    =
    // Compute the encryption of the counter value
    aes128_encrypt_block_buffer iv_b enc_ctr_b key keys_b;
    
    // Xor the encrypted counter to the plaintext, to make progress on the gctr computation
    let iv = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
    gcm_load_xor_store_buffer plain_b enc_ctr_b cipher_b i (Ghost.hide num_blocks) key iv;
    
    // Update our hash (TODO: unify 32 vs 64 and remove this cast)
    let i32:nat32 = UInt32.v i in
    let i64:UInt64.t = UInt64.uint_to_t i32 in
    ghash_incremental_one_block_buffer h_b hash_b cipher_b i64;
    Opaque_s.reveal_opaque ghash_incremental_def;

    // Increment the ctr
    inc32_buffer iv_b;
    ()
  in
  *)
  C.Loops.for 0ul num_blocks inv 
    (fun (i:U32.t{ U32.v 0ul <= U32.v i /\ U32.v i < U32.v num_blocks }) ->
      // Compute the encryption of the counter value
      aes128_encrypt_block_buffer iv_b enc_ctr_b key keys_b;
      
      // Xor the encrypted counter to the plaintext, to make progress on the gctr computation
      let iv = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
      gcm_load_xor_store_buffer plain_b enc_ctr_b cipher_b i (Ghost.hide num_blocks) key iv;
      
      // Update our hash (TODO: unify 32 vs 64 and remove this cast)
      let i32:nat32 = UInt32.v i in
      let i64:UInt64.t = UInt64.uint_to_t i32 in
      ghash_incremental_one_block_buffer h_b hash_b cipher_b i64;
      Opaque_s.reveal_opaque ghash_incremental_def;

      // Increment the ctr
      inc32_buffer iv_b;
      ()
    )
  ;
  pop_frame();
  ()

#reset-options "--z3rlimit 20"
let gcm128_one_pass
             (plain_b:B.buffer U8.t) (num_bytes:U32.t)  
             (iv_b:B.buffer U8.t) 
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
             (h_b hash_b:B.buffer U8.t) 
           : Stack unit
  (requires fun h ->
    let mods = M.(loc_union (loc_buffer cipher_b) 
                 (loc_union (loc_buffer iv_b) 
                            (loc_buffer hash_b))) in 
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    B.live h h_b /\ B.live h hash_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer keys_b)  mods /\
    M.loc_disjoint (M.loc_buffer h_b)     mods /\ 
    
    M.(loc_disjoint (loc_buffer iv_b) (loc_buffer cipher_b)) /\
    M.(loc_disjoint (loc_buffer hash_b) (loc_buffer cipher_b)) /\
    M.(loc_disjoint (loc_buffer hash_b) (loc_buffer iv_b)) /\
    
    B.length plain_b  == bytes_to_quad_size (U32.v num_bytes) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length h_b == 16 /\
    B.length hash_b == 16 /\
    B.length plain_b % 16 == 0 /\

    4096 * (U32.v num_bytes) < pow2_32 /\
    256 * bytes_to_quad_size (U32.v num_bytes) < pow2_32 /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h
  )
  (ensures fun h () h' ->
    let mods = M.(loc_union (loc_buffer cipher_b) 
                 (loc_union (loc_buffer iv_b) 
                            (loc_buffer hash_b))) in
    M.modifies mods h h' /\
    // REVIEW: Do we really need to relist all of these liveness predicates?
    B.live h' plain_b /\ B.live h' iv_b /\ B.live h' keys_b /\ B.live h' cipher_b /\
    B.live h' h_b /\ B.live h' hash_b /\
    (let num_bytes = U32.v num_bytes in
     let iv_old = buffer_to_quad32 iv_b h in
     let iv_new = buffer_to_quad32 iv_b h' in
     let old_hash = buffer_to_quad32 hash_b h in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     // GCTR
     let plain  = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 num_bytes in
     let cipher = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 num_bytes in     
     cipher == gctr_encrypt_LE iv_old (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key) /\

     iv_new.lo1 == iv_old.lo1 /\
     iv_new.hi2 == iv_old.hi2 /\
     iv_new.hi3 == iv_old.hi3 /\     

     // GHash
     (num_bytes == 0 ==> old_hash == new_hash) /\
     (let cipher_padded_bytes = pad_to_128_bits cipher in
      let cipher_padded_quads = le_bytes_to_seq_quad32 cipher_padded_bytes in
      (num_bytes > 0 ==> 
        length cipher_padded_quads > 0 /\ 
        new_hash == ghash_incremental h_val old_hash cipher_padded_quads
      )
    )
   ) /\
  True) 
  =
  let h0 = ST.get() in
  if U32.v num_bytes > 0 then (
    let num_blocks = U32.div num_bytes 16ul in
    let num_extra = U32.rem num_bytes 16ul in
    gcm128_one_pass_blocks plain_b num_blocks iv_b key keys_b cipher_b h_b hash_b;
    let h1 = ST.get() in
    //assert (gctr_partial AES_128 (U32.v num_blocks) (buffer_to_seq_quad32 plain_b h1) (buffer_to_seq_quad32 cipher_b h1) (Ghost.reveal key) (buffer_to_quad32 iv_b h0));
    (*
    assert (let c = buffer_to_seq_quad32 cipher_b h1 in
            (U32.v num_blocks) > 0 ==> length c > 0 /\       
            buffer_to_quad32 hash_b h1 == 
            ghash_incremental (buffer_to_quad32 h_b h0) 
                              (buffer_to_quad32 hash_b h0) 
                              (slice c 0 (U32.v num_blocks)));
    *)   
    if num_extra = 0ul then (   
      // No work to be done.  Just call a bunch of lemmas
        
      // From gctr_bytes_no_extra(), we get:
      gctr_partial_completed AES_128 
                             (buffer_to_seq_quad32 plain_b h1)
                             (buffer_to_seq_quad32 cipher_b h1)
                             (Ghost.reveal key)
                             (buffer_to_quad32 iv_b h0); 
      gctr_partial_to_full_basic (buffer_to_quad32 iv_b h0)  
                                 (buffer_to_seq_quad32 plain_b h1)
                                 AES_128
                                 (Ghost.reveal key)
                                 (buffer_to_seq_quad32 cipher_b h1);
      no_extra_bytes_helper (buffer_to_seq_quad32 plain_b h1) (U32.v num_bytes);
      no_extra_bytes_helper (buffer_to_seq_quad32 cipher_b h1) (U32.v num_bytes);  

      // From ghash_incremental_bytes_no_extra() we get the following,
      // after eliminating redundancies with lemma calls above):
      le_bytes_to_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h1);

      // From gcm_one_pass, we get:
      bytes_to_quad_size_no_extra_bytes (U32.v num_bytes);

      // Prove a property about le_bytes_to_seq_quad32 while trying to keep its definition hidden
      let length_helper (x:int) : Lemma (forall y . {:pattern length (le_bytes_to_seq_quad32 y)}
                                             length y > 0 ==> length (le_bytes_to_seq_quad32 y) > 0) =
        Opaque_s.reveal_opaque le_bytes_to_seq_quad32_def
      in
      length_helper 0;                            
      ()
    ) else (
      let iv_old = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
      let hash_old = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h0) in      
      gctr_bytes_extra_buffer plain_b num_bytes iv_old iv_b key keys_b cipher_b;
      ghash_incremental_bytes_extra_buffer cipher_b hash_b h_b num_bytes hash_old;    
      ()
    )    
  ) else (
    // Wow, this is a painful way to handle ghost values :(
    let plain  = Ghost.elift2 buffer_to_seq_quad32  (Ghost.hide plain_b)  (Ghost.hide h0) in
    let cipher = Ghost.elift2 buffer_to_seq_quad32  (Ghost.hide cipher_b) (Ghost.hide h0) in
    let old_iv = Ghost.elift2 buffer_to_quad32      (Ghost.hide iv_b)     (Ghost.hide h0) in 
    gctr_encrypt_empty (Ghost.reveal old_iv) 
                       (Ghost.reveal plain) 
                       (Ghost.reveal cipher) 
                       AES_128 
                       (Ghost.reveal key);
    ()
  );
  ()


assume val zero_quad32_buffer (b:B.buffer U8.t) : Stack unit
  (requires fun h ->
    B.live h b /\
    B.length b == 16
  )
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer b) h h' /\
    (let new_b = buffer_to_quad32 b h' in
     new_b == Mkfour 0 0 0 0)
  )

assume val mk_quad32_lo0_be_1_buffer (b:B.buffer U8.t) : Stack unit
  (requires fun h ->
    B.live h b /\
    B.length b == 16
  )
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer b) h h' /\
    (let old_b = buffer_to_quad32 b h  in
     let new_b = buffer_to_quad32 b h' in
     new_b == Mkfour 1 old_b.lo1 old_b.hi2 old_b.hi3)
  )

assume val gcm_make_length_quad_buffer 
  (plain_num_bytes auth_num_bytes:U64.t)
  (b:B.buffer U8.t)
  : Stack unit
  (requires fun h ->
    B.live h b /\
    B.length b == 16 /\
    8 * (U64.v plain_num_bytes) < pow2_32 /\
    8 * (U64.v  auth_num_bytes) < pow2_32
  )
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer b) h h' /\
    (let new_b = buffer_to_quad32 b h' in
     new_b == Mkfour (8 * (U64.v plain_num_bytes)) 0 (8 * (U64.v auth_num_bytes)) 0)
  )


assume val quad32_xor_buffer 
  (src1 src2 dst:B.buffer U8.t)
  : Stack unit
  (requires fun h ->
    B.live h src1 /\ B.live h src2 /\ B.live h dst /\
    B.length src1 == 16 /\ B.length src2 == 16 /\ B.length dst == 16
  )
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer dst) h h' /\
    (let src1 = buffer_to_quad32 src1 h  in
     let src2 = buffer_to_quad32 src2 h  in
     let dst  = buffer_to_quad32 dst  h' in
     dst = quad32_xor src1 src2)
  )

let gcm_core_part1      
    (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t) 
    (auth_b:B.buffer U8.t)  (auth_num_bytes:U64.t)
    (iv_b:B.buffer U8.t) 
    (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
    (cipher_b:B.buffer U8.t)
    (h_b hash_b:B.buffer U8.t)
    : ST (Ghost.erased quad32x3)
  (requires fun h -> 
      let mods = M.((loc_union (loc_buffer cipher_b) 
                    (loc_union (loc_buffer iv_b)
                    (loc_union (loc_buffer h_b)
                               (loc_buffer hash_b))))) in 
      B.live h plain_b /\ B.live h auth_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
      B.live h h_b /\ B.live h hash_b /\
      
      M.loc_disjoint (M.loc_buffer plain_b) mods /\
      M.loc_disjoint (M.loc_buffer auth_b) mods /\
      M.loc_disjoint (M.loc_buffer keys_b)  mods /\
            
      M.(loc_disjoint (loc_buffer iv_b) (loc_buffer cipher_b)) /\
      M.(loc_disjoint (loc_buffer hash_b) (loc_buffer cipher_b)) /\
      M.(loc_disjoint (loc_buffer hash_b) (loc_buffer iv_b)) /\
      M.(loc_disjoint (loc_buffer h_b) (loc_buffer iv_b)) /\
      M.(loc_disjoint (loc_buffer h_b) (loc_buffer cipher_b)) /\
      M.(loc_disjoint (loc_buffer h_b) (loc_buffer hash_b)) /\
      
      B.length plain_b  == bytes_to_quad_size (U64.v plain_num_bytes) * 16 /\
      B.length auth_b   == bytes_to_quad_size (U64.v auth_num_bytes) * 16 /\
      B.length cipher_b == B.length plain_b /\
      B.length iv_b     == 16 /\
      B.length h_b == 16 /\
      B.length hash_b == 16 /\

      4096 * (U64.v plain_num_bytes) < pow2_32 /\
      4096 * (U64.v auth_num_bytes)  < pow2_32 /\
      256 * bytes_to_quad_size (U64.v plain_num_bytes) < pow2_32 /\
      256 * bytes_to_quad_size (U64.v auth_num_bytes)  < pow2_32 /\

      // AES reqs
      B.length keys_b == (nr AES_128 + 1) * 16 /\
      B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
      keys_match key keys_b h            
  )
  (ensures fun h q3 h' -> 
    let mods = M.((loc_union (loc_buffer cipher_b) 
                    (loc_union (loc_buffer iv_b)
                    (loc_union (loc_buffer h_b)
                               (loc_buffer hash_b))))) in 
    B.live h plain_b /\ B.live h auth_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    B.live h h_b /\ B.live h hash_b /\
      
    M.modifies mods h h' /\
    
    (let plain_num_bytes = U64.v plain_num_bytes in
     let auth_num_bytes = U64.v auth_num_bytes in
     let iv_old = buffer_to_quad32 iv_b h in
     let iv_new = buffer_to_quad32 iv_b h' in
     let old_hash = buffer_to_quad32 hash_b h in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h' in
     let auth   = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32   auth_b h))  0 auth_num_bytes in
     let plain  = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 plain_num_bytes in
     let cipher = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 plain_num_bytes in 
     let (y_0, y_auth, y_cipher) = (Ghost.reveal q3) in
     let auth_padded_bytes = pad_to_128_bits auth in
     let auth_padded_quads = le_bytes_to_seq_quad32 auth_padded_bytes in
     let cipher_padded_bytes = pad_to_128_bits cipher in
     let cipher_padded_quads = le_bytes_to_seq_quad32 cipher_padded_bytes in
        
     // GCTR 
     let k = seq_nat32_to_seq_nat8_LE (Ghost.reveal key) in
     cipher == fst (gcm_encrypt_LE AES_128 k (be_quad32_to_bytes iv_old) plain auth) /\

     // Intermediate hash state needed for the next step
     y_0      == Mkfour 0 0 0 0 /\
     y_auth   == ghash_incremental0 h_val y_0    auth_padded_quads /\
     y_cipher == ghash_incremental0 h_val y_auth cipher_padded_quads /\
     new_hash == y_cipher /\     
     h_val == aes_encrypt_LE AES_128 (Ghost.reveal key) y_0 /\

     // Intermediate IV state
     iv_new.lo1 == iv_old.lo1 /\
     iv_new.hi2 == iv_old.hi2 /\
     iv_new.hi3 == iv_old.hi3 /\     
    True)
  )
  =
  let h0 = ST.get() in
  let iv_BE = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
  push_frame ();
  zero_quad32_buffer h_b;
  zero_quad32_buffer hash_b;
  aes128_encrypt_block_buffer h_b h_b key keys_b;  // h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) 
  let h1 = ST.get() in
  let y_0 = Ghost.hide (Mkfour 0 0 0 0) in
  ghash_incremental_bytes_buffer h_b hash_b auth_b auth_num_bytes;
  let h2 = ST.get() in

  let y_auth = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h2) in
  mk_quad32_lo0_be_1_buffer iv_b;
  inc32_buffer iv_b;  // iv_b == old(iv_b)[lo0 := 2]
  let h3 = ST.get() in

  let icb_enc = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h3) in
  let plain_num_bytes_nat64:nat64 = U64.v plain_num_bytes in
  let p_n = U32.uint_to_t plain_num_bytes_nat64 in
  gcm128_one_pass plain_b p_n iv_b key keys_b cipher_b h_b hash_b;
  let h4 = ST.get() in
  let y_cipher = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h4) in
  GCM_i.gcm_encrypt_LE_fst_helper 
    (Ghost.reveal icb_enc) 
    (Ghost.reveal iv_BE) 
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h0)) 0 plain_num_bytes_nat64)
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32   auth_b h0)) 0 (U64.v auth_num_bytes))
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h4)) 0 plain_num_bytes_nat64)
    AES_128
    (Ghost.reveal key);
  Opaque_s.reveal_opaque le_bytes_to_seq_quad32_def; 
  pop_frame();
  Ghost.hide (Ghost.reveal y_0, Ghost.reveal y_auth, Ghost.reveal y_cipher)  

(*
#reset-options "--z3rlimit 20"
let gcm_core      
    (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t) 
    (auth_b:B.buffer U8.t)  (auth_num_bytes:U64.t)
    (iv_b:B.buffer U8.t) 
    (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
    (cipher_b:B.buffer U8.t)
    (tag_b:B.buffer U8.t) : ST unit
  (requires fun h -> 
      let mods = M.((loc_union (loc_buffer cipher_b) (loc_buffer iv_b))) in 
      B.live h plain_b /\ B.live h auth_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
      M.loc_disjoint (M.loc_buffer plain_b) mods /\
      M.loc_disjoint (M.loc_buffer keys_b)  mods /\
      M.(loc_disjoint (loc_buffer iv_b) (loc_buffer cipher_b)) /\
      
      B.length plain_b  == bytes_to_quad_size (U64.v plain_num_bytes) * 16 /\
      B.length auth_b   == bytes_to_quad_size (U64.v auth_num_bytes) * 16 /\
      B.length cipher_b == B.length plain_b /\
      B.length iv_b     == 16 /\

      4096 * (U64.v plain_num_bytes) < pow2_32 /\
      4096 * (U64.v auth_num_bytes)  < pow2_32 /\
      256 * bytes_to_quad_size (U64.v plain_num_bytes) < pow2_32 /\
      256 * bytes_to_quad_size (U64.v auth_num_bytes)  < pow2_32 /\

      // AES reqs
      B.length keys_b == (nr AES_128 + 1) * 16 /\
      B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
      (let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
       let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
       BV.as_seq h keys128_b == round_keys /\
       True) /\                    
      True                   
  )
  (ensures fun h () h' -> 
    h' `B.live` cipher_b /\
    h' `B.live` tag_b /\
    M.modifies (M.loc_union (M.loc_buffer cipher_b) (M.loc_buffer tag_b)) h h' /\  
    (let auth  = seq_U8_to_seq_nat8 (slice (B.as_seq h auth_b) 0 (U64.v auth_num_bytes)) in
     let plain = seq_U8_to_seq_nat8 (slice (B.as_seq h plain_b) 0 (U64.v plain_num_bytes)) in
     let cipher = seq_U8_to_seq_nat8 (slice (B.as_seq h' cipher_b) 0 (U64.v plain_num_bytes)) in 
     B.length iv_b % 16 == 0 /\
     B.length tag_b % 16 == 0 /\
     4096 * length plain < pow2_32 /\
     4096 * length auth < pow2_32 /\     
     (let iv128_b  = BV.mk_buffer_view iv_b  Views.view128 in
      let tag128_b = BV.mk_buffer_view tag_b Views.view128 in
      BV.length iv128_b  > 0 /\
      BV.length tag128_b > 0 /\
      (let iv_BE = reverse_bytes_quad32 (index (BV.as_seq h iv128_b) 0) in
       let tag = index (BV.as_seq h' tag128_b) 0 in // TODO: Should be able to simplify this to the original bytes
       let c,t = gcm_encrypt_LE AES_128 
                                (seq_nat32_to_seq_nat8_LE (Ghost.reveal key))
                                (be_quad32_to_bytes iv_BE)
                                plain
                                auth in
       cipher == c /\
       le_quad32_to_bytes tag == t                                                     
     )
    )
   ) 
  )
  =
  let h0 = ST.get() in
  let iv_BE = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
  push_frame ();
  let h_b = B.alloca 0uy 16ul in
  let hash_b = B.alloca 0uy 16ul in
  zero_quad32_buffer h_b;
  zero_quad32_buffer hash_b;
  aes128_encrypt_block_buffer h_b h_b key keys_b;  // h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) 
  let h1 = ST.get() in
  let y_0 = Ghost.hide (Mkfour 0 0 0 0) in
  ghash_incremental_bytes_buffer h_b hash_b auth_b auth_num_bytes;
  let h2 = ST.get() in
  let y_auth = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h2) in
  mk_quad32_lo0_be_1_buffer iv_b;
  inc32_buffer iv_b;  // iv_b == old(iv_b)[lo0 := 2]
  let h3 = ST.get() in
  let icb_enc = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h3) in
  let plain_num_bytes_nat64:nat64 = U64.v plain_num_bytes in
  let p_n = U32.uint_to_t plain_num_bytes_nat64 in
  gcm128_one_pass plain_b p_n iv_b key keys_b cipher_b h_b hash_b;
  let h4 = ST.get() in
  let y_cipher = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h4) in
  GCM_i.gcm_encrypt_LE_fst_helper 
    (Ghost.reveal icb_enc) 
    (Ghost.reveal iv_BE) 
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h0)) 0 plain_num_bytes_nat64)
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32   auth_b h0)) 0 (U64.v auth_num_bytes))
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h4)) 0 plain_num_bytes_nat64)
    AES_128
    (Ghost.reveal key);
  Opaque_s.reveal_opaque le_bytes_to_seq_quad32_def;  // REVIEW: Save for later?

  let length_quad_b = B.alloca 0uy 16ul in
  gcm_make_length_quad_buffer plain_num_bytes auth_num_bytes length_quad_b;
  ghash_incremental_one_block_buffer h_b hash_b length_quad_b 0UL;
  let h5 = ST.get() in
  let y_final = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h5) in

  // Invoke lemma showing that incremental hashing works
  lemma_hash_append3 
    (buffer_to_quad32 h_b h1)
    (Ghost.reveal y_0)
    (Ghost.reveal y_auth)
    (Ghost.reveal y_cipher)
    (Ghost.reveal y_final)
    (let auth_bytes = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 auth_b h0)) 0 (U64.v auth_num_bytes) in
     let auth_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits auth_bytes) in
     auth_padded_quads)
    (let cipher_bytes = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h5)) 0 (U64.v plain_num_bytes) in
     let cipher_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes) in
     cipher_padded_quads)
    (create 1 (buffer_to_quad32 length_quad_b h5));
     

    (*
    ghost var auth_bytes := slice_work_around(le_seq_quad32_to_bytes(buffer128_as_seq(old(mem), auth_b)), old(auth_num_bytes));
    ghost var auth_padded_quads := le_bytes_to_seq_quad32(pad_to_128_bits(auth_bytes));

    ghost var cipher := slice_work_around(le_seq_quad32_to_bytes(buffer128_as_seq(mem, out_b)), old(plain_num_bytes));
    ghost var cipher_padded_quads := le_bytes_to_seq_quad32(pad_to_128_bits(cipher));
    lemma_hash_append3(h, y_0, y_auth, y_cipher, y_final,
                       auth_padded_quads, //buffer128_as_seq(mem, auth_b),
                       cipher_padded_quads, //buffer128_as_seq(mem, out_b),
                       create(1, length_quad32)); 
  *)
  
  (*
  mk_quad32_lo0_be_1_buffer iv_b;
  
  aes128_encrypt_block_buffer iv_b iv_b key keys_b;
  quad32_xor_buffer hash_b iv_b tag_b;
  // Call lemma: gctr_encrypt_one_block(icb_BE, old(io), alg, key) ?

  // Call: le_seq_quad32_to_bytes_of_singleton(xmm1);

  
  (*
  let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in

  let encrypted_ctr = aes128_encrypt_block j0_BE key keys_b in
  let tag = quad32_xor encrypted_ctr y_final in
  // Call more lemmas here
  *)
  *)
  admit();
  pop_frame();
  ()  
*)

(*
let gcm128_encrypt (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t) 
                   (auth_b:B.buffer U8.t)  (auth_num_bytes:U64.t)
                   (iv_b:B.buffer U8.t) 
                   (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
                   (cipher_b:B.buffer U8.t)
                   (tag_b:B.buffer U8.t) : ST unit
  (requires fun h ->  h `B.live` plain_b /\
                   h `B.live` auth_b /\
                   h `B.live` keys_b /\
                   h `B.live` cipher_b /\
                   h `B.live` tag_b /\
                   
                   M.loc_disjoint (M.loc_buffer plain_b) (M.loc_buffer cipher_b) /\
                   M.loc_disjoint (M.loc_buffer auth_b)  (M.loc_buffer cipher_b) /\
                   M.loc_disjoint (M.loc_buffer keys_b)  (M.loc_buffer cipher_b) /\
                   M.loc_disjoint (M.loc_buffer tag_b)   (M.loc_buffer cipher_b) /\
                   B.length plain_b  == bytes_to_quad_size (U64.v plain_num_bytes) * 16 /\
                   B.length auth_b   == bytes_to_quad_size (U64.v auth_num_bytes) * 16 /\
                   B.length cipher_b == B.length plain_b /\
                   B.length iv_b     == 16 /\

                   // TODO: Unclear how to translate the following.  Should be derived from interop addr_map
                   //plain_ptr + 16 * bytes_to_quad_size(plain_num_bytes) < pow2_64;
                   //auth_ptr  + 16 * bytes_to_quad_size(auth_num_bytes)  < pow2_64;
                   //out_ptr   + 16 * bytes_to_quad_size(plain_num_bytes) < pow2_64;

                   //256 * B.length plain < pow2_32 /\
                   4096 * (U64.v plain_num_bytes) < pow2_32 /\
                   4096 * (U64.v auth_num_bytes)  < pow2_32 /\
                   256 * bytes_to_quad_size (U64.v plain_num_bytes) < pow2_32 /\
                   256 * bytes_to_quad_size (U64.v auth_num_bytes)  < pow2_32 /\

                   // AES reqs
                   B.length keys_b == (nr AES_128 + 1) * 16 /\
                   B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
                   (let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
                    let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
                    BV.as_seq h keys128_b == round_keys /\
                    True) /\                    
                   True                   
  )
  (ensures fun h () h' -> 
    h' `B.live` cipher_b /\
    h' `B.live` tag_b /\
    M.modifies (M.loc_union (M.loc_buffer cipher_b) (M.loc_buffer tag_b)) h h' /\  
    (let auth  = seq_U8_to_seq_nat8 (slice (B.as_seq h auth_b) 0 (U64.v auth_num_bytes)) in
     let plain = seq_U8_to_seq_nat8 (slice (B.as_seq h plain_b) 0 (U64.v plain_num_bytes)) in
     let cipher = seq_U8_to_seq_nat8 (slice (B.as_seq h' cipher_b) 0 (U64.v plain_num_bytes)) in 
     B.length iv_b % 16 == 0 /\
     B.length tag_b % 16 == 0 /\
     4096 * length plain < pow2_32 /\
     4096 * length auth < pow2_32 /\     
     (let iv128_b  = BV.mk_buffer_view iv_b  Views.view128 in
      let tag128_b = BV.mk_buffer_view tag_b Views.view128 in
      BV.length iv128_b  > 0 /\
      BV.length tag128_b > 0 /\
      (let iv_BE = reverse_bytes_quad32 (index (BV.as_seq h iv128_b) 0) in
       let tag = index (BV.as_seq h' tag128_b) 0 in // TODO: Should be able to simplify this to the original bytes
       let c,t = gcm_encrypt_LE AES_128 
                                (seq_nat32_to_seq_nat8_LE (Ghost.reveal key))
                                (be_quad32_to_bytes iv_BE)
                                plain
                                auth in
       cipher == c /\
       le_quad32_to_bytes tag == t                                                     
     )
    )
   ) 
  )
  =
  // TODO: Call stub generated by Aymeric's interop
  admit()

*)
