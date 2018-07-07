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
     let cipher = buffer_to_seq_quad32 cipher_b h' in
     let key = Ghost.reveal key in
     let iv = Ghost.reveal iv in
     gctr_partial AES_128 (offset + 1) plain cipher key (inc32 iv (offset + 1))
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
    ) /\
  True) 
  =
  push_frame();
//  let ctr_b = B.alloca 0uy 16ul in
  let enc_ctr_b = B.alloca 0uy 16ul in
//  memcpy_simple iv_b ctr_b 16ul;
  let h0 = ST.get() in
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
     let key = Ghost.reveal key in
     new_iv == inc32 old_iv i /\
     gctr_partial AES_128 i plain cipher key old_iv
    )
  in
  let body (i:U32.t{ U32.v 0ul <= U32.v i /\ U32.v i < U32.v num_blocks }) : Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h () h' -> inv h (U32.v i) /\ inv h (U32.v i + 1)))
    =
    aes128_encrypt_block_buffer iv_b enc_ctr_b key keys_b;
    let h1 = ST.get() in
    let iv = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
    gcm_load_xor_store_buffer plain_b enc_ctr_b cipher_b i (Ghost.hide num_blocks) key iv;

    // Update our hash
    //ghash_incremental_bytes_buffer h_b hash_b cipher_b

    // Increment the ctr
    inc32_buffer iv_b;
    admit();
    ()
  in
  //C.Loops.for 0ul num_blocks inv body;
  pop_frame();
  admit();
  ()

(*
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
    M.loc_disjoint (M.loc_buffer hash_b)  mods /\    
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

(*
let gcm_core (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t) 
             (auth_b:B.buffer U8.t)  (auth_num_bytes:U64.t)
             (iv_BE:quad32) 
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
             (tag_b:B.buffer U8.t) : Stack unit
  (requires fun h -> 
    4096 * (U64.v plain_num_bytes) < pow2_32 /\
    4096 * (U64.v auth_num_bytes)  < pow2_32 /\
    True)
  (ensures fun h () h' -> True)
  =
  push_frame ();
  let quad32_zero = Mkfour 0 0 0 0 in
  let h = aes128_encrypt_block quad32_zero key keys_b in
  (*
  let iv_be = reverse_bytes_quad32 iv in
  let iv_be = four_insert iv_be 2 0 in
  *) 
  let y_0 = quad32_zero in 
  let y_auth = ghash_incremental_bytes h y_0 auth_b auth_num_bytes in
  let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
  let j0_inc32_BE = Mkfour 2 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
  let y_cipher = gcm128_one_pass plain_b plain_num_bytes key keys_b cipher_b y_auth j0_inc32_BE in
  // Call some lemmas here
  let length_quad = Mkfour (8 * UInt64.v plain_num_bytes) 0 (8 * UInt64.v auth_num_bytes) 0 in
  let length_quad_b = B.alloca 0uy 16ul in
  quad32_to_buffer length_quad length_quad_b;
  let y_final = ghash_incremental_bytes h y_cipher length_quad_b 16UL in
  let encrypted_ctr = aes128_encrypt_block j0_BE key keys_b in
  let tag = quad32_xor encrypted_ctr y_final in
  quad32_to_buffer tag tag_b;  
  // Call more lemmas here
  pop_frame();
  ()  
*)

let gcm128_encrypt (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t) 
                   (auth_b:B.buffer U8.t)  (auth_num_bytes:U64.t)
                   (iv_b:B.buffer U8.t) 
                   (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
                   (cipher_b:B.buffer U8.t)
f                   (tag_b:B.buffer U8.t) : ST unit
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
