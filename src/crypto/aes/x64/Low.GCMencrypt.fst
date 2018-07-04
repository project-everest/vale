module Low.GCMencrypt

open FStar.HyperStack.ST

module B = LowStar.Buffer
module BV = LowStar.BufferView
module M = LowStar.Modifies
open LowStar.ModifiesPat
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module HST = FStar.HyperStack.ST

open Types_s
open Types_i
open Words_s
open Words.Seq_s
open AES_s
open GCM_s
open GCM_helpers_i
open X64.Memory_i_s
open FStar.Seq

let test (x:int) (y:int) : ST unit 
  (requires fun h0 -> True)
  (ensures fun h0 () h1 -> True)
  =
  push_frame ();
  pop_frame();
  ()

open FStar.Mul

let seq_U8_to_seq_nat8 (b:seq U8.t) : (seq nat8) =
  Seq.init (length b) (fun (i:nat { i < length b }) -> U8.v (index b i))

assume val aes128_encrypt_block (input:quad32) 
                                (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
                              : Stack quad32 
  (requires fun h -> True)
  (ensures fun h output h' -> True)                            

assume val ghash_incremental_bytes (h old_hash:quad32) (input_b:B.buffer U8.t) (num_bytes:U64.t) : Stack quad32
  (requires fun h -> True)
  (ensures fun h new_hash h' -> True) 

assume val gcm128_one_pass 
             (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t)              
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
             (old_hash iv_BE:quad32) 
           : Stack quad32
  (requires fun h -> True)
  (ensures fun h new_hash h' -> True) 

assume val quad32_to_buffer (q:quad32) (b:B.buffer U8.t) : Stack unit
  (requires fun h -> True)
  (ensures fun h () h' -> True)

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
