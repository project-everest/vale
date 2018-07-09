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

open FStar.Mul

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (plain_b:b8) (plain_num_bytes:nat64) (auth_b:b8) (auth_num_bytes:nat64) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) (tag_b:b8) =
   B.length plain_b % 16 == 0 /\ B.length auth_b % 16 == 0 /\ B.length iv_b % 16 == 0 /\ B.length keys_b % 16 == 0 /\ B.length cipher_b % 16 == 0 /\ B.length tag_b % 16 == 0 /\
live h plain_b /\ live h auth_b /\ live h iv_b /\ live h keys_b /\ live h cipher_b /\ live h tag_b /\ locs_disjoint [plain_b;auth_b;iv_b;keys_b;cipher_b;tag_b] /\
                   B.length plain_b  == bytes_to_quad_size (plain_num_bytes) * 16 /\
                   B.length auth_b   == bytes_to_quad_size (auth_num_bytes) * 16 /\
                   B.length cipher_b == B.length plain_b /\
                   B.length iv_b     == 16 /\
		   B.length tag_b >= 1 /\

                   4096 * (plain_num_bytes) < pow2_32 /\
                   4096 * (auth_num_bytes)  < pow2_32 /\
                   256 * bytes_to_quad_size (plain_num_bytes) < pow2_32 /\
                   256 * bytes_to_quad_size (auth_num_bytes)  < pow2_32 /\

                   // AES reqs
                   B.length keys_b == (nr AES_128 + 1) * 16 /\
                   B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
                   (let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
                    let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
                    BV.as_seq h keys128_b == round_keys /\
                    True) /\                    
                   True    

noextract
let seq_U8_to_seq_nat8 (b:seq U8.t) : (s:seq nat8{length s == length b}) =
  Seq.init (length b) (fun (i:nat { i < length b }) -> let n:nat8 = U8.v (index b i) in n)

let post_cond (h0:HS.mem) (h1:HS.mem) (plain_b:b8) (plain_num_bytes:nat64) (auth_b:b8) (auth_num_bytes:nat64) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) (tag_b:b8) =    
    B.length plain_b % 16 == 0 /\ B.length auth_b % 16 == 0 /\ B.length iv_b % 16 == 0 /\ B.length keys_b % 16 == 0 /\ B.length cipher_b % 16 == 0 /\ B.length tag_b % 16 == 0 /\
    h1 `B.live` cipher_b /\
    h1 `B.live` tag_b /\
    B.length plain_b  == bytes_to_quad_size (plain_num_bytes) * 16 /\
    B.length auth_b   == bytes_to_quad_size (auth_num_bytes) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b     == 16 /\

    (let auth  = seq_U8_to_seq_nat8 (slice (B.as_seq h0 auth_b) 0 auth_num_bytes) in
     let plain = seq_U8_to_seq_nat8 (slice (B.as_seq h0 plain_b) 0 plain_num_bytes) in
     let cipher = seq_U8_to_seq_nat8 (slice (B.as_seq h1 cipher_b) 0 plain_num_bytes) in 
     B.length iv_b % 16 == 0 /\
     B.length tag_b % 16 == 0
     /\
     4096 * length plain < pow2_32 /\
     4096 * length auth < pow2_32 /\
     (let iv128_b  = BV.mk_buffer_view iv_b  Views.view128 in
      let tag128_b = BV.mk_buffer_view tag_b Views.view128 in
      BV.length iv128_b  > 0 /\
      BV.length tag128_b > 0 /\
      (let iv_BE = reverse_bytes_quad32 (index (BV.as_seq h0 iv128_b) 0) in
       let tag = index (BV.as_seq h1 tag128_b) 0 in // TODO: Should be able to simplify this to the original bytes
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


val gcmencrypt: plain_b:b8 -> plain_num_bytes:UInt64.t -> auth_b:b8 -> auth_num_bytes:UInt64.t -> iv_b:b8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:b8 -> cipher_b:b8 -> tag_b:b8 -> Stack unit
	(requires (fun h -> pre_cond h plain_b (UInt64.v plain_num_bytes) auth_b (UInt64.v auth_num_bytes) iv_b key keys_b cipher_b tag_b ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 plain_b (UInt64.v plain_num_bytes) auth_b (UInt64.v auth_num_bytes) iv_b key keys_b cipher_b tag_b /\  M.modifies (M.loc_union (M.loc_buffer cipher_b) (M.loc_buffer tag_b)) h0 h1))
