module Low.GCMencrypt

open FStar.HyperStack.ST

module B = LowStar.Buffer
module M = LowStar.Modifies
open LowStar.ModifiesPat
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module HST = FStar.HyperStack.ST

open Types_s
open Words_s
open GCM_helpers_i

let test (x:int) (y:int) : ST unit 
  (requires fun h0 -> True)
  (ensures fun h0 () h1 -> True)
  =
  push_frame ();
  pop_frame();
  ()

open FStar.Mul

let gcm128_encrypt (plain:B.buffer U8.t) (plain_num_bytes:U64.t) 
                   (auth:B.buffer U8.t)  (auth_num_bytes:U64.t)
                   (iv:quad32) 
                   (keys:B.buffer U8.t)
                   (cipher:B.buffer U8.t)
                   (tag:B.buffer U8.t) : ST unit
  (requires fun h ->  h `B.live` plain /\
                   h `B.live` auth /\
                   h `B.live` keys /\
                   h `B.live` cipher /\
                   h `B.live` tag /\
                   M.loc_disjoint (M.loc_buffer plain) (M.loc_buffer cipher) /\
                   M.loc_disjoint (M.loc_buffer auth)  (M.loc_buffer cipher) /\
                   M.loc_disjoint (M.loc_buffer keys)  (M.loc_buffer cipher) /\
                   M.loc_disjoint (M.loc_buffer tag)   (M.loc_buffer cipher) /\
                   B.length plain  == bytes_to_quad_size (U64.v plain_num_bytes) /\
                   B.length auth   == bytes_to_quad_size (U64.v auth_num_bytes) /\
                   B.length cipher == B.length plain /\
                   256 * B.length plain < pow2_32 /\
                   4096 * (U64.v plain_num_bytes) < pow2_32 /\
                   4096 * (U64.v auth_num_bytes)  < pow2_32 /\
                   256 * bytes_to_quad_size (U64.v plain_num_bytes) < pow2_32 /\
                   256 * bytes_to_quad_size (U64.v auth_num_bytes)  < pow2_32 /\
                   B.length keys >= 11 /\
                   // TODO: Other AES key requirements here
                   True
                   
                   
  )
  (ensures fun h () h' -> 
    h' `B.live` cipher /\
    h' `B.live` tag /\
    M.modifies (M.loc_union (M.loc_buffer cipher) (M.loc_buffer tag)) h h' /\   
  True)
  =
  ()
