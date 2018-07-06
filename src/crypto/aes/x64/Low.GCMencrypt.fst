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
module E = Kremlin.Endianness

open Types_s
open Types_i
open Words_s
open Words.Seq_s
open AES_s
open GCTR_s
open GCM_s
open GCM_helpers_i
open GHash_i
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

let buffer_to_nat32 (b:B.buffer U8.t { B.length b % 4 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot nat32 =
  let b32 = BV.mk_buffer_view b Views.view32 in
  BV.as_buffer_mk_buffer_view b Views.view32;
  BV.get_view_mk_buffer_view b Views.view32;
  BV.length_eq b32;
  //assert (B.length b >= 4);
  //assert (BV.length b32 > 0);
  U32.v (BV.sel h b32 0)
  //U32.v (index (BV.as_seq h b32) 0)

let buffer_to_quad (b:B.buffer U8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0
  //index (BV.as_seq h b128) 0

let buffer_to_seq_quad (b:B.buffer U8.t { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:seq quad32 {length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let nat32_to_buffer (n:nat32) (b:B.buffer U8.t { B.length b % 4 == 0 } ) : Stack unit
  (requires fun h -> B.live h b /\ B.length b == 4)
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer b) h h' /\
    buffer_to_nat32 b h' == n
  )
  =
  let original_n = n in
  B.upd b 0ul (U8.uint_to_t (n % 0x100));
  let n = n `op_Division` 0x100 in
  B.upd b 1ul (U8.uint_to_t (n % 0x100));
  let n = n `op_Division` 0x100 in
  B.upd b 2ul (U8.uint_to_t (n % 0x100));
  let n = n `op_Division` 0x100 in
  B.upd b 3ul (U8.uint_to_t (n % 0x100));
  let h = ST.get() in
  Opaque_s.reveal_opaque Views.put32_def;
  let b_s = B.as_seq h b in
  let v_s = (Views.put32 (U32.uint_to_t original_n)) in
  assert (equal b_s v_s);
  Views.inverses32();
  BV.as_buffer_mk_buffer_view b Views.view32;
  BV.get_view_mk_buffer_view b Views.view32;
  let b32 = BV.mk_buffer_view b Views.view32 in
  BV.length_eq b32;
  assert (BV.length b32 > 0);
  BV.get_sel h b32 0;
  ()

let nat32_from_buffer (b:B.buffer U8.t { B.length b % 4 == 0 }) : Stack nat32
  (requires fun h -> B.live h b /\ B.length b > 0)
  (ensures fun h n h' -> 
    M.modifies M.loc_none h h' /\
    n == buffer_to_nat32 b h
  )
  =
  admit()     // TODO

(*
let quad32_to_buffer' (q:quad32) (b:B.buffer U8.t { B.length b % 16 == 0 } ) : Stack unit
  (requires fun h -> B.live h b /\ B.length b == 16)
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer b) h h' /\
    buffer_to_quad b h' == q
  )
  =
  let lo0_b = B.sub b 0ul 4ul in
  nat32_to_buffer q.lo0 lo0_b;
  let lo1_b = B.sub b 4ul 4ul in
  nat32_to_buffer q.lo1 lo1_b;
  let hi2_b = B.sub b 8ul 4ul in
  nat32_to_buffer q.hi2 hi2_b;  
  let hi3_b = B.sub b 12ul 4ul in
  nat32_to_buffer q.hi3 hi3_b;  
  let h' = ST.get() in
  Opaque_s.reveal_opaque Views.put128_def;
  let p_s = Views.put128_def q in
  let v_s = B.as_seq h' b in
  assert (length p_s == length v_s);
  assert (equal p_s v_s);
  (*
  Views.inverses128();
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.length_eq b128;
  *)
  admit();
  ()
*)

let quad32_to_buffer (q:quad32) (b:B.buffer U8.t { B.length b % 16 == 0 } ) : Stack unit
  (requires fun h -> B.live h b /\ B.length b > 0)
  (ensures fun h () h' -> 
    M.modifies (M.loc_buffer b) h h' /\
    buffer_to_quad b h' == q
  )
  =
  let b_lo0 = E.n_to_le 4ul q.lo0 in
  let b_lo1 = E.n_to_le 4ul q.lo1 in
  let b_hi2 = E.n_to_le 4ul q.hi2 in
  let b_hi3 = E.n_to_le 4ul q.hi3 in
  B.upd b 0ul (index b_lo0 0);
  B.upd b 1ul (index b_lo0 1);
  B.upd b 2ul (index b_lo0 2);
  B.upd b 3ul (index b_lo0 3);
  B.upd b 4ul (index b_lo1 0);
  B.upd b 5ul (index b_lo1 1);
  B.upd b 6ul (index b_lo1 2);
  B.upd b 7ul (index b_lo1 3);  
  B.upd b 8ul (index b_hi2 0);
  B.upd b 9ul (index b_hi2 1);
  B.upd b 10ul (index b_hi2 2);
  B.upd b 11ul (index b_hi2 3);
  B.upd b 12ul (index b_hi3 0);
  B.upd b 13ul (index b_hi3 1);
  B.upd b 14ul (index b_hi3 2);
  B.upd b 15ul (index b_hi3 3);
admit();  // TODO: Prove this actually works!
  ()
  
let buffer_to_quad32 (b:B.buffer U8.t { B.length b % 16 == 0 }) : Stack quad32
  (requires fun h -> B.live h b /\ B.length b > 0)
  (ensures fun h q h' -> 
    M.modifies M.loc_none h h' /\
    q == buffer_to_quad b h
  )
  =
  let b_lo0 = [B.index b 0ul; B.index b 1ul; B.index b 2ul; B.index b 3ul] in
  let b_lo1 = [B.index b 4ul; B.index b 5ul; B.index b 6ul; B.index b 7ul] in
  let b_hi2 = [B.index b 8ul; B.index b 9ul; B.index b 10ul; B.index b 11ul] in
  let b_hi3 = [B.index b 12ul; B.index b 13ul; B.index b 14ul; B.index b 15ul] in
  let lo0 = E.le_to_n (of_list b_lo0) in
  let lo1 = E.le_to_n (of_list b_lo1) in
  let hi2 = E.le_to_n (of_list b_hi2) in
  let hi3 = E.le_to_n (of_list b_hi3) in
admit();    // TODO: Prove this actually works!
  Mkfour lo0 lo1 hi2 hi3

let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

let keys_match' (key:Ghost.erased (aes_key_LE AES_128)) (keys128_b:BV.buffer quad32) (h:HS.mem) =
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

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
    keys_match key keys_b h (*
    (let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
     let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
     BV.as_seq h keys128_b == round_keys)  
    *)
  )
  (ensures fun h () h' -> 
    B.live h' input_b /\ B.live h' keys_b /\
    M.modifies (M.loc_buffer output_b) h h' /\
    (let  input_q = buffer_to_quad  input_b h in
     let output_q = buffer_to_quad output_b h' in
     output_q == aes_encrypt_LE AES_128 (Ghost.reveal key) input_q)
  )         

let aes128_encrypt_block (input:quad32) 
                         (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
                        : Stack quad32 
  (requires fun h ->
    // AES reqs
    B.live h keys_b /\
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h (*
    (let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
     let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
     BV.as_seq h keys128_b == round_keys)  
     *)
  )
  (ensures fun h output h' -> 
    M.modifies M.loc_none h h' /\
    output == aes_encrypt_LE AES_128 (Ghost.reveal key) input
  )                            
  = 
  push_frame ();
  // TODO: Future work: Pass a pointer to the struct, instead of copying to a bytes buffer
  let  input_b = B.alloca 0uy 16ul in
  let output_b = B.alloca 0uy 16ul in
  quad32_to_buffer input input_b;
assume (keys_match key keys_b (ST.get()));   // TODO: Remove this once BV.as_seq plays nicely with push_frame()
  aes128_encrypt_block_buffer input_b output_b key keys_b;
  let output = buffer_to_quad32 output_b in
  pop_frame ();
  output

(*
let aes128_encrypt_block_debug (input:quad32) 
                         (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
                        : Stack quad32 
  (requires fun h ->
    // AES reqs
    B.live h keys_b /\
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h (*
    (let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
     let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
     BV.as_seq h keys128_b == round_keys)  
     *)
  )
  (ensures fun h output h' -> 
    //modifies_none h h' /\
    //output == aes_encrypt_LE AES_128 (Ghost.reveal key) input
    True
  )                            
  = 
  //Call these lemmas explicitly to relate a buffer view back to the underlying buffer
  BV.as_buffer_mk_buffer_view keys_b Views.view128;
  BV.get_view_mk_buffer_view keys_b Views.view128;
  BV.length_eq (BV.mk_buffer_view keys_b Views.view128);
  let h0 = ST.get() in
  //assert (keys_match key keys_b h0);
  assert (keys_match' key (BV.mk_buffer_view keys_b Views.view128) h0);
  push_frame ();
  let h1 = ST.get() in
  //assert (keys_match key keys_b h1);
  assert (keys_match' key (BV.mk_buffer_view keys_b Views.view128) h1);
  // TODO: Future work: Pass a pointer to the struct, instead of copying to a bytes buffer
  let  input_b = magic() in // B.alloca 0uy 16ul in
  let output_b = magic() in //B.alloca 0uy 16ul in
  //quad32_to_buffer input input_b;
  assume (B.live h1 input_b /\ B.live h1 keys_b /\ B.live h1 output_b);
  assume (B.length  input_b % 16 == 0 /\ B.length  input_b >= 16 /\
    B.length output_b % 16 == 0 /\ B.length output_b >= 16);
  aes128_encrypt_block_buffer input_b output_b key keys_b;
  let output = buffer_to_quad32 output_b in
  pop_frame ();
  output
*)

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
    (let old_hash = buffer_to_quad hash_b h  in
     let new_hash = buffer_to_quad hash_b h' in
     let h_q      = buffer_to_quad h_b    h  in
     let num_bytes = U64.v num_bytes in 
     (num_bytes == 0 ==> new_hash == old_hash) /\
     (let input_bytes = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad input_b h)) 0 num_bytes in
      let padded_bytes = pad_to_128_bits input_bytes in
      let input_quads = le_bytes_to_seq_quad32 padded_bytes in
      num_bytes > 0 ==>  
        length input_quads > 0 /\
        new_hash == ghash_incremental h_q old_hash input_quads
     )
    )
  )

let ghash_incremental_bytes (h_val old_hash:quad32) (input_b:B.buffer U8.t) (num_bytes:U64.t) : Stack quad32
  (requires fun h -> 
    B.live h input_b /\
    B.length input_b % 16 == 0 /\ 
    B.length input_b >= 16 * (bytes_to_quad_size (U64.v num_bytes)) /\
    True
  )
  (ensures fun h new_hash h' -> 
    M.modifies (M.loc_none) h h' /\
    (let num_bytes = U64.v num_bytes in 
     (num_bytes == 0 ==> new_hash == old_hash) /\
     (let input_bytes = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad input_b h)) 0 num_bytes in
      let padded_bytes = pad_to_128_bits input_bytes in
      let input_quads = le_bytes_to_seq_quad32 padded_bytes in
      num_bytes > 0 ==>  
        length input_quads > 0 /\
        new_hash == ghash_incremental h_val old_hash input_quads
     )
    )
  )
  =
  let h0 = ST.get() in
  push_frame ();
  let h1 = ST.get() in
  //assume (buffer_to_seq_quad input_b h0 == buffer_to_seq_quad input_b h1);
  // TODO: Future work: Pass a pointer to the struct, instead of copying to a bytes buffer
  let    h_b = B.alloca 0uy 16ul in
  let hash_b = B.alloca 0uy 16ul in
  quad32_to_buffer h_val       h_b;
  let h1_5 = ST.get() in
  quad32_to_buffer old_hash hash_b; 
  let h2 = ST.get() in
assume (buffer_to_quad h_b h1_5 == buffer_to_quad h_b h2);  // TODO: Remove this once BV.as_seq plays nicely with other stack changes
  ghash_incremental_bytes_buffer h_b hash_b input_b num_bytes;
  let h3 = ST.get() in
  let output = buffer_to_quad32 hash_b in
  pop_frame ();
  let h4 = ST.get() in
assume (buffer_to_seq_quad input_b h2 == buffer_to_seq_quad input_b h0);    // TODO: Remove this once BV.as_seq plays nicely with other stack changes
  output


assume val gcm128_one_pass 
             (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t)              
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
             (old_hash iv_BE:quad32) 
           : Stack quad32
  (requires fun h -> True)
  (ensures fun h new_hash h' -> True) 


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
