module Reverse_quad32

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
open X64.Memory_i_s

let rec loc_locs_disjoint_rec (l:b8) (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let bufs_disjoint (ls:list b8) : Type0 = normalize (locs_disjoint_rec ls)

unfold
let buf_disjoint_from (b:b8) (ls:list b8) : Type0 = normalize (loc_locs_disjoint_rec b ls)

let buffer_to_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let pre_cond (h:HS.mem) (b:b8) = live h b /\ length b == 16

let post_cond (h:HS.mem) (h':HS.mem) (b:b8) = length b == 16 /\
      M.modifies (M.loc_buffer b) h h' /\
    (let old_b = buffer_to_quad32 b h  in
     let new_b = buffer_to_quad32 b h' in
     new_b == reverse_bytes_quad32 old_b)

val reverse_bytes_quad32_buffer: b:b8 -> Stack unit
	(requires (fun h -> pre_cond h b ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 b ))
