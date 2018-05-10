module Memory_s

module H = FStar.Monotonic.Heap
module HS = FStar.HyperStack
module B = FStar.Buffer
module M = FStar.Modifies

let heap = H.heap
let mem = HS.mem

let type_of_typ a = a

let buffer = B.buffer
let buffer_as_seq = B.as_seq
let buffer_readable = B.live
let buffer_length #t b = UInt32.uint_to_t (B.length b)

let loc = M.loc
let loc_none = M.loc_none
let loc_union = M.loc_union
let loc_buffer = M.loc_buffer
let loc_disjoint = M.loc_disjoint
let loc_includes = M.loc_includes
let modifies = M.modifies

#reset-options "--initial_fuel 1 --max_fuel 1"
let tuint8 = UInt8.t
let tuint16 = UInt16.t
let tuint32 = UInt32.t
let tuint64 = UInt64.t
//let tuint128 = magic()
#reset-options

// TODO: loc_readable
let loc_readable h s = unit // admit ()
let loc_readable_none h = admit ()
let loc_readable_union h s1 s2 = admit ()
let loc_readable_buffer #t h b = admit ()

let buffer_length_buffer_as_seq #t h b = ()

let modifies_buffer_elim #t1 b p h h' =
  M.modifies_buffer_elim b p h h'

let modifies_loc_readable #t b p h h' =
  // TODO
  admit ()

let loc_disjoint_none_r s = M.loc_disjoint_none_r s
let loc_disjoint_union_r s s1 s2 = M.loc_disjoint_union_r s s1 s2
let loc_includes_refl s = M.loc_includes_refl s
let loc_includes_trans s1 s2 s3 = M.loc_includes_trans s1 s2 s3
let loc_includes_union_r s s1 s2 = M.loc_includes_union_r s s1 s2
let loc_includes_union_l s1 s2 s = M.loc_includes_union_l s1 s2 s
let loc_includes_none s = M.loc_includes_none s
let modifies_refl s h = M.modifies_refl s h
let modifies_loc_includes s1 h h' s2 = M.modifies_loc_includes s1 h h' s2
let modifies_trans s12 h1 h2 s23 h3 = M.modifies_trans s12 h1 h2 s23 h3

// TODO
let buffer_read #_ _ _ _ = admit ()
let buffer_write #_ _ _ _ _ = admit ()
