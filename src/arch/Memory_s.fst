module Memory_s

module H = FStar.Monotonic.Heap
module HS = FStar.HyperStack
module P = FStar.Pointer

let heap = H.heap
let mem = HS.mem

let typ = P.typ
let type_of_typ = P.type_of_typ

let buffer = P.buffer
let buffer_as_seq = P.buffer_as_seq
let buffer_readable = P.buffer_readable
let buffer_length = P.buffer_length
let loc = P.loc
let loc_none = P.loc_none
let loc_union = P.loc_union
let loc_buffer = P.loc_buffer
let loc_disjoint = P.loc_disjoint
let loc_includes = P.loc_includes
let modifies = P.modifies

#reset-options "--initial_fuel 1 --max_fuel 1"
let tuint8 = P.TBase P.TUInt8
let tuint16 = P.TBase P.TUInt16
let tuint32 = P.TBase P.TUInt32
let tuint64 = P.TBase P.TUInt64
let tuint128 = magic()
#reset-options

// TODO: loc_readable
let loc_readable h s = admit ()
let loc_readable_none h = admit ()
let loc_readable_union h s1 s2 = admit ()
let loc_readable_buffer #t h b = admit ()

let buffer_length_buffer_as_seq #t h b = P.buffer_length_buffer_as_seq h b

let modifies_buffer_elim #t1 b p h h' =
  P.modifies_buffer_elim b p h h'

let modifies_loc_readable #t b p h h' =
  // TODO
  admit ()

let loc_disjoint_none_r s = P.loc_disjoint_none_r s
let loc_disjoint_union_r s s1 s2 = P.loc_disjoint_union_r s s1 s2
let loc_includes_refl s = P.loc_includes_refl s
let loc_includes_trans s1 s2 s3 = P.loc_includes_trans s1 s2 s3
let loc_includes_union_r s s1 s2 = P.loc_includes_union_r s s1 s2
let loc_includes_union_l s1 s2 s = P.loc_includes_union_l s1 s2 s
let loc_includes_none s = P.loc_includes_none s
let modifies_refl s h = P.modifies_refl s h
let modifies_loc_includes s1 h h' s2 = P.modifies_loc_includes s1 h h' s2
let modifies_trans s12 h1 h2 s23 h3 = P.modifies_trans s12 h1 h2 s23 h3

// TODO
let buffer_read = admit ()
let buffer_write = admit ()
