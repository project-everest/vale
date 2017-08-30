module Memory_i_s

module M = Memory_s

let heap = M.heap
let mem = M.mem

let coerce (#a:Type0) (b:Type0{a == b}) (x:a) : b = x

let m_of_typ (t:typ) : M.typ =
  match t with
  | TBase TUInt8 -> M.tuint8
  | TBase TUInt16 -> M.tuint16
  | TBase TUInt32 -> M.tuint32
  | TBase TUInt64 -> M.tuint64

let v_of_typ (t:typ) (v:type_of_typ t) : M.type_of_typ (m_of_typ t) =
  match t with
  | TBase TUInt8 -> coerce (M.type_of_typ (m_of_typ t)) (UInt8.uint_to_t v)
  | TBase TUInt16 -> coerce (M.type_of_typ (m_of_typ t)) (UInt16.uint_to_t v)
  | TBase TUInt32 -> coerce (M.type_of_typ (m_of_typ t)) (UInt32.uint_to_t v)
  | TBase TUInt64 -> coerce (M.type_of_typ (m_of_typ t)) (UInt64.uint_to_t v)

let v_to_typ (t:typ) (v:M.type_of_typ (m_of_typ t)) : type_of_typ t =
  match t with
  | TBase TUInt8 -> UInt8.v (coerce UInt8.t v)
  | TBase TUInt16 -> UInt16.v (coerce UInt16.t v)
  | TBase TUInt32 -> UInt32.v (coerce UInt32.t v)
  | TBase TUInt64 -> UInt64.v (coerce UInt64.t v)

let lemma_v_to_of_typ (t:typ) (v:type_of_typ t) : Lemma
  (ensures v_to_typ t (v_of_typ t v) == v)
  [SMTPat (v_to_typ t (v_of_typ t v))]
  =
  match t with
  | TBase TUInt8 -> assert (UInt8.v (UInt8.uint_to_t v) == v)
  | TBase TUInt16 -> assert (UInt16.v (UInt16.uint_to_t v) == v)
  | TBase TUInt32 -> assert (UInt32.v (UInt32.uint_to_t v) == v)
  | TBase TUInt64 -> assert (UInt64.v (UInt64.uint_to_t v) == v)

let buffer t = M.buffer (m_of_typ t)

let buffer_as_seq #t h b =
  let s = M.buffer_as_seq h b in
  let len = Seq.length s in
  let contents (i:nat{i < len}) : type_of_typ t = v_to_typ t (Seq.index s i) in
  Seq.init len contents

let buffer_readable #t h b = M.buffer_readable h b
let loc = M.loc
let loc_none = M.loc_none
let loc_union = M.loc_union
let loc_buffer #t b = M.loc_buffer b
let loc_disjoint = M.loc_disjoint
let loc_includes = M.loc_includes
let modifies = M.modifies

let modifies_goal_directed s h1 h2 = modifies s h1 h2
let lemma_modifies_goal_directed s h1 h2 = ()

let modifies_buffer_elim #t1 b p h h' =
  M.modifies_buffer_elim b p h h';
  assert (Seq.equal (buffer_as_seq h b) (buffer_as_seq h' b));
  ()

let loc_includes_refl s = M.loc_includes_refl s
let loc_includes_trans s1 s2 s3 = M.loc_includes_trans s1 s2 s3
let loc_includes_union_r s s1 s2 = M.loc_includes_union_r s s1 s2
let loc_includes_union_l s1 s2 s = M.loc_includes_union_l s1 s2 s
let loc_includes_union_l_buffer #t s1 s2 b = M.loc_includes_union_l s1 s2 (loc_buffer b)
let loc_includes_none s = M.loc_includes_none s
let modifies_refl s h = M.modifies_refl s h
let modifies_goal_directed_refl s h = M.modifies_refl s h
let modifies_loc_includes s1 h h' s2 = M.modifies_loc_includes s1 h h' s2
let modifies_trans s12 h1 h2 s23 h3 = M.modifies_trans s12 h1 h2 s23 h3

let modifies_goal_directed_trans s12 h1 h2 s13 h3 =
  modifies_trans s12 h1 h2 s13 h3;
  modifies_loc_includes s13 h1 h3 (loc_union s12 s13);
  ()

let modifies_goal_directed_trans2 s12 h1 h2 s13 h3 = modifies_goal_directed_trans s12 h1 h2 s13 h3

let default_of_typ (t:typ) : type_of_typ t =
  match t with
  | TBase TUInt8 -> 0
  | TBase TUInt16 -> 0
  | TBase TUInt32 -> 0
  | TBase TUInt64 -> 0

let buffer_read #t b i h =
  if i < 0 || i >= Arch_s.nat32_max then default_of_typ t else
  let v = M.buffer_read b (UInt32.uint_to_t i) h in
  v_to_typ t v

let buffer_write #t b i v h =
  if i < 0 || i >= Arch_s.nat32_max then h else
  let vu = v_of_typ t v in
  let h' = M.buffer_write b (UInt32.uint_to_t i) vu h in
  assert (v_to_typ t vu == v); // v_to_typ (v_of_typ v)
  assert
    (i < Seq.length (buffer_as_seq h b) /\ buffer_readable h b ==>
      Seq.equal (buffer_as_seq h' b) (Seq.upd (buffer_as_seq h b) i v));
  h'

