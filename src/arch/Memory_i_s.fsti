module Memory_i_s
// TODO: eventually, this should be an untrusted module named Memory_i,
// but we're currently including it in the trusted Semantics_s module(s),
// so it has to be trusted.

unfold let nat8 = Words_s.nat8
unfold let nat16 = Words_s.nat16
unfold let nat32 = Words_s.nat32
unfold let nat64 = Words_s.nat64
unfold let quad32 = Types_s.quad32

val heap : Type u#1
val mem : Type u#1

type base_typ = 
| TUInt8
| TUInt16
| TUInt32
| TUInt64
| TUInt128

type typ =
| TBase: (b:base_typ) -> typ

let type_of_base_typ (t:base_typ) : Tot Type0 =
  match t with
  | TUInt8 -> nat8
  | TUInt16 -> nat16
  | TUInt32 -> nat32
  | TUInt64 -> nat64
  | TUInt128 -> quad32

let type_of_typ (t:typ) : Tot Type0 =
  match t with
  | TBase b -> type_of_base_typ b

val buffer (t:typ) : Type0
val buffer_as_seq (#t:typ) (h:mem) (b:buffer t) : GTot (Seq.seq (type_of_typ t))
val buffer_readable (#t:typ) (h:mem) (b:buffer t) : GTot Type0
val buffer_length (#t:typ) (b:buffer t) : GTot nat
val loc : Type u#0
val loc_none : loc
val loc_union (s1 s2:loc) : GTot loc
val loc_buffer (#t:typ) (b:buffer t) : GTot loc
val loc_disjoint (s1 s2:loc) : GTot Type0
val loc_includes (s1 s2:loc) : GTot Type0
val modifies (s:loc) (h1 h2:mem) : GTot Type0

unfold let buffer8 = buffer (TBase TUInt8)
unfold let buffer16 = buffer (TBase TUInt16)
unfold let buffer32 = buffer (TBase TUInt32)
unfold let buffer64 = buffer (TBase TUInt64)
unfold let buffer128 = buffer (TBase TUInt128)

val loc_readable (h:mem) (s:loc) : GTot Type0

val loc_readable_none (h:mem) : Lemma
  (ensures (loc_readable h loc_none))
  [SMTPat (loc_readable h loc_none)]

val loc_readable_union (h:mem) (s1 s2:loc) : Lemma
  (requires (loc_readable h s1 /\ loc_readable h s2))
  (ensures (loc_readable h (loc_union s1 s2)))
  [SMTPat (loc_readable h (loc_union s1 s2))]

val loc_readable_buffer (#t:typ) (h:mem) (b:buffer t) : Lemma
  (requires (buffer_readable h b))
  (ensures (loc_readable h (loc_buffer b)))
  [SMTPat (loc_readable h (loc_buffer b))]

let rec loc_locs_disjoint_rec (l:loc) (ls:list loc) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_disjoint l h /\ loc_disjoint h l /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list loc) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let locs_disjoint (ls:list loc) : Type0 = normalize (locs_disjoint_rec ls)

// equivalent to modifies; used to prove modifies clauses via modifies_goal_directed_trans
val modifies_goal_directed (s:loc) (h1 h2:mem) : GTot Type0
val lemma_modifies_goal_directed (s:loc) (h1 h2:mem) : Lemma
  (modifies s h1 h2 == modifies_goal_directed s h1 h2)

val buffer_length_buffer_as_seq (#t:typ) (h:mem) (b:buffer t) : Lemma
  (requires True)
  (ensures (Seq.length (buffer_as_seq h b) == buffer_length b))
  [SMTPat (Seq.length (buffer_as_seq h b))]

val modifies_buffer_elim (#t1:typ) (b:buffer t1) (p:loc) (h h':mem) : Lemma
  (requires
    loc_disjoint (loc_buffer b) p /\
    loc_readable h' p /\
    buffer_readable h b /\
    modifies p h h'
  )
  (ensures
    buffer_readable h b /\
    buffer_readable h' b /\
    buffer_as_seq h b == buffer_as_seq h' b
  )
  [SMTPatOr [
    [SMTPat (modifies p h h'); SMTPat (buffer_readable h' b)];
    [SMTPat (modifies p h h'); SMTPat (buffer_as_seq h' b)]
  ]]

val loc_disjoint_none_r (s:loc) : Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]

val loc_disjoint_union_r (s s1 s2:loc) : Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]

val loc_includes_refl (s:loc) : Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]

val loc_includes_trans (s1 s2 s3:loc) : Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r (s s1 s2:loc) : Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))
  [SMTPat (loc_includes s (loc_union s1 s2))]

val loc_includes_union_l (s1 s2 s:loc) : Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))
  // for efficiency, no SMT pattern

val loc_includes_union_l_buffer (#t:typ) (s1 s2:loc) (b:buffer t) : Lemma
  (requires (loc_includes s1 (loc_buffer b) \/ loc_includes s2 (loc_buffer b)))
  (ensures (loc_includes (loc_union s1 s2) (loc_buffer b)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_buffer b))]

val loc_includes_none (s:loc) : Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]

val modifies_refl (s:loc) (h:mem) : Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]

val modifies_goal_directed_refl (s:loc) (h:mem) : Lemma
  (modifies_goal_directed s h h)
  [SMTPat (modifies_goal_directed s h h)]

val modifies_loc_includes (s1:loc) (h h':mem) (s2:loc) : Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  // for efficiency, no SMT pattern

val modifies_trans (s12:loc) (h1 h2:mem) (s23:loc) (h3:mem) : Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))
  // for efficiency, no SMT pattern

// Prove (modifies s13 h1 h3).
// To avoid unnecessary matches, don't introduce any other modifies terms.
// Introduce modifies_goal_directed instead.
val modifies_goal_directed_trans (s12:loc) (h1 h2:mem) (s13:loc) (h3:mem) : Lemma
  (requires
    modifies s12 h1 h2 /\
    modifies_goal_directed s13 h2 h3 /\
    loc_includes s13 s12
  )
  (ensures (modifies s13 h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s13 h1 h3)]

val modifies_goal_directed_trans2 (s12:loc) (h1 h2:mem) (s13:loc) (h3:mem) : Lemma
  (requires
    modifies s12 h1 h2 /\
    modifies_goal_directed s13 h2 h3 /\
    loc_includes s13 s12
  )
  (ensures (modifies_goal_directed s13 h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies_goal_directed s13 h1 h3)]

val buffer_read (#t:typ) (b:buffer t) (i:int) (h:mem) : Pure (type_of_typ t)
  (requires True)
  (ensures (fun v ->
    0 <= i /\ i < buffer_length b /\ buffer_readable h b ==>
    v == Seq.index (buffer_as_seq h b) i
  ))

val buffer_write (#t:typ) (b:buffer t) (i:int) (v:type_of_typ t) (h:mem) : Pure mem
  (requires True)
  (ensures (fun h' ->
    0 <= i /\ i < buffer_length b /\ buffer_readable h b ==>
    modifies (loc_buffer b) h h' /\
    buffer_readable h' b /\
    buffer_as_seq h' b == Seq.upd (buffer_as_seq h b) i v
  ))

