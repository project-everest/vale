module Memory_s

val heap : Type u#1 // FStar.Monotonic.Heap.heap
val mem : Type u#1 // FStar.HyperStack.mem

//////////////////////////////////////////////////////////////////////////////
// Definitions from FStar.Pointer.Base
//////////////////////////////////////////////////////////////////////////////

val typ : Type0
val type_of_typ : typ -> Type0
val buffer (t:typ) : Type0
val buffer_as_seq (#t:typ) (h:mem) (b:buffer t) : GTot (Seq.seq (type_of_typ t))
val buffer_readable (#t:typ) (h:mem) (b:buffer t) : GTot Type0 // for now, using just buffer_readable, not buffer_live
val buffer_length (#t:typ) (b:buffer t) : GTot UInt32.t
val loc : Type u#0
val loc_none : loc
val loc_union (s1 s2:loc) : GTot loc
val loc_buffer (#t:typ) (b:buffer t) : GTot loc
val loc_disjoint (s1 s2:loc) : GTot Type0
val loc_includes (s1 s2:loc) : GTot Type0
val modifies (s:loc) (h1 h2:mem) : GTot Type0

val tuint8 : (t:typ{type_of_typ t == UInt8.t})
val tuint16 : (t:typ{type_of_typ t == UInt16.t})
val tuint32 : (t:typ{type_of_typ t == UInt32.t})
val tuint64 : (t:typ{type_of_typ t == UInt64.t})
//val tuint128 : (t:typ{type_of_typ t == UInt128.t})

val loc_readable (h:mem) (s:loc) : GTot Type0

val loc_readable_none (h:mem) : Lemma
  (ensures (loc_readable h loc_none))

val loc_readable_union (h:mem) (s1 s2:loc) : Lemma
  (requires (loc_readable h s1 /\ loc_readable h s2))
  (ensures (loc_readable h (loc_union s1 s2)))

val loc_readable_buffer (#t:typ) (h:mem) (b:buffer t) : Lemma
  (requires (buffer_readable h b))
  (ensures (loc_readable h (loc_buffer b)))

//////////////////////////////////////////////////////////////////////////////
// Lemmas from FStar.Pointer.Base
// (with some simplifications and fewer SMT patterns)
//////////////////////////////////////////////////////////////////////////////

val buffer_length_buffer_as_seq (#t:typ) (h:mem) (b:buffer t) : Lemma
  (requires True)
  (ensures (Seq.length (buffer_as_seq h b) == UInt32.v (buffer_length b)))
  [SMTPat (Seq.length (buffer_as_seq h b))]

val modifies_buffer_elim (#t1:typ) (b:buffer t1) (p:loc) (h h':mem) : Lemma
  (requires
    loc_disjoint (loc_buffer b) p /\
    buffer_readable h b /\
    UInt32.v (buffer_length b) > 0 /\
    modifies p h h'
  )
  (ensures
    buffer_readable h b /\
    buffer_readable h' b /\
    buffer_as_seq h b == buffer_as_seq h' b
  )

val modifies_loc_readable (#t:typ) (b:buffer t) (p:loc) (h h':mem) : Lemma
  (requires
    loc_readable h' p /\
    buffer_readable h b /\
    modifies p h h'
  )
  (ensures
    buffer_readable h' b
  )

val loc_disjoint_none_r (s:loc) : Lemma
  (ensures (loc_disjoint s loc_none))

val loc_disjoint_union_r (s s1 s2:loc) : Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))

val loc_includes_refl (s:loc) : Lemma
  (loc_includes s s)

val loc_includes_trans (s1 s2 s3:loc) : Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r (s s1 s2:loc) : Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))

val loc_includes_union_l (s1 s2 s:loc) : Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))

val loc_includes_none (s:loc) : Lemma
  (loc_includes s loc_none)

val modifies_refl (s:loc) (h:mem) : Lemma
  (modifies s h h)

val modifies_loc_includes (s1:loc) (h h':mem) (s2:loc) : Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))

val modifies_trans (s12:loc) (h1 h2:mem) (s23:loc) (h3:mem) : Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))

//////////////////////////////////////////////////////////////////////////////
// Pure versions of read_buffer, write_buffer
//////////////////////////////////////////////////////////////////////////////

// All members of (type_of_typ t) are inhabited, so buffer_read can always return a value:
val buffer_read (#t:typ) (b:buffer t) (i:UInt32.t) (h:mem) : Pure (type_of_typ t)
  (requires True)
  (ensures (fun v ->
    UInt32.v i < UInt32.v (buffer_length b) /\ buffer_readable h b ==>
    v == Seq.index (buffer_as_seq h b) (UInt32.v i)
  ))

val buffer_write (#t:typ) (b:buffer t) (i:UInt32.t) (v:type_of_typ t) (h:mem) : Pure mem
  (requires True)
  (ensures (fun h' ->
    UInt32.v i < UInt32.v (buffer_length b) /\ buffer_readable h b ==>
    modifies (loc_buffer b) h h' /\
    buffer_readable h' b /\
    buffer_as_seq h' b == Seq.upd (buffer_as_seq h b) (UInt32.v i) v
  ))

