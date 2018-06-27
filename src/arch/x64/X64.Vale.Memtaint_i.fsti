module X64.Vale.Memtaint_i
// This interface should not refer to Semantics_s

open X64.Machine_s
open X64.Memory_i

noeq type abuffer = | Buffer: (t:typ) -> buffer t -> abuffer

type t = abuffer -> taint

val equal: memtaint1:t -> memtaint2:t -> Type0

val lemma_equal_intro : memtaint1:t -> memtaint2:t -> Lemma
  (requires forall b. memtaint1 b == memtaint2 b)
  (ensures equal memtaint1 memtaint2)
  [SMTPat (equal memtaint1 memtaint2)]

val lemma_equal_elim : memtaint1:t -> memtaint2:t -> Lemma
  (requires equal memtaint1 memtaint2)
  (ensures memtaint1 == memtaint2)
  [SMTPat (equal memtaint1 memtaint2)]


