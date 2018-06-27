module X64.Vale.Memtaint_i
open X64.Machine_s
open X64.Memory_i
open FStar.FunctionalExtensionality

let equal memtaint1 memtaint2 = feq memtaint1 memtaint2
let lemma_equal_intro memtaint1 memtaint2 = ()
let lemma_equal_elim memtaint1 memtaint2 = ()
