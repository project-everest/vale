module X64.Bytes_Semantics_i

open X64.Bytes_Semantics_s
open X64.Machine_s

val same_mem_get_heap_val (ptr:int) (mem1 mem2:heap) : Lemma
  (requires get_heap_val64 ptr mem1 == get_heap_val64 ptr mem2)
  (ensures forall i. i >= ptr /\ i < ptr + 8 ==> mem1.[i] == mem2.[i])

val frame_update_heap (ptr:int) (v:nat64) (mem:heap) : Lemma (
  let new_mem = update_heap64 ptr v mem in
  forall j. j < ptr \/ j >= ptr + 8 ==> 
    mem.[j] == new_mem.[j]) 

val correct_update_get (ptr:int) (v:nat64) (mem:heap) : Lemma (
  get_heap_val64 ptr (update_heap64 ptr v mem) == v)
  [SMTPat (get_heap_val64 ptr (update_heap64 ptr v mem))] 
