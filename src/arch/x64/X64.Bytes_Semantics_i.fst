module X64.Bytes_Semantics_i
open Opaque_s

#reset-options "--z3rlimit 100 --max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

(*
let aux0 (ptr:int) (mem:heap) : Lemma (mod_8 (get_heap_val64 ptr mem) == mem.[ptr]) = ()
let aux1 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val64 ptr mem) `op_Division` 0x100) == mem.[ptr + 1]) = ()
let aux2 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val64 ptr mem) `op_Division` 0x10000) == mem.[ptr + 2]) = ()


let aux3 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val64 ptr mem) `op_Division` 0x1000000) == mem.[ptr + 3]) = ()


let aux4 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val64 ptr mem) `op_Division` 0x100000000) == mem.[ptr + 4]) = ()
    
let aux5 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val64 ptr mem) `op_Division` 0x10000000000) == mem.[ptr + 5]) = ()

let aux6 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val64 ptr mem) `op_Division` 0x1000000000000) == mem.[ptr + 6]) = ()    

let aux7 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val64 ptr mem) `op_Division` 0x100000000000000) == mem.[ptr + 7]) = ()
*)

let same_mem_get_heap_val (ptr:int) (mem1 mem2:heap) =
(*
  aux0 ptr mem1;
  aux0 ptr mem2;
  aux1 ptr mem1;
  aux1 ptr mem2;
  aux2 ptr mem1;
  aux2 ptr mem2;
  aux3 ptr mem1;
  aux3 ptr mem2;
  aux4 ptr mem1;
  aux4 ptr mem2;
  aux5 ptr mem1;
  aux5 ptr mem2;
  aux6 ptr mem1;
  aux6 ptr mem2;
  aux7 ptr mem1;
  aux7 ptr mem2;
*)
  admit () // TODO

let frame_update_heap ptr v mem =
  reveal_opaque get_heap_val64_def;
  reveal_opaque update_heap64_def

let correct_update_get ptr v mem =
  reveal_opaque get_heap_val64_def;
  reveal_opaque update_heap64_def

let same_mem_get_heap_val32 ptr mem1 mem2 =
assume False; // TODO
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def

let frame_update_heap32 (ptr:int) (v:nat32) (mem:heap) : Lemma
  (let mem' = update_heap32 ptr v mem in
  forall i. i < ptr \/ i >= ptr + 4 ==> mem.[i] == mem'.[i]) =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def

let frame_update_heap128 ptr v s =
  let mem1 = update_heap32 ptr v.lo0 s.mem in
  frame_update_heap32 ptr v.lo0 s.mem;
  let mem2 = update_heap32 (ptr+4) v.lo1 mem1 in
  frame_update_heap32 (ptr+4) v.lo1 mem1;
  let mem3 = update_heap32 (ptr+8) v.hi2 mem2 in
  frame_update_heap32 (ptr+8) v.hi2 mem2;
  let mem4 = update_heap32 (ptr+12) v.hi3 mem3 in  
  frame_update_heap32 (ptr+12) v.hi3 mem3

let correct_update_get32 (ptr:int) (v:nat32) (mem:heap) : Lemma
  (get_heap_val32 ptr (update_heap32 ptr v mem) == v) =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def

#reset-options "--z3rlimit 30 --using_facts_from 'Prims Opaque_s X64.Bytes_Semantics_s Words_s Types_s'"

let correct_update_get128 ptr v s =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def;
  let mem1 = update_heap32 ptr v.lo0 s.mem in
  frame_update_heap32 ptr v.lo0 s.mem;
  correct_update_get32 ptr v.lo0 s.mem;
  let mem2 = update_heap32 (ptr+4) v.lo1 mem1 in
  frame_update_heap32 (ptr+4) v.lo1 mem1;
  correct_update_get32 (ptr+4) v.lo1 mem1;
  let mem3 = update_heap32 (ptr+8) v.hi2 mem2 in
  frame_update_heap32 (ptr+8) v.hi2 mem2;
  correct_update_get32 (ptr+8) v.hi2 mem2;
  let mem4 = update_heap32 (ptr+12) v.hi3 mem3 in  
  frame_update_heap32 (ptr+12) v.hi3 mem3;
  correct_update_get32 (ptr+12) v.hi3 mem3
