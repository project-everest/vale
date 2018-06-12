module X64.Bytes_Semantics_i
open Opaque_i

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
