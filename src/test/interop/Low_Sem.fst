module Low_Sem

module List = FStar.List.Tot.Base
module M = Vale_Sem
module B = FStar.Buffer
module HS = FStar.HyperStack
open Machine_int
open Interop64

type heap = M.heap

let buffer64 = B.buffer UInt64.t
let buffer_addr (b:buffer64) (addrs:addr_map) =
  addrs.[(B.as_addr b, B.idx b, B.length b)]
  
let buffer_read (b:buffer64) (i:nat{i < B.length b}) (mem:HS.mem) : GTot nat64 =
  let contents = B.as_seq mem b in
  UInt64.v (Seq.index contents i)

let buffer_write (b:buffer64) (i:nat{i < B.length b}) (v:nat64) (mem:HS.mem) : GTot HS.mem =
  admit()

noeq type low_state_p = {
  s:M.state;
  addrs:addr_map;
  ptrs: list buffer64;
  mem: HS.mem;
}

let valid_state s =
  list_disjoint_or_eq s.ptrs /\
  s.s.M.mem == down_mem64 s.mem s.addrs s.ptrs

type low_state = (s:low_state_p{valid_state s})

val valid_mem: ptr:int 
  -> s:low_state
  -> GTot bool
val load_mem: ptr:int 
  -> s:low_state
  -> GTot nat64
val store_mem: ptr:int 
  -> v:nat64 
  -> s:low_state
  -> GTot low_state

val addr_in_ptr: (addr:int) -> (ptr:buffer64) -> (addrs:addr_map) ->
  GTot (b:bool{ not b <==> (forall i. 0 <= i /\ i < B.length ptr ==> 
    addr <> (buffer_addr ptr addrs) + 8 `op_Multiply` i)})
  
// Checks if address addr corresponds to one of the elements of buffer ptr
let addr_in_ptr (addr:int) (ptr:buffer64) (addrs:addr_map) =
  let n = B.length ptr in
  let base = buffer_addr ptr addrs in
  let rec aux (i:nat) : Tot (b:bool{not b <==> (forall j. i <= j /\ j < n ==> 
    addr <> base + 8 `op_Multiply` j)}) 
    (decreases %[n-i]) =
    if i >= n then false
    else if addr = base + 8 `op_Multiply` i then true
    else aux (i+1)
  in aux 0


let rec valid_mem_aux addr ps (addrs:addr_map) : GTot (b:bool{
  (not b) <==> (forall (x:buffer64). (List.memP x ps ==> not (addr_in_ptr addr x addrs) ))}) 
  = match ps with
    | [] -> false
    | a::q -> if (addr_in_ptr addr a addrs) then true else valid_mem_aux addr q addrs

let valid_mem addr s =
  // Iterate over the list of buffers existing in this state
  valid_mem_aux addr s.ptrs s.addrs


let load_mem ptr s = M.get_heap_value ptr s.s

let store_mem ptr v s =
  let s' = M.update_mem ptr v s.s in
  admit()

let rec valid_mem_aux_lemma addr ps addrs (x:buffer64) : Lemma (
   List.memP x ps /\ addr_in_ptr addr x addrs ==>
   valid_mem_aux addr ps addrs
   ) =
   match ps with
     | [] -> ()
     | a::q -> valid_mem_aux_lemma addr q addrs x

val lemma_valid_mem: b:buffer64
  -> i:nat 
  -> s:low_state
  -> Lemma (requires i < B.length b /\ List.memP b s.ptrs)
     (ensures valid_mem 
       (buffer_addr b s.addrs + 8 `op_Multiply` i)
       s)

let lemma_valid_mem b i s =
  let base = buffer_addr b s.addrs in
  let addr = base + 8 `op_Multiply` i in
  valid_mem_aux_lemma addr s.ptrs s.addrs b

val lemma_load_mem: b:buffer64
  -> i:nat
  -> s:low_state
  -> Lemma (requires i < B.length b /\ List.memP b s.ptrs)
     (ensures load_mem (buffer_addr b s.addrs + 8 `op_Multiply` i) s == buffer_read b i s.mem)

let lemma_load_mem b i s = ()

val lemma_store_mem: b:buffer64 
  -> i:nat 
  -> v:nat64
  -> s:low_state
  -> Lemma (requires i < B.length b /\ List.memP b s.ptrs)
     (ensures (store_mem (buffer_addr b s.addrs + 8 `op_Multiply` i) v s).mem == buffer_write b i v s.mem)

val lemma_store_load_mem: i:int 
  -> v:nat64
  -> s:low_state
  -> Lemma (load_mem i (store_mem i v s) == v)

val lemma_frame_store_mem: i:int 
  -> v:nat64
  -> s:low_state
  -> Lemma (let s' = store_mem i v s in
     forall i'. i' <> i /\ valid_mem i s /\ valid_mem i' s ==> 
       load_mem i' s = load_mem i' s')

val lemma_valid_store_mem: i:int 
  -> v:nat64
  -> s:low_state
  -> Lemma (let s' = store_mem i v s in
     forall j. valid_mem j s <==> valid_mem j s')
