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

val buffer_write: b:buffer64 -> (n:nat{n < B.length b}) -> v:nat64 -> (h0:HS.mem{B.live h0 b}) -> GTot
 (h1:HS.mem)
 
let buffer_write b n v h0 =
 let s0 = B.sel h0 b in
// assume (B.idx b + B.length b <= B.max_length b);
// assume (B.max_length b == Seq.Base.length s0);
// assume (0 <= B.idx b + n /\ B.idx b + n < B.max_length b);
 let s = Seq.upd s0 (B.idx b + n) (UInt64.uint_to_t v) in
// assume (HS.live_region h0 (B.frameOf b));
 let h1 = HS.upd h0 (B.content b) s in
// lemma_aux #a b n z h0;
 h1

noeq type low_state_p = {
  s:M.state;
  addrs:addr_map;
  ptrs: list buffer64;
  mem: HS.mem;
}

type low_state = (s:low_state_p{list_disjoint_or_eq s.ptrs /\ list_live s.mem s.ptrs})

let valid_state (s:low_state) =
  s.s.M.mem == down_mem64 s.mem s.addrs s.ptrs

// type low_state = (s:low_state_p{valid_state s})

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

let rec get_addr_in_ptr (n base addr:nat) (i:nat{exists j. i <= j /\ j < n /\ base + 8 `op_Multiply` j == addr}) : 
    GTot (j:nat{base + 8 `op_Multiply` j == addr})
    (decreases %[n-i]) =
    if base + 8 `op_Multiply` i = addr then i
    else if i >= n then i
    else get_addr_in_ptr n base addr (i+1)


let rec valid_mem_aux addr ps (addrs:addr_map) : GTot (b:bool{
  (not b) <==> (forall (x:buffer64). (List.memP x ps ==> not (addr_in_ptr addr x addrs) ))}) 
  = match ps with
    | [] -> false
    | a::q -> if (addr_in_ptr addr a addrs) then true else valid_mem_aux addr q addrs

let valid_mem addr s =
  // Iterate over the list of buffers existing in this state
  valid_mem_aux addr s.ptrs s.addrs

let load_mem ptr s = M.get_heap_value ptr s.s

let rec store_mem_aux addr ps (v:nat64) (addrs:addr_map) (h0:HS.mem{list_live h0 ps}) : 
  GTot (h1:HS.mem{forall (b:buffer64). B.live h0 b <==> B.live h1 b }) =
  match ps with
  | [] -> h0
  | a::q ->
    let base = buffer_addr a addrs in
    let n = B.length a in
    if addr_in_ptr addr a addrs then
    begin
//      buffer_write a 0 v h0
      buffer_write a (get_addr_in_ptr n base addr 0) v h0
    end
    else store_mem_aux addr q v addrs h0

let store_mem ptr v s =
  let s' = M.update_mem ptr v s.s in
  let h1 = store_mem_aux ptr s.ptrs v s.addrs s.mem in
  {s with s = s'; mem = h1}

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
  -> Lemma (requires i < B.length b /\ List.memP b s.ptrs /\ valid_state s)
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
  -> Lemma (requires i < B.length b /\ List.memP b s.ptrs /\ valid_state s)
     (ensures load_mem (buffer_addr b s.addrs + 8 `op_Multiply` i) s == buffer_read b i s.mem)

let lemma_load_mem b i s = ()

val lemma_store_mem: b:buffer64 
  -> i:nat 
  -> v:nat64
  -> s:low_state
  -> Lemma (requires i < B.length b /\ List.memP b s.ptrs /\ valid_state s)
     (ensures (let s' = store_mem (buffer_addr b s.addrs + 8 `op_Multiply` i) v s in
       s'.mem == buffer_write b i v s.mem))

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

val lemma_valid_state_store_mem: i:int 
  -> v:nat64
  -> s:low_state
  -> Lemma (requires (valid_state s /\ valid_mem i s))
    (ensures valid_state (store_mem i v s))

#set-options "--z3rlimit 20"

let valid_disjoint i i' s : Lemma 
  (valid_mem i s /\ valid_mem i' s /\ i' <> i ==> i' + 8 <= i \/ i + 8 <= i') =
  let rec aux addrs (ps:list buffer64{list_disjoint_or_eq ps}) : Lemma 
  (requires (i <> i' /\ valid_mem_aux i ps addrs /\ valid_mem_aux i' ps addrs))
  (ensures (i' + 8 <= i \/ i + 8 <= i')) =
  match ps with
  | [] -> ()
  | a::q -> 
    if (addr_in_ptr i a addrs) then
      if (addr_in_ptr i' a addrs) then ()
      else
      let rec aux2 (ps2:list buffer64{list_disjoint_or_eq (a::ps2)}) : Lemma
      (requires valid_mem_aux i' ps2 addrs)
      (ensures (i' + 8 <= i \/ i + 8 <= i')) =
      match ps2 with
    	| [] -> ()
    	| b::r -> 
	  if (addr_in_ptr i' b addrs) then begin
	    assert (disjoint_or_eq a b);
	    ()
	  end
	  else aux2 r
      in aux2 q
    else begin 
      if (addr_in_ptr i' a addrs) then begin
      let rec aux2 (ps2:list buffer64{list_disjoint_or_eq (a::ps2)}) : Lemma
	(requires valid_mem_aux i ps2 addrs)
	(ensures (i' + 8 <= i \/ i + 8 <= i')) =
	match ps2 with
    	  | [] -> ()
    	  | b::r -> 
	    if (addr_in_ptr i b addrs) then begin
	      assert (disjoint_or_eq a b);
	      ()
	    end
	    else aux2 r
	in aux2 q	
      end
      else aux addrs q
    end
  in
  Classical.move_requires (aux s.addrs) s.ptrs

let lemma_store_mem b i v s =
  let addr = buffer_addr b s.addrs + 8 `op_Multiply` i in
  let s' = store_mem addr v s in
  let rec aux (ps:list buffer64{list_disjoint_or_eq ps}) (h0:HS.mem{list_live h0 ps}) : 
    Lemma (requires (valid_state s /\ List.memP b ps /\ i < B.length b) )
    (ensures (store_mem_aux addr ps v s.addrs h0 == buffer_write b i v h0)) = 
  match ps with
    | [] -> ()
    | a::q ->
      if addr_in_ptr addr a s.addrs then begin
	assert (disjoint_or_eq a b);
	()
      end
      else begin
	assert (b =!= a);
	aux q h0
      end
  in aux s.ptrs s.mem

let lemma_store_load_mem i v s = ()

let lemma_frame_store_mem i v s =
  let s' = store_mem i v s in
  let rec aux i' : Lemma (i' <> i /\ valid_mem i s /\ valid_mem i' s ==>
    load_mem i' s = load_mem i' s') =
    valid_disjoint i i' s;
    M.frame_update_heap i v s.s.M.mem;
    ()
  in Classical.forall_intro aux 

let lemma_valid_store_mem i v s = ()

let store_buffer_down_mem (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{list_disjoint_or_eq ps /\ List.memP b ps}) (h0:HS.mem{list_live h0 ps}) (addrs:addr_map) :
  Lemma (
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in
    let base = buffer_addr b addrs in
    forall j. j < base + 8 `op_Multiply` i \/ j >= base + 8 `op_Multiply` (i+1) ==>
      mem1.[j] == mem2.[j]) = admit()

let store_buffer_aux_down_mem (ptr:int) (v:nat64) (s:low_state) : Lemma (
  let mem1 = down_mem64 s.mem s.addrs s.ptrs in
  let h1 = store_mem_aux ptr s.ptrs v s.addrs s.mem in
  let mem2 = down_mem64 h1 s.addrs s.ptrs in
  forall j. j < ptr \/ j >= ptr + 8 ==> mem1.[j] == mem2.[j]) =
  admit()

let store_buffer_aux_down_mem2 (ptr:int) (v:nat64) (s:low_state) : Lemma (
  let h1 = store_mem_aux ptr s.ptrs v s.addrs s.mem in
  let mem2 = down_mem64 h1 s.addrs s.ptrs in
  M.get_heap_val ptr mem2 == v) =
  admit()

#set-options "--z3rlimit 60"

let lemma_valid_state_store_mem i v s =
  let s' = store_mem i v s in
  assert (s.s.M.mem == down_mem64 s.mem s.addrs s.ptrs);
  // assert (s'.s == M.update_mem i v s.s);
  // assert (M.get_heap_value i s'.s == v);
  M.frame_update_heap i v s.s.M.mem;
  store_buffer_aux_down_mem i v s;
  store_buffer_aux_down_mem2 i v s;
  let mem1 = s'.s.M.mem in
  let mem2 = down_mem64 s'.mem s.addrs s.ptrs in
  // assert (M.get_heap_val i mem1 == v);
  // assert (M.get_heap_val i mem2 == v);
  M.same_mem_get_heap_val i mem1 mem2;
  // assert (forall j. j < i \/ j >= i + 8 ==> mem1.[j] == mem2.[j]);
  // assert (forall j. j >= i /\ j < i + 8 ==> mem1.[j] == mem2.[j]);
  assume (forall j. mem1.[j] == mem2.[j]);
  assert (Map.equal mem1 mem2);
  assert (mem1 == mem2);
//  assert (s'.s.M.mem == down_mem64 s'.mem s.addrs s.ptrs);
  ()
  
