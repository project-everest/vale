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
 (h1:HS.mem{B.as_seq h1 b == Seq.upd (B.as_seq h0 b) n (UInt64.uint_to_t v) /\ B.modifies_1 b h0 h1})

// Proven but private in FStar.Buffer
assume private val lemma_aux: b:buffer64 -> n:nat{n < B.length b} -> z:UInt64.t
  -> h0:HS.mem -> Lemma
  (requires (B.live h0 b))
  (ensures (B.live h0 b
    /\ B.modifies_1 b h0 (HS.upd h0 (B.content b) (Seq.upd (B.sel h0 b) (B.idx b + n) z)) ))

let buffer_write b n v h0 =
 let s0 = B.sel h0 b in
 let s = Seq.upd s0 (B.idx b + n) (UInt64.uint_to_t v) in
 let h1 = HS.upd h0 (B.content b) s in
 lemma_aux b n (UInt64.uint_to_t v) h0;
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

#set-options "--z3rlimit 40"

let written_buffer_down (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{list_disjoint_or_eq ps /\ List.memP b ps}) (h0:HS.mem{list_live h0 ps}) (addrs:addr_map) :
  Lemma (
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in
    let base = buffer_addr b addrs in
    let n = B.length b in
    forall j. (base <= j /\ j < base + 8 `op_Multiply` i) \/ 
	 (base + 8 `op_Multiply` (i+1) <= j /\ j < base + 8 `op_Multiply` n) ==>
	 mem1.[j] == mem2.[j]) = 
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in	 
    let base = buffer_addr b addrs in
    let n = B.length b in
    let rec aux1 (k:nat) (mem1:M.heap{correct_down64 h0 addrs ps mem1}) 
      (mem2:M.heap{
      (correct_down64 h1 addrs ps mem2) /\
      (forall j. base <= j /\ j < base + k `op_Multiply` 8 ==> mem1.[j] == mem2.[j])}) : 
      Lemma (requires True)
      (ensures (forall j. j >= base /\ j < base + 8 `op_Multiply` i ==> mem1.[j] == mem2.[j]))
      (decreases %[i-k]) =
    if k >= i then ()
    else begin
      assert (Seq.index (B.as_seq h0 b) k == Seq.index (B.as_seq h1 b) k);
      M.same_mem_get_heap_val (base + 8 `op_Multiply` k) mem1 mem2;
      aux1 (k+1) mem1 mem2
    end
    in
    
    let rec aux2 (k:nat{k > i}) (mem1:M.heap{correct_down64 h0 addrs ps mem1})
    (mem2:M.heap{
      (correct_down64 h1 addrs ps mem2) /\
      (forall j. base + 8 `op_Multiply` (i+1) <= j /\ j < base + k `op_Multiply` 8 ==>
      mem1.[j] == mem2.[j])}) :
      Lemma 
      (requires True)
      (ensures (forall j. j >= base + 8 `op_Multiply` (i+1) /\ j < base + 8 `op_Multiply` n ==> 
	mem1.[j] == mem2.[j]))
      (decreases %[n-k]) =
    if k >= n then ()
    else begin
      assert (Seq.index (B.as_seq h0 b) k == Seq.index (B.as_seq h1 b) k);
      M.same_mem_get_heap_val (base + 8 `op_Multiply` k) mem1 mem2;
      aux2 (k+1) mem1 mem2
    end
    in      
    
    aux1 0 mem1 mem2;
    aux2 (i+1) mem1 mem2

let same_mem_get_heap_val_buf (base n:int) (mem1 mem2:M.heap) : Lemma
  (requires (forall i. 0 <= i /\ i < n ==> 
    M.get_heap_val (base + 8 `op_Multiply` i) mem1 == M.get_heap_val (base + 8 `op_Multiply` i) mem2))
  (ensures (forall i. i >= base /\ i < base + n `op_Multiply` 8 ==> mem1.[i] == mem2.[i])) =
  let rec aux (k:nat) : Lemma
  (requires (forall i. i >= base /\ i < base + k `op_Multiply` 8 ==> mem1.[i] == mem2.[i]) /\
   (forall i. 0 <= i /\ i < n ==> 
    M.get_heap_val (base + 8 `op_Multiply` i) mem1 == M.get_heap_val (base + 8 `op_Multiply` i) mem2) 
  )
  (ensures (forall i. i >= base /\ i < base + n `op_Multiply` 8 ==> mem1.[i] == mem2.[i]))
  (decreases %[n-k]) =
  if k >= n then ()
  else begin
    M.same_mem_get_heap_val (base + k `op_Multiply` 8) mem1 mem2;
    aux (k+1)
  end
  in aux 0

let rec unwritten_buffer_down_aux (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{list_disjoint_or_eq ps /\ List.memP b ps})
  (h0:HS.mem{list_live h0 ps}) 
  (addrs:addr_map) (a:buffer64{a =!= b /\ List.memP a ps})  : 
  Lemma (let base = buffer_addr a addrs in
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in
    forall j. j >= base /\ j < base + (B.length a) `op_Multiply` 8 ==> mem1.[j] == mem2.[j]) =
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in
    let base = buffer_addr a addrs in    
    let s0 = B.as_seq h0 a in
    assert (disjoint_or_eq a b);
    // We need this to help z3
    assert (forall j. 0 <= j /\ j < B.length a ==> UInt64.v (Seq.index s0 j) == M.get_heap_val (base + (j `op_Multiply` 8)) mem1 );
    same_mem_get_heap_val_buf base (B.length a) mem1 mem2


let unwritten_buffer_down (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{list_disjoint_or_eq ps /\ List.memP b ps}) (h0:HS.mem{list_live h0 ps}) (addrs:addr_map) : Lemma (
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in
    forall  (a:buffer64{List.memP a ps /\ a =!= b}) j.
    let base = buffer_addr a addrs in j >= base /\ j < base + B.length a `op_Multiply` 8 ==> mem1.[j] == mem2.[j]) =
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in   
    let fintro (a:buffer64{List.memP a ps /\ a =!= b}) 
      : Lemma 
      (forall j. let base = buffer_addr a addrs in 
      j >= base /\ j < base + (B.length a) `op_Multiply` 8 ==> 
	mem1.[j] == mem2.[j]) =
      let base = buffer_addr a addrs in
      unwritten_buffer_down_aux b i v ps h0 addrs a
    in
    Classical.forall_intro fintro

let store_buffer_down_mem (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{list_disjoint_or_eq ps /\ List.memP b ps}) (h0:HS.mem{list_live h0 ps}) (addrs:addr_map) :
  Lemma (
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in
    let base = buffer_addr b addrs in
    forall j. j < base + 8 `op_Multiply` i \/ j >= base + 8 `op_Multiply` (i+1) ==>
      mem1.[j] == mem2.[j]) =
    let mem1 = down_mem64 h0 addrs ps in
    let h1 = buffer_write b i v h0 in
    let mem2 = down_mem64 h1 addrs ps in
    let base = buffer_addr b addrs in
    let n = B.length b in
    same_unspecified_down h0 h1 addrs ps;

    unwritten_buffer_down b i v ps h0 addrs;

    assert (forall j. (exists (a:buffer64{List.memP a ps /\ a =!= b}) . let base = buffer_addr a addrs in
      j >= base /\ j < base + B.length a `op_Multiply` 8) ==> mem1.[j] == mem2.[j]);

    written_buffer_down b i v ps h0 addrs;
    ()

let rec get_addr_ptr (ptr:int) (addrs:addr_map) (ps:list buffer64{valid_mem_aux ptr ps addrs}) : 
  GTot (b:buffer64{List.memP b ps /\ addr_in_ptr ptr b addrs}) =
  match ps with
  // The list cannot be empty because of the mem predicate
  | a::q -> if addr_in_ptr ptr a addrs then a else get_addr_ptr ptr addrs q

let store_buffer_aux_down_mem (ptr:int) (v:nat64) (s:low_state{valid_mem ptr s}) : Lemma (
  let mem1 = down_mem64 s.mem s.addrs s.ptrs in
  let h1 = store_mem_aux ptr s.ptrs v s.addrs s.mem in
  let mem2 = down_mem64 h1 s.addrs s.ptrs in
  forall j. j < ptr \/ j >= ptr + 8 ==> mem1.[j] == mem2.[j]) =
  let h1 = store_mem_aux ptr s.ptrs v s.addrs s.mem in
  let b = get_addr_ptr ptr s.addrs s.ptrs in
  let i = get_addr_in_ptr (B.length b) (buffer_addr b s.addrs) ptr 0 in
  let rec aux (ps:list buffer64{list_disjoint_or_eq ps /\ valid_mem_aux ptr ps s.addrs}) (h:HS.mem{list_live h ps}) :
  Lemma (let b = get_addr_ptr ptr s.addrs ps in
    let i = get_addr_in_ptr (B.length b) (buffer_addr b s.addrs) ptr 0 in
    store_mem_aux ptr ps v s.addrs h == buffer_write b i v h) =
    match ps with
    | [] -> ()
    | a::q ->
      if addr_in_ptr ptr a s.addrs then () else aux q h    
  in aux s.ptrs s.mem;
  store_buffer_down_mem b i v s.ptrs s.mem s.addrs

let store_buffer_aux_down_mem2 (ptr:int) (v:nat64) (s:low_state{valid_mem ptr s}) : Lemma (
  let h1 = store_mem_aux ptr s.ptrs v s.addrs s.mem in
  let mem2 = down_mem64 h1 s.addrs s.ptrs in
  M.get_heap_val ptr mem2 == v) =
  let b = get_addr_ptr ptr s.addrs s.ptrs in
  let i = get_addr_in_ptr (B.length b) (buffer_addr b s.addrs) ptr 0 in
  let h1 = store_mem_aux ptr s.ptrs v s.addrs s.mem in
  let mem2 = down_mem64 h1 s.addrs s.ptrs in
  let rec aux (ps:list buffer64{list_disjoint_or_eq ps /\ valid_mem_aux ptr ps s.addrs}) (h:HS.mem{list_live h ps}) :
  Lemma (let b = get_addr_ptr ptr s.addrs ps in
    let i = get_addr_in_ptr (B.length b) (buffer_addr b s.addrs) ptr 0 in
    store_mem_aux ptr ps v s.addrs h == buffer_write b i v h) =
    match ps with
    | [] -> ()
    | a::q ->
      if addr_in_ptr ptr a s.addrs then () else aux q h    
  in aux s.ptrs s.mem;
  assert (UInt64.v (Seq.index (B.as_seq h1 b) i) == v);
  ()
  
#set-options "--z3rlimit 60"

let lemma_valid_state_store_mem i v s =
  let s' = store_mem i v s in
  M.frame_update_heap i v s.s.M.mem;
  store_buffer_aux_down_mem i v s;
  store_buffer_aux_down_mem2 i v s;
  let mem1 = s'.s.M.mem in
  let mem2 = down_mem64 s'.mem s.addrs s.ptrs in
  M.same_mem_get_heap_val i mem1 mem2;
  assert (forall j. mem1.[j] == mem2.[j]);
  assert (Map.equal mem1 mem2);
  ()
  
