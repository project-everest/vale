module Interop

(** Attempt to define down and up functions, to express relation between
    Low*'s and Vale's memory models.
    Currently only supports buffers of UInt8
*)


module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer

open Opaque_s
open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Bytes_Semantics_i

#reset-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

let sub l i = l - i

unfold
let disjoint_or_eq ptr1 ptr2 = B.disjoint ptr1 ptr2 \/ ptr1 == ptr2

let list_disjoint_or_eq (#a:Type0) (ptrs:list (B.buffer a)) =
  forall p1 p2. List.memP p1 ptrs /\ List.memP p2 ptrs ==> disjoint_or_eq p1 p2

let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 || addr2 + length2 < addr1

type addr_map = (m:((B.buffer UInt8.t) -> nat64){
  forall (buf1 buf2:B.buffer UInt8.t). B.disjoint buf1 buf2 ==> 
    disjoint_addr (m buf1) (B.length buf1) (m buf2) (B.length buf2)})

unfold
let list_live mem ptrs = forall p . List.memP p ptrs ==> B.live mem p

(* Additional hypotheses, which should be added to the corresponding libraries at some point *)

(* If two refs have the same address, and are in the heap, they are equal *)
assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma 
  (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

(* Write a buffer in the vale memory *)

let rec write_vale_mem (contents:Seq.seq UInt8.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 
	0 <= j /\ j < i ==> curr_heap.[addr+j] == UInt8.v (Seq.index contents j)}) : Tot heap (decreases %[sub length i]) =
    if i >= length then curr_heap
    else (
      let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
      assert (Set.equal (Map.domain heap) (Set.complement Set.empty));
      write_vale_mem contents length addr (i+1) heap
    )      

let rec frame_write_vale_mem (contents:Seq.seq UInt8.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. j < addr \/ j >= addr + length ==> curr_heap.[j] == new_heap.[j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
	let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
	assert (Set.equal (Map.domain heap) (Set.complement Set.empty));      
	frame_write_vale_mem contents length addr (i+1) heap
      end
      
let rec load_store_write_vale_mem 
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. 0 <= j /\ j < length ==> UInt8.v (Seq.index contents j) == new_heap.[addr + j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
	let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
	assert (Set.equal (Map.domain heap) (Set.complement Set.empty));      
	load_store_write_vale_mem contents length addr (i+1) heap
      end

let correct_down_p (mem:HS.mem) (addrs:addr_map) (heap:heap) (p:B.buffer UInt8.t) =
  let length = B.length p in
  let contents = B.as_seq mem p in
  let addr = addrs p in
  (forall i.  0 <= i /\ i < length ==> heap.[addr + i] == UInt8.v (FStar.Seq.index contents i))

#set-options "--z3rlimit 40"

let correct_down_p_cancel mem (addrs:addr_map) heap (p:B.buffer UInt8.t) : Lemma
  (forall p'. p == p' ==>       
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) = 
  let rec aux (p':B.buffer UInt8.t) : Lemma 
    (p == p'  ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs p in
        let new_heap = write_vale_mem contents length addr 0 heap in
	load_store_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux
      
let correct_down_p_frame mem (addrs:addr_map) (heap:heap) (p:B.buffer UInt8.t) : Lemma
  (forall p'. B.disjoint p p' /\ correct_down_p mem addrs heap p' ==>       
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) = 
  let rec aux (p':B.buffer UInt8.t) : Lemma 
    (B.disjoint p p' /\ correct_down_p mem addrs heap p' ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs p in
        let new_heap = write_vale_mem contents length addr 0 heap in
	frame_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux

let correct_down mem (addrs:addr_map) (ptrs: list (B.buffer UInt8.t)) heap =
  forall p. List.memP p ptrs ==> correct_down_p mem addrs heap p

(* Takes a Low* Hyperstack and two buffers (for the moment) and create a vale memory + keep track of the vale addresses *)
val down_mem: (mem:HS.mem) -> (addrs: addr_map) -> (ptrs:list (B.buffer UInt8.t){list_disjoint_or_eq ptrs}) -> GTot (heap :heap {correct_down mem addrs ptrs heap})

let rec down_mem_aux (ptrs:list (B.buffer UInt8.t){list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (ps:list (B.buffer UInt8.t))
  (accu:list (B.buffer UInt8.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{correct_down mem addrs accu h}) : 
  GTot (heap:heap{correct_down mem addrs ptrs heap}) =
  match ps with
    | [] -> h
    | a::q ->
      let length = B.length a in
      let contents = B.as_seq mem a in
      let addr = addrs a in
      let new_heap = write_vale_mem contents length addr 0 h in
      load_store_write_vale_mem contents length addr 0 h;
      correct_down_p_cancel mem addrs h a;
      correct_down_p_frame mem addrs h a;
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
      down_mem_aux ptrs addrs mem q (a::accu) new_heap

let down_mem mem addrs ptrs =
  (* Dummy heap *)
  let heap = FStar.Map.const 0 in
  assert (Set.equal (Map.domain heap) (Set.complement Set.empty));
  let (heap:X64.Bytes_Semantics_s.heap) = heap in
  down_mem_aux ptrs addrs mem ptrs [] heap

val unspecified_down:
  (mem:HS.mem) ->
  (addrs:addr_map) ->
  (ptrs: list (B.buffer UInt8.t){list_disjoint_or_eq ptrs}) ->
  Lemma (
    let heap = down_mem mem addrs ptrs in
    forall i. (
      forall (b:B.buffer UInt8.t{List.memP b ptrs}).
        let base = addrs b in
	i < base \/ i >= base + B.length b) ==>
      heap.[i] == 0)

private
let rec frame_down_mem_aux
  (ptrs:list (B.buffer UInt8.t){list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (ps:list (B.buffer UInt8.t))
  (accu: list (B.buffer UInt8.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{correct_down mem addrs accu h}) :
  Lemma (
    let heap = down_mem_aux ptrs addrs mem ps accu h in
    forall i. (forall (b:B.buffer UInt8.t{List.memP b ps}).
      let base = addrs b in
      i < base \/ i >= base + B.length b) ==>
    heap.[i] == h.[i]) =
  match ps with
  | [] -> ()
  | a::q -> 
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs a in
    let new_heap = write_vale_mem contents length addr 0 h in
    frame_write_vale_mem contents length addr 0 h;
    correct_down_p_cancel mem addrs h a;
    correct_down_p_frame mem addrs h a;    
    assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
    frame_down_mem_aux ptrs addrs mem q (a::accu) new_heap;
    ()

let unspecified_down mem addrs ptrs =
  let heap = Map.const 0 in
  assert (Set.equal (Map.domain heap) (Set.complement Set.empty));
  let (heap:X64.Bytes_Semantics_s.heap) = heap in      
  frame_down_mem_aux ptrs addrs mem ptrs [] heap
  
val same_unspecified_down: 
  (mem1: HS.mem) -> 
  (mem2: HS.mem) -> 
  (addrs:addr_map) ->
  (ptrs:list (B.buffer UInt8.t){list_disjoint_or_eq ptrs}) ->
  Lemma (
    let heap1 = down_mem mem1 addrs ptrs in
    let heap2 = down_mem mem2 addrs ptrs in
    forall i. (forall (b:B.buffer UInt8.t{List.memP b ptrs}). 
      let base = addrs b in
      i < base \/ i >= base + B.length b) ==>
      heap1.[i] == heap2.[i])

let same_unspecified_down mem1 mem2 addrs ptrs =
  unspecified_down mem1 addrs ptrs;
  unspecified_down mem2 addrs ptrs
