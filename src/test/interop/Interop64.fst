module Interop64

(** Test of the interop with buffers of UInt64 *)

module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module B = FStar.Buffer

open Machine_int
open Vale_Sem

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

let sub l i = l - i

let disjoint_or_eq ptr1 ptr2 = B.disjoint ptr1 ptr2 \/ ptr1 == ptr2

let list_disjoint_or_eq (#a:Type0) (ptrs:list (B.buffer a)) =
  forall p1 p2. List.memP p1 ptrs /\ List.memP p2 ptrs ==> disjoint_or_eq p1 p2

(* Abstract maps linking buffers to addresses in the Vale heap. A buffer is uniquely identified by its address, idx and length. TODO : Add Type? *)
type buffer_triple = nat * nat * nat
let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + (8 `op_Multiply` length1) < addr2 || addr2 + (8 `op_Multiply` length2) < addr1

type addr_map = (m:(Map.t buffer_triple nat64){forall (buf1 buf2:B.buffer UInt64.t). B.disjoint buf1 buf2 ==> disjoint_addr (m.[(B.as_addr buf1, B.idx buf1, B.length buf1)]) (B.length buf1)
  (m.[(B.as_addr buf2, B.idx buf2, B.length buf2)]) (B.length buf2)})

(* Additional hypotheses, which should be added to the corresponding libraries at some point *)

(* If two refs have the same address, and are in the heap, they are equal *)
assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma 
  (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

let word_to_bytes (v:UInt64.t) : (s: Seq.seq UInt8.t{Seq.length s = 8}) =
  let s = Seq.create 8 (UInt8.uint_to_t (UInt.zero 8)) in
  let v = UInt64.v v in
  let s0 = UInt8.uint_to_t (v % 0x100) in
  let v = v / 0x100 in 
  let s1 = UInt8.uint_to_t (v % 0x100) in
  let v = v / 0x100 in
  let s2 = UInt8.uint_to_t (v % 0x100) in
  let v = v / 0x100 in
  let s3 = UInt8.uint_to_t (v % 0x100) in
  let v = v / 0x100 in
  let s4 = UInt8.uint_to_t (v % 0x100) in
  let v = v / 0x100 in
  let s5 = UInt8.uint_to_t (v % 0x100) in
  let v = v / 0x100 in
  let s6 = UInt8.uint_to_t (v % 0x100) in
  let v = v / 0x100 in
  let s7 = UInt8.uint_to_t (v % 0x100) in
  let v = v / 0x100 in
  let s = Seq.upd s 0 s0 in
  let s = Seq.upd s 1 s1 in
  let s = Seq.upd s 2 s2 in
  let s = Seq.upd s 3 s3 in
  let s = Seq.upd s 4 s4 in
  let s = Seq.upd s 5 s5 in
  let s = Seq.upd s 6 s6 in
  let s = Seq.upd s 7 s7 in  
  s
  


let rec write_vale64 (v:UInt64.t) addr (heap:Vale_Sem.heap) : Tot Vale_Sem.heap = 
  let v' = word_to_bytes v in
  let heap = heap.[addr] <- Seq.index v' 0 in
  let heap = heap.[addr + 1] <- Seq.index v' 1 in
  let heap = heap.[addr + 2] <- Seq.index v' 2 in
  let heap = heap.[addr + 3] <- Seq.index v' 3 in
  let heap = heap.[addr + 4] <- Seq.index v' 4 in
  let heap = heap.[addr + 5] <- Seq.index v' 5 in
  let heap = heap.[addr + 6] <- Seq.index v' 6 in  
  let heap = heap.[addr + 7] <- Seq.index v' 7 in  
  heap
