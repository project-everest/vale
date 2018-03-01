module Interop

(** Attempt to define down and up functions, to express relation between
    Low*'s and Vale's memory models.
    Currently only supports buffers of UInt8
*)


module List = FStar.List.Tot.Base

module HS = FStar.Monotonic.HyperStack
// module P = FStar.Pointer.Base
module B = FStar.Buffer
open Machine

open Vale_Sem

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

let sub l i = l - i

(**

TODO : This was the more generic version taking a variable number of parameters

(* Takes a Hyperstack and a buffer, and updates a low-level Vale heap
   with the contents of the buffer *)
val update_vale_mem: HS.mem -> P.(buffer (TBase TUInt8)) -> Vale_Sem.heap -> GTot Vale_Sem.heap

let update_vale_mem mem buf heap =
  let addr = P.buffer_as_addr buf in
  let length = P.buffer_length buf in
  let contents = P.buffer_as_seq mem buf in
  let rec aux (i:nat{i <= UInt32.v length}) curr_heap : GTot Vale_Sem.heap (decreases %[sub length i]) =
    if i >= (UInt32.v length) then curr_heap
    else
      aux (i+1) (curr_heap.[addr + i] <- FStar.Seq.index contents i)
  in aux 0 heap

(* Copy write_buffer from FStar.Pointer.Base, replacing Stack effect by Tot *)
assume val write_buffer
  (#t: P.typ)
  (b: P.buffer t)
  (i: UInt32.t)
  (v: P.type_of_typ t)
  (mem: HS.mem)
  : HS.mem

assume val write_spec
  (#t: P.typ)
  (b: P.buffer t)
  (i: UInt32.t)
  (v: P.type_of_typ t)
  (mem: HS.mem) : Lemma 
  (requires UInt32.v i < UInt32.v (P.buffer_length b))
  (ensures Seq.index (P.buffer_as_seq (write_buffer #t b i v mem) b) (UInt32.v i) == v )

(* Takes a buffer, the previous HyperStack, and a low-level Vale Heap, and reconstructs the buffer
   from the data in the Vale Heap *)
val reconstruct_buf: P.(buffer (TBase TUInt8)) -> HS.mem -> Vale_Sem.heap -> GTot HS.mem
let reconstruct_buf buf mem heap =
  let addr = P.buffer_as_addr buf in
  let length = P.buffer_length buf in
  let rec aux (i:nat{i <= UInt32.v length}) curr_mem : GTot HS.mem (decreases %[sub length i]) =
    if i >= (UInt32.v length) then curr_mem
    else
      aux (i+1) (write_buffer buf (UInt32.uint_to_t i) heap.[addr + i] curr_mem)
  in aux 0 mem

(* Takes a Low* Hyperstack, and a list of live buffers, and returns a low-level Vale heap
containing these buffers *)
val down_mem_list: HS.mem -> list P.(buffer (TBase TUInt8)) -> GTot Vale_Sem.heap

let down_mem_list mem buffers =
  (* Create a dummy heap *)
  let heap : heap = FStar.Map.const (UInt8.uint_to_t 0) in
  let heap = heap.[0] <- (UInt8.uint_to_t 1) in
  let rec aux bufs accu_heap : GTot (Vale_Sem.heap) = match bufs with
  | [] -> accu_heap
  | a :: q -> aux q (update_vale_mem mem a accu_heap)
  in aux buffers heap
  
(* Takes a low-level Vale Heap and the initial Hyperstack, and reconstructs the buffers in the HyperStack *)
val up_mem_list: Vale_Sem.heap -> list P.(buffer (TBase TUInt8)) -> HS.mem -> GTot HS.mem

let up_mem_list heap buffers mem =
  let rec aux bufs accu_mem heap : GTot HS.mem = match bufs with
    | [] -> accu_mem
    | a :: q -> aux q (reconstruct_buf a accu_mem heap) heap
  in aux buffers mem heap

**)

let rec write_vale_mem contents (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:Vale_Sem.heap{forall j. 0 <= j /\ j < i ==> curr_heap.[addr + j] == Seq.index contents j}) : GTot Vale_Sem.heap (decreases %[sub length i]) =
    if i >= length then curr_heap
    else
      write_vale_mem contents length addr (i+1) (curr_heap.[addr + i] <- FStar.Seq.index contents i)

let rec frame_write_vale_mem contents (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:Vale_Sem.heap{forall j. 0 <= j /\ j < i ==> curr_heap.[addr + j] == Seq.index contents j}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. j < addr \/ j >= addr + length ==> curr_heap.[j] == new_heap.[j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else frame_write_vale_mem contents length addr (i+1) (curr_heap.[addr+i] <- Seq.index contents i)

let rec load_store_write_vale_mem contents (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:Vale_Sem.heap{forall j. 0 <= j /\ j < i ==> curr_heap.[addr + j] == Seq.index contents j}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. 0 <= j /\ j < length ==> Seq.index contents j == new_heap.[addr + j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else load_store_write_vale_mem contents length addr (i+1)  (curr_heap.[addr+i] <- Seq.index contents i)

val correct_down: HS.mem -> B.buffer UInt8.t -> B.buffer UInt8.t -> Vale_Sem.heap * nat64 * nat64 -> Type0
let correct_down mem ptr1 ptr2 res =
  let heap, addr1, addr2 = res in
  let length1 = B.length ptr1 in
  let length2 = B.length ptr2 in
  let contents1 = B.as_seq mem ptr1 in
  let contents2 = B.as_seq mem ptr2 in
  (forall i.  0 <= i /\ i < length1 ==> heap.[addr1 + i] == FStar.Seq.index contents1 i) /\
  (forall i.  0 <= i /\ i < length2 ==> heap.[addr2 + i] == FStar.Seq.index contents2 i)

(* Takes a Low* Hyperstack and two buffers (for the moment) and create a vale memory + keep track of the vale addresses *)
val down_mem: (mem:HS.mem) -> (ptr1:B.buffer UInt8.t) -> (ptr2:B.buffer UInt8.t) -> GTot (res: (Vale_Sem.heap * nat64 * nat64){correct_down mem ptr1 ptr2 res})

#set-options "--z3rlimit 40"

let down_mem mem ptr1 ptr2 =
  (* Dummy heap *)
  let heap : heap = FStar.Map.const (UInt8.uint_to_t 0) in
  let length1 = B.length ptr1 in
  let length2 = B.length ptr2 in
  let contents1 = B.as_seq mem ptr1 in
  let contents2 = B.as_seq mem ptr2 in
  let addr1 = 0 in
  let addr2 = length1 in
  let heap1 = write_vale_mem contents1 length1 addr1 0 heap in
  load_store_write_vale_mem contents1 length1 addr1 0 heap;
  let heap2 = write_vale_mem contents2 length2 addr2 0 heap1 in
  frame_write_vale_mem contents2 length2 addr2 0 heap1;
  load_store_write_vale_mem contents2 length2 addr2 0 heap1;
  heap2, addr1, addr2

(* Takes a Low* Hyperstack and two buffers (for the moment) and create a vale state *)
val down: HS.mem -> B.buffer UInt8.t -> B.buffer UInt8.t -> GTot Vale_Sem.state

let down mem ptr1 ptr2 =
  let heap, addr1, addr2 = down_mem mem ptr1 ptr2 in
  Vale_Sem.Mkstate true (fun x -> if x = Rax then addr1 else if x = Rbx then addr2 else 0) heap 

assume val upd: #a:Type -> b:B.buffer a -> (n:nat{n < B.length b}) -> z:a -> h0:HS.mem -> 
  (h1:HS.mem{B.modifies_1 b h0 h1 /\ B.as_seq h1 b == Seq.upd (B.as_seq h0 b) n z })

let rec write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (i:nat{i <= length}) curr_mem : GTot HS.mem (decreases %[sub length i]) = 
  if i >= length then curr_mem
  else
    write_low_mem heap length addr buf (i+1) (upd buf i heap.[addr + i] curr_mem)

val up_mem: Vale_Sem.heap -> (ptr1: B.buffer UInt8.t) -> nat64 -> (ptr2: (B.buffer UInt8.t){B.disjoint ptr1 ptr2}) -> nat64 -> HS.mem -> GTot HS.mem

let up_mem heap ptr1 addr1 ptr2 addr2 mem =
  let length1 = B.length ptr1 in
  let length2 = B.length ptr2 in
  let mem1 = write_low_mem heap length1 addr1 ptr1 0 mem in
  let mem2 = write_low_mem heap length2 addr2 ptr2 0 mem in
  mem2

val down_up_identity: (mem:HS.mem) -> (ptr1:B.buffer UInt8.t) -> (ptr2:(B.buffer UInt8.t){B.disjoint ptr1 ptr2}) -> Lemma 
  (let heap, addr1, addr2 = down_mem mem ptr1 ptr2 in let new_mem = up_mem heap ptr1 addr1 ptr2 addr2 mem in
    new_mem == mem)

let down_up_identity mem ptr1 ptr2 =
  let heap, addr1, addr2 = down_mem mem ptr1 ptr2 in let new_mem = up_mem heap ptr1 addr1 ptr2 addr2 mem in
  assume (B.length ptr1 > 0); 
  assert (heap.[addr1] == Seq.index (B.as_seq mem ptr1) 0);
  // assert (Seq.index (P.buffer_as_seq mem ptr1) 0 == Seq.index (P.buffer_as_seq new_mem ptr1) 0);
  // assert (forall i. 0 <= i /\ i < UInt32.v (P.buffer_length ptr1) ==> Seq.index (P.buffer_as_seq mem ptr1) i == Seq.index (P.buffer_as_seq new_mem ptr1) i);
  // assert (P.buffer_as_seq mem ptr1 == P.buffer_as_seq new_mem ptr1);
  admit()
