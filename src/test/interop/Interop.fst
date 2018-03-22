module Interop

(** Attempt to define down and up functions, to express relation between
    Low*'s and Vale's memory models.
    Currently only supports buffers of UInt8
*)


module List = FStar.List.Tot.Base

module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
// module P = FStar.Pointer.Base
module B = FStar.Buffer
open Machine

open Vale_Sem

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

let sub l i = l - i

(* Abstract maps linking buffers to addresses in the Vale heap. A buffer is uniquely identified by its address, idx and length. TODO : Add Type? *)
type buffer_triple = nat * nat * nat
let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 || addr2 + length2 < addr1

type addr_map = (m:(Map.t buffer_triple nat64){forall (buf1 buf2:B.buffer UInt8.t). B.disjoint buf1 buf2 ==> disjoint_addr (m.[(B.as_addr buf1, B.idx buf1, B.length buf1)]) (B.length buf1)
  (m.[(B.as_addr buf2, B.idx buf2, B.length buf2)]) (B.length buf2)})

(* Additional hypotheses, which should be added to the corresponding libraries at some point *)

assume val lemma_aux: #a:Type -> b:B.buffer a -> n:nat{n < B.length b} -> z:a
  -> h0:HS.mem -> Lemma
  (requires (B.live h0 b))
  (ensures (B.live h0 b
    /\ B.modifies_1 b h0 (HS.upd h0 (B.content b) (Seq.upd (B.sel h0 b) (B.idx b + n) z)) ))

(* Tot version of upd for Hyperstacks *)
val upd_tot: #a:Type -> b:B.buffer a -> (n:nat{n < B.length b}) -> z:a -> (h0:HS.mem{B.live h0 b}) -> GTot
  (h1:HS.mem{B.modifies_1 b h0 h1 /\ B.as_seq h1 b == Seq.upd (B.as_seq h0 b) n z /\ B.live h1 b /\ HyperStack.ST.equal_domains h0 h1})

(* The assumes would very likely be proven directly with access to the private elements of FStar.Buffer *)
let upd_tot #a b n z h0 =
  let s0 = B.sel h0 b in
  assume (B.idx b + B.length b <= B.max_length b);
  assume (B.max_length b == Seq.Base.length s0);
  assume (0 <= B.idx b + n /\ B.idx b + n < B.max_length b);
  let s = Seq.upd s0 (B.idx b + n) z in
  assume (HS.live_region h0 (B.frameOf b));
  let h1 = HS.upd h0 (B.content b) s in
  lemma_aux #a b n z h0;
  h1

(* If two refs have the same address, and are in the heap, they are equal *)
assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma 
  (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

assume val lemma_sel_upd_extensionality (#a:Type) (#rel:Preorder.preorder a) (h:HS.mem) (r:HS.mreference a rel{h `HS.contains` r})
 :Lemma (requires True) (ensures (HS.upd h r (HS.sel h r) == h))
        [SMTPat (HS.upd h r (HS.sel h r))]

assume val lemma_upd_cancel (#a:Type) (#rel:Preorder.preorder a) (h:HS.mem) (r:HS.mreference a rel{h `HS.contains` r}) (x y:a)
 :Lemma (requires True) (ensures (HS.upd (HS.upd h r x) r y ==
                               HS.upd h r y))
     [SMTPat (HS.upd (HS.upd h r x) r y)]

assume val lemma_upd_commute (#a:Type) (#rel:Preorder.preorder a) (h:HS.mem) (r1:HS.mreference a rel{h `HS.contains` r1}) (r2:HS.mreference a rel{h `HS.contains` r2}) (x y:a)
 :Lemma (requires (HS.as_addr r1 <> HS.as_addr r2))
        (ensures (HS.upd (HS.upd h r1 x) r2 y ==
                  HS.upd (HS.upd h r2 y) r1 x))
     [SMTPat (HS.upd (HS.upd h r1 x) r2 y)]

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

(* Write a buffer in the vale memory *)

let rec write_vale_mem contents (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:Vale_Sem.heap{forall j. 0 <= j /\ j < i ==> curr_heap.[addr + j] == Seq.index contents j}) : Tot Vale_Sem.heap (decreases %[sub length i]) =
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

logic val correct_down: HS.mem -> addr_map -> B.buffer UInt8.t -> B.buffer UInt8.t -> Vale_Sem.heap -> Type0
logic let correct_down mem addrs ptr1 ptr2 heap =
  let length1 = B.length ptr1 in
  let length2 = B.length ptr2 in
  let contents1 = B.as_seq mem ptr1 in
  let contents2 = B.as_seq mem ptr2 in
  let addr1 = addrs.[(B.as_addr ptr1, B.idx ptr1, B.length ptr1)] in
  let addr2 = addrs.[(B.as_addr ptr2, B.idx ptr2, B.length ptr2)] in
  (forall i.  0 <= i /\ i < length1 ==> heap.[addr1 + i] == FStar.Seq.index contents1 i) /\
  (forall i.  0 <= i /\ i < length2 ==> heap.[addr2 + i] == FStar.Seq.index contents2 i)

(* Takes a Low* Hyperstack and two buffers (for the moment) and create a vale memory + keep track of the vale addresses *)
val down_mem: (mem:HS.mem) -> (addrs: addr_map) -> (ptr1:B.buffer UInt8.t) -> (ptr2:B.buffer UInt8.t{B.disjoint ptr1 ptr2}) -> GTot (heap :Vale_Sem.heap {correct_down mem addrs ptr1 ptr2 heap})

#set-options "--z3rlimit 40"

let down_mem mem addrs ptr1 ptr2 =
  (* Dummy heap *)
  let heap : heap = FStar.Map.const (UInt8.uint_to_t 0) in
  let length1 = B.length ptr1 in
  let length2 = B.length ptr2 in
  let contents1 = B.as_seq mem ptr1 in
  let contents2 = B.as_seq mem ptr2 in
  let addr1 = addrs.[(B.as_addr ptr1, B.idx ptr1, B.length ptr1)] in
  let addr2 = addrs.[(B.as_addr ptr2, B.idx ptr2, B.length ptr2)] in
  let heap1 = write_vale_mem contents1 length1 addr1 0 heap in
  load_store_write_vale_mem contents1 length1 addr1 0 heap;
  let heap2 = write_vale_mem contents2 length2 addr2 0 heap1 in
  frame_write_vale_mem contents2 length2 addr2 0 heap1;
  load_store_write_vale_mem contents2 length2 addr2 0 heap1;
  heap2

let create_seq (#a:Type0) heap length addr : Tot (s':Seq.seq a{Seq.length s' = length /\ 
  (forall j. 0 <= j /\ j < length ==> Seq.index s' j == heap.[addr + j])}) =
  let rec aux (#a:Type0) heap length addr (i:nat{i <= length}) (s:Seq.seq a{Seq.length s = i /\ 
    (forall j. 0 <= j /\ j < i ==> Seq.index s j == heap.[addr + j])}) : Tot (s':Seq.seq a{Seq.length s' = length /\ 
    (forall j. 0 <= j /\ j < length ==> Seq.index s' j == heap.[addr + j])}) (decreases %[sub length i]) =
  if i = length then s
    else
    let s' = Seq.append s (Seq.create 1 (heap.[addr + i])) in
    aux heap length addr (i+1) s'
  in aux heap length addr 0 Seq.createEmpty

let rec write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (curr_mem:HS.mem{B.live curr_mem buf}) : GTot HS.mem = 
  let s = B.sel curr_mem buf in
  let modified = create_seq heap length addr in
  let lo = Seq.slice s 0 (B.idx buf) in
  let hi = Seq.slice s (B.idx buf + length) (B.max_length buf) in
  let s' = Seq.append lo (Seq.append modified hi) in
  HS.upd curr_mem (B.content buf) s'

let frame_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (mem:HS.mem{B.live mem buf}) : Lemma
  (let new_mem = write_low_mem heap length addr buf mem in
    forall (b:(B.buffer UInt8.t){B.live mem b /\ B.disjoint b buf}). B.equal mem b new_mem b) =
    let new_mem = write_low_mem heap length addr buf mem in
    let rec aux (b : B.buffer UInt8.t{B.live mem b /\ B.disjoint b buf}) : Lemma (B.equal mem b new_mem b) =
      if B.as_addr b <> B.as_addr buf || B.frameOf b <> B.frameOf buf then ()
      else begin
	ref_extensionality (Map.sel mem.HS.h (B.frameOf b)) (B.as_ref buf) (B.as_ref b);
	assert (forall i. i + B.idx b - B.idx b = i);
	assert (Seq.equal (B.as_seq mem b) (B.as_seq new_mem b));
	()
      end
    in Classical.forall_intro aux

let load_store_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (mem:HS.mem{B.live mem buf}) : Lemma
  (let new_mem = write_low_mem heap length addr buf mem in
    forall j. 0 <= j /\ j < length ==> Seq.index (B.as_seq new_mem buf) j == heap.[addr + j]) = ()

let invariant_write_low_memheap heap length addr (b:(B.buffer UInt8.t){length = B.length b}) (mem:HS.mem{B.live mem b}) : Lemma
  (requires (forall i. 0 <= i /\ i < B.length b ==> Seq.index (B.as_seq mem b) i == heap.[addr + i]))
  (ensures (mem == write_low_mem heap length addr b mem)) 
  [SMTPat (mem == write_low_mem heap length addr b mem)]
  =
  let new_mem = write_low_mem heap length addr b mem in	  
  let s = B.sel mem b in
  let s' = B.sel new_mem b in
  let lo_i = Seq.slice s 0 (B.idx b) in
  let hi_i = Seq.slice s (B.idx b + length) (B.max_length b) in
  let mi_create = create_seq heap length addr in
  let s_app = Seq.append lo_i (Seq.append mi_create hi_i) in
  assert (Seq.equal (HS.sel mem (B.content b)) s_app);
  ()

logic let correct_up mem (addrs:addr_map) buf1 buf2 new_mem heap =
  let length1 = B.length buf1 in
  let length2 = B.length buf2 in
  let addr1 = addrs.[(B.as_addr buf1, B.idx buf1, B.length buf1)] in
  let addr2 = addrs.[(B.as_addr buf2, B.idx buf2, B.length buf2)] in  
  (forall j. 0 <= j /\ j < length1 ==> Seq.index (B.as_seq new_mem buf1) j == heap.[addr1 + j])
  /\ (forall j. 0 <= j /\ j < length2 ==> Seq.index (B.as_seq new_mem buf2) j == heap.[addr2 + j])

val up_mem: (heap:Vale_Sem.heap) -> (addrs:addr_map) -> (ptr1: B.buffer UInt8.t) -> (ptr2: (B.buffer UInt8.t){B.disjoint ptr1 ptr2}) -> (mem:HS.mem{B.live mem ptr1 /\ B.live mem ptr2}) -> GTot (new_mem:HS.mem{correct_up mem addrs ptr1 ptr2 new_mem heap})

#set-options "--z3rlimit 100 --z3refresh"

(* The unused variable addr1 is needed for the postcondition to verify ?! *)
let up_mem heap addrs ptr1 ptr2 mem = 
  let length1 = B.length ptr1 in
  let length2 = B.length ptr2 in
  let addr1 = addrs.[(B.as_addr ptr1, B.idx ptr1, B.length ptr1)] in
  let addr2 = addrs.[(B.as_addr ptr2, B.idx ptr2, B.length ptr2)] in  
  let mem1 = write_low_mem heap length1 addr1 ptr1 mem in
  frame_write_low_mem heap length1 addr1 ptr1 mem;
  load_store_write_low_mem heap length1 addr1 ptr1 mem;
  assert(forall j. 0 <= j /\ j < length1 ==> Seq.index (B.as_seq mem1 ptr1) j == heap.[addr1 + j]);
  let mem2 = write_low_mem heap length2 addr2 ptr2 mem1 in
  assert (B.live mem1 ptr1);
  frame_write_low_mem heap length2 addr2 ptr2 mem1;
  load_store_write_low_mem heap length2 addr2 ptr2 mem1;
  assert (B.equal mem1 ptr1 mem2 ptr1);
  mem2

val down_up_identity: (mem:HS.mem) -> (addrs:addr_map) -> (ptr1:(B.buffer UInt8.t){B.live mem ptr1})  -> (ptr2:(B.buffer UInt8.t){B.live mem ptr2 /\ B.disjoint ptr1 ptr2}) -> Lemma 
  (let heap = down_mem mem addrs ptr1 ptr2 in 
   let length1 = B.length ptr1 in
   let length2 = B.length ptr2 in
   let addr1 = addrs.[(B.as_addr ptr1, B.idx ptr1, B.length ptr1)] in
   let addr2 = addrs.[(B.as_addr ptr2, B.idx ptr2, B.length ptr2)] in     
   let new_mem = up_mem heap addrs ptr1 ptr2 mem in
    mem == new_mem)
  
let down_up_identity mem addrs ptr1 ptr2 =
  let heap = down_mem mem addrs ptr1 ptr2 in 
  let new_mem = up_mem heap addrs ptr1 ptr2 mem in
  let length1 = B.length ptr1 in
  let length2 = B.length ptr2 in
  let addr1 = addrs.[(B.as_addr ptr1, B.idx ptr1, B.length ptr1)] in
  let addr2 = addrs.[(B.as_addr ptr2, B.idx ptr2, B.length ptr2)] in   
  let b1 = B.content ptr1 in
  let b2 = B.content ptr2 in
  invariant_write_low_memheap heap length1 addr1 ptr1 mem;
  let mem1 = write_low_mem heap length1 addr1 ptr1 mem in
  invariant_write_low_memheap heap length2 addr2 ptr2 mem;
  ()
