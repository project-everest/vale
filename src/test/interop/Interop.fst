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

open FStar.Tactics

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

logic val correct_down: HS.mem -> B.buffer UInt8.t -> B.buffer UInt8.t -> Vale_Sem.heap * nat64 * nat64 -> Type0
logic let correct_down mem ptr1 ptr2 res =
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

(* Stateful version
val write_low_mem: (heap:Vale_Sem.heap) -> (length:nat) -> (addr:nat) -> (buf:(B.buffer UInt8.t){length = B.length buf}) -> (i:nat{i <= length}) -> HyperStack.ST.Stack unit
  (requires (fun h -> B.live h buf /\
    (forall j. 0 <= j /\ j < i ==> Seq.index (B.as_seq h buf) j == heap.[addr + j])
  ))
  (ensures (fun h0 _ h1 -> B.live h0 buf /\ B.live h1 buf
    /\ (forall (b:(B.buffer UInt8.t){B.live h0 b}). B.disjoint b buf ==> B.equal h0 b h1 b)
    /\ (forall j. 0 <= j /\ j < length ==> Seq.index (B.as_seq h1 buf) j == heap.[addr + j])
    /\ (forall (b:(B.buffer UInt8.t)). B.live h0 b ==> B.live h1 b)
    /\ HyperStack.ST.equal_domains h0 h1
  ))
  (decreases %[sub length i])

let rec write_low_mem heap length addr buf i  = 
  if i >= length then ()
  else begin
    B.upd buf (UInt32.uint_to_t (UInt.to_uint_t 32 i)) heap.[addr + i];
    write_low_mem heap length addr buf (i+1)
  end
*)

assume val lemma_aux: #a:Type -> b:B.buffer a -> n:nat{n < B.length b} -> z:a
  -> h0:HS.mem -> Lemma
  (requires (B.live h0 b))
  (ensures (B.live h0 b
    /\ B.modifies_1 b h0 (HS.upd h0 (B.content b) (Seq.upd (B.sel h0 b) (B.idx b + n) z)) ))

val upd_tot: #a:Type -> b:B.buffer a -> (n:nat{n < B.length b}) -> z:a -> (h0:HS.mem{B.live h0 b}) -> GTot
  (h1:HS.mem{B.modifies_1 b h0 h1 /\ B.as_seq h1 b == Seq.upd (B.as_seq h0 b) n z /\ B.live h1 b /\ HyperStack.ST.equal_domains h0 h1})
  
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
  

let rec write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (i:nat{i <= length}) (curr_mem:HS.mem{B.live curr_mem buf}) : GTot HS.mem (decreases %[sub length i]) = 
  if i >= length then curr_mem
  else
    write_low_mem heap length addr buf (i+1) (upd_tot buf i heap.[addr + i] curr_mem)

let rec frame_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (i:nat{i <= length}) (mem:HS.mem{B.live mem buf}) : Lemma
  (requires True)
  (ensures (let new_mem = write_low_mem heap length addr buf i mem in
    forall (b:(B.buffer UInt8.t){B.live mem b}). B.disjoint b buf ==> B.equal mem b new_mem b))
  (decreases %[sub length i]) =
    if i >= length then ()
    else begin
      let new_mem = upd_tot buf i heap.[addr+i] mem in
      frame_write_low_mem heap length addr buf (i+1) new_mem
    end

let rec load_store_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (i:nat{i <= length}) (mem:HS.mem{B.live mem buf}) : Lemma
  (requires forall j. 0 <= j /\ j < i ==> Seq.index (B.as_seq mem buf) j == heap.[addr + j])
  (ensures (let new_mem = write_low_mem heap length addr buf i mem in
    forall j. 0 <= j /\ j < length ==> Seq.index (B.as_seq new_mem buf) j == heap.[addr + j]))
  (decreases %[sub length i]) =
  if i >= length then ()
  else begin
    let new_mem = upd_tot buf i heap.[addr + i] mem in
    load_store_write_low_mem heap length addr buf (i+1) new_mem
  end

let rec live_preserved_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (i:nat{i <= length}) (mem:HS.mem{B.live mem buf}) : Lemma
  (requires True)
  (ensures (let new_mem = write_low_mem heap length addr buf i mem in
    forall (b:(B.buffer UInt8.t)). B.live mem b ==> B.live new_mem b))
  (decreases %[sub length i]) =
    if i >= length then ()
    else begin
      let new_mem = upd_tot buf i heap.[addr + i] mem in
      B.lemma_reveal_modifies_1 buf mem new_mem;
      live_preserved_write_low_mem heap length addr buf (i+1) new_mem
    end

let rec equal_domains_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (i:nat{i <= length}) (mem:HS.mem{B.live mem buf}) : Lemma
  (requires True)
  (ensures (let new_mem = write_low_mem heap length addr buf i mem in
    HyperStack.ST.equal_domains mem new_mem))
  (decreases %[sub length i]) =
    if i >= length then ()
    else begin
      let new_mem = upd_tot buf i heap.[addr + i] mem in
      equal_domains_write_low_mem heap length addr buf (i+1) new_mem
    end

let rec modifies_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (i:nat{i <= length}) (mem:HS.mem{B.live mem buf}) : Lemma
  (requires True)
  (ensures (let new_mem = write_low_mem heap length addr buf i mem in
    B.modifies_1 buf mem new_mem))
  (decreases %[sub length i]) =
    if i >= length then ()
    else begin
      let new_mem = upd_tot buf i heap.[addr + i] mem in
      modifies_write_low_mem heap length addr buf (i+1) new_mem
    end

let rec underlying_seq_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (i:nat{i <= length}) (mem:HS.mem{B.live mem buf}) : Lemma
  (requires True)
  (ensures (let new_mem = write_low_mem heap length addr buf i mem in
    let s0 = B.sel mem buf in
    let s1 = B.sel new_mem buf in
    (forall j. 0 <= j /\ j < B.idx buf ==> Seq.index s0 j == Seq.index s1 j) /\
    (forall j. B.idx buf + length <= j /\ j < Seq.length s0 ==> Seq.index s0 j == Seq.index s1 j)))
  (decreases %[sub length i]) =
    if i >= length then ()
    else begin
      let new_mem = upd_tot buf i heap.[addr + i] mem in
      underlying_seq_write_low_mem heap length addr buf (i+1) new_mem
    end

let equal_non_seq_buf mem new_mem buf =
  let s0 = B.sel mem buf in
  let s1 = B.sel new_mem buf in
  (forall j. {:pattern (Seq.index s0 j == Seq.index s1 j)} 0 <= j /\ j < B.idx buf ==> Seq.index s0 j == Seq.index s1 j) /\
  (forall j. {:pattern (Seq.index s0 j == Seq.index s1 j)} B.idx buf + B.length buf <= j /\ j < Seq.length s0 ==> Seq.index s0 j == Seq.index s1 j)

let equal_non_seq_bufs mem new_mem buf1 buf2 =
  if B.frameOf buf1 <> B.frameOf buf2 || B.as_addr buf1 <> B.as_addr buf2 then begin
    equal_non_seq_buf mem new_mem buf1 /\ equal_non_seq_buf mem new_mem buf2
  end
  else begin
    forall i. 0 <= i /\ i < B.max_length buf1 /\ i < B.max_length buf2 ==>
      not (i >= B.idx buf1 && i < B.idx buf1 + B.length buf1) ==>
      not (i >= B.idx buf2 && i < B.idx buf2 + B.length buf2) ==>
      Seq.index (B.sel mem buf1) i == Seq.index (B.sel new_mem buf1) i /\
      Seq.index (B.sel mem buf2) i == Seq.index (B.sel new_mem buf2) i
  end

logic let correct_up mem buf1 buf2 new_mem heap addr1 addr2 =
  let length1 = B.length buf1 in
  let length2 = B.length buf2 in
  forall (b:(B.buffer UInt8.t){B.live mem b}). (B.disjoint b buf1 /\ B.disjoint b buf2 ==> B.equal mem b new_mem b)
  /\ (forall j. 0 <= j /\ j < length1 ==> Seq.index (B.as_seq new_mem buf1) j == heap.[addr1 + j])
  /\ (forall j. 0 <= j /\ j < length2 ==> Seq.index (B.as_seq new_mem buf2) j == heap.[addr2 + j])
  /\ HyperStack.ST.equal_domains mem new_mem
  /\ equal_non_seq_bufs mem new_mem buf1 buf2
  /\ B.modifies_2 buf1 buf2 mem new_mem

assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

val up_mem: (heap:Vale_Sem.heap) -> (ptr1: B.buffer UInt8.t) -> (addr1:nat64) -> (ptr2: (B.buffer UInt8.t){B.disjoint ptr1 ptr2}) -> (addr2:nat64) 
  -> (length1:nat{length1 = B.length ptr1}) -> (length2:nat{length2 = B.length ptr2}) -> (mem:HS.mem{B.live mem ptr1 /\ B.live mem ptr2}) -> GTot (new_mem:HS.mem{correct_up mem ptr1 ptr2 new_mem heap addr1 addr2})

let up_mem heap ptr1 addr1 ptr2 addr2 length1 length2 mem = 
  let mem1 = write_low_mem heap length1 addr1 ptr1 0 mem in
  frame_write_low_mem heap length1 addr1 ptr1 0 mem;
  load_store_write_low_mem heap length1 addr1 ptr1 0 mem;
  live_preserved_write_low_mem heap length1 addr1 ptr1 0 mem;
  equal_domains_write_low_mem heap length1 addr1 ptr1 0 mem;
  underlying_seq_write_low_mem heap length1 addr1 ptr1 0 mem;
  modifies_write_low_mem heap length1 addr1 ptr1 0 mem;
  B.lemma_reveal_modifies_1 ptr1 mem mem1;
  let mem2 = write_low_mem heap length2 addr2 ptr2 0 mem1 in
  frame_write_low_mem heap length2 addr2 ptr2 0 mem1;
  load_store_write_low_mem heap length2 addr2 ptr2 0 mem1;
  equal_domains_write_low_mem heap length2 addr2 ptr2 0 mem1;
  underlying_seq_write_low_mem heap length2 addr2 ptr2 0 mem1;
  modifies_write_low_mem heap length2 addr2 ptr2 0 mem1;
  B.lemma_reveal_modifies_1 ptr2 mem1 mem2;
  if (B.as_addr ptr1 <> B.as_addr ptr2 || B.frameOf ptr1 <> B.frameOf ptr2) then
  begin
  assert (B.sel mem1 ptr1 == B.sel mem2 ptr1);
  assert (B.sel mem ptr2 == B.sel mem1 ptr2);
  mem2
  end
  else begin
  let h0 = Map.sel mem2.HS.h (B.frameOf ptr1) in
  ref_extensionality h0 (B.as_ref ptr1) (B.as_ref ptr2);
  mem2
  end

let hs_equal (h0:HS.mem) (h1:HS.mem) = FStar.HyperStack.ST.equal_domains h0 h1 /\ HS.modifies Set.empty h0 h1

let shift_equal_seq (b:B.buffer UInt8.t) (h0 h1: HS.mem) : Lemma
  (requires (forall i. 0 <= i /\ i < B.length b ==> Seq.index (B.as_seq h0 b) i == Seq.index (B.as_seq h1 b) i))
  (ensures (forall i. B.idx b <= i /\ i < B.idx b + B.length b ==> Seq.index (B.sel h0 b) i == Seq.index (B.sel h1 b) i)) =
  let s0 = B.sel h0 b in
  let s1 = B.sel h1 b in
  assert (forall i. 0 <= i /\ i < B.length b ==> Seq.index s0 (B.idx b + i) == Seq.index s1 (B.idx b + i));
  assert (forall i. i == i - B.idx b + B.idx b);
  ()

let non_seq_as_seq_equal (b:B.buffer UInt8.t) (h0 h1: HS.mem) : Lemma 
  (requires (B.as_seq h0 b == B.as_seq h1 b /\ equal_non_seq_buf h0 h1 b))
  (ensures (Seq.equal (B.sel h0 b) (B.sel h1 b))) =
 let s0 = B.sel h0 b in
 let s1 = B.sel h1 b in
 assert (forall i. 0 <= i /\ i < B.idx b ==> Seq.index s0 i == Seq.index s1 i);
 shift_equal_seq b h0 h1;
 assert (forall i. B.idx b <= i /\ i < B.idx b + B.length b ==> Seq.index s0 i == Seq.index s1 i);
 ()

let same_seq_equal (b1:B.buffer UInt8.t) (b2:B.buffer UInt8.t{B.max_length b1 = B.max_length b2}) (h0 h1:HS.mem) : Lemma
  (requires (B.as_ref b1 == B.as_ref b2 /\ B.frameOf b1 = B.frameOf b2 /\ B.as_seq h0 b1 == B.as_seq h1 b1 /\ B.as_seq h0 b2 == B.as_seq h1 b2 /\ (forall i. 0 <= i /\ i < B.max_length b1 /\ i < B.max_length b2 ==>
      not (i >= B.idx b1 && i < B.idx b1 + B.length b1) ==>
      not (i >= B.idx b2 && i < B.idx b2 + B.length b2) ==>
      Seq.index (B.sel h0 b1) i == Seq.index (B.sel h1 b1) i /\
      Seq.index (B.sel h0 b2) i == Seq.index (B.sel h1 b2) i)))
  (ensures (Seq.equal (B.sel h0 b1) (B.sel h1 b1)) /\ Seq.equal (B.sel h0 b1) (B.sel h1 b1)) =
  let s1_0 = B.sel h0 b1 in
  let s1_1 = B.sel h1 b1 in
  let s2_0 = B.sel h0 b2 in
  let s2_1 = B.sel h1 b2 in
  assert (s1_0 == s2_0);
  shift_equal_seq b1 h0 h1;
  shift_equal_seq b2 h0 h1;
  ()
  
val down_up_identity: (mem:HS.mem) -> (ptr1:(B.buffer UInt8.t){B.live mem ptr1})  -> (ptr2:(B.buffer UInt8.t){B.live mem ptr2 /\ B.disjoint ptr1 ptr2})
  -> (length1:nat{length1 = B.length ptr1}) -> (length2:nat{length2 = B.length ptr2}) -> Lemma 
  (let heap, addr1, addr2 = down_mem mem ptr1 ptr2 in let new_mem = up_mem heap ptr1 addr1 ptr2 addr2 length1 length2 mem in
    hs_equal mem new_mem)

assume val equal_heap: (h0:Heap.heap) -> (h1:Heap.heap) -> Lemma (Heap.equal_dom h0 h1 /\ Heap.modifies Set.empty h0 h1 ==> Heap.equal h0 h1)

let down_up_identity mem ptr1 ptr2 length1 length2 =
  let heap, addr1, addr2 = down_mem mem ptr1 ptr2 in let new_mem = up_mem heap ptr1 addr1 ptr2 addr2 length1 length2 mem in
  assert (FStar.HyperStack.ST.equal_domains mem new_mem);
  assume (B.modifies_1 ptr1 mem new_mem);
  B.lemma_reveal_modifies_1 ptr1 mem new_mem;
  let r = B.frameOf ptr1 in // rid
  let s = Set.singleton r in // Set of rid, containing only {r}
  let m1 = new_mem.HS.h in // hmap of Hyperstack
  let m_inter = Map.restrict (HS.mod_set s) mem.HS.h in
  let m2 = Map.concat new_mem.HS.h m_inter in
   // We only have to focus on the heap for this rid
   assert (forall r'. r' <> r ==> Map.sel m1 r' == Map.sel m2 r');
  let h0 = Map.sel m1 r in // Heap
  let h1 = Map.sel m2 r in // Heap
  let ref = B.as_ref ptr1 in
  let addrof = Heap.addr_of ref in
  equal_heap h0 h1;
  assert (Heap.equal_dom h0 h1);
  assert (HS.modifies_ref r (Set.singleton addrof) mem new_mem);
  assert (Heap.modifies (Set.singleton addrof) (Map.sel mem.HS.h r) (Map.sel new_mem.HS.h r)); // Only this address is modified in this heap
  assert (Seq.equal (B.as_seq mem ptr1) (B.as_seq new_mem ptr1));
  assert (B.as_seq mem ptr1 == B.as_seq new_mem ptr1);
  assert (Seq.equal (B.as_seq mem ptr2) (B.as_seq new_mem ptr2));
  assert (B.as_seq mem ptr2 == B.as_seq new_mem ptr2);
  if (B.as_addr ptr1 <> B.as_addr ptr2 || B.frameOf ptr1 <> B.frameOf ptr2) then begin
    non_seq_as_seq_equal ptr1 mem new_mem;
    assert (Seq.equal (B.sel mem ptr1) (B.sel new_mem ptr1))
  end
  else begin
    ref_extensionality h0 (B.as_ref ptr1) (B.as_ref ptr2);
    same_seq_equal ptr1 ptr2 mem new_mem;
    assert (Seq.equal (B.sel mem ptr1) (B.sel new_mem ptr1))
  end;
  assert (B.sel mem ptr1 == B.sel new_mem ptr1); // The complete underlying sequence (not just B.as_seq) is the same before and after
  assert (Heap.sel h1 ref == B.sel new_mem ptr1);

  // assume (h1 == Heap.upd h0 ref (B.sel new_mem ptr1));
  // assert (Heap.sel h0 ref == Heap.sel h1 ref);
  admit()

 // assert (forall (a:Type) (rel:Preorder.preorder a) (r:Heap.mref a rel). Heap.addr_of r == addrof /\ Heap.is_mm r == Heap.is_mm (B.as_ref ptr1) ==> Heap.sel h0 r == Heap.sel h1 r);
//  assume (forall (a:Type) (rel:Preorder.preorder a) (r:Heap.mref a rel). Heap.addr_of r == addrof ==> Heap.sel h0 r == Heap.sel h1 r);
(* This is sufficient to prove the property  
  
  assert (Heap.modifies Set.empty h0 h1);
  assert (Heap.equal (Map.sel m1 r) (Map.sel m2 r));
  assert (forall k. Map.sel m1 k == Map.sel m2 k);
  assert (Map.equal new_mem.HS.h (Map.concat new_mem.HS.h (Map.restrict (HS.mod_set s) mem.HS.h)));
  assert (HS.equal_on s mem.HS.h new_mem.HS.h);
  assert (FStar.HyperStack.modifies Set.empty mem new_mem) *)
  
