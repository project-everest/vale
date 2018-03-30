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

let disjoint_or_eq ptr1 ptr2 = B.disjoint ptr1 ptr2 \/ ptr1 == ptr2

let list_disjoint_or_eq (#a:Type0) (ptrs:list (B.buffer a)) =
  forall p1 p2. List.memP p1 ptrs /\ List.memP p2 ptrs ==> disjoint_or_eq p1 p2

(* Abstract maps linking buffers to addresses in the Vale heap. A buffer is uniquely identified by its address, idx and length. TODO : Add Type? *)
type buffer_triple = nat * nat * nat
let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 || addr2 + length2 < addr1

type addr_map = (m:(Map.t buffer_triple nat64){forall (buf1 buf2:B.buffer UInt8.t). B.disjoint buf1 buf2 ==> disjoint_addr (m.[(B.as_addr buf1, B.idx buf1, B.length buf1)]) (B.length buf1)
  (m.[(B.as_addr buf2, B.idx buf2, B.length buf2)]) (B.length buf2)})

(* Additional hypotheses, which should be added to the corresponding libraries at some point *)

(* If two refs have the same address, and are in the heap, they are equal *)
assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma 
  (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

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

let correct_down_p mem (addrs:addr_map) heap p =
  let length = B.length p in
  let contents = B.as_seq mem p in
  let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
  (forall i.  0 <= i /\ i < length ==> heap.[addr + i] == FStar.Seq.index contents i)

#set-options "--z3rlimit 40"

let correct_down_p_cancel mem (addrs:addr_map) heap (p:B.buffer UInt8.t) : Lemma
  (forall p'. p == p' ==>       
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) = 
  let rec aux (p':B.buffer UInt8.t) : Lemma 
    (p == p'  ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
        let new_heap = write_vale_mem contents length addr 0 heap in
	load_store_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux
      
let correct_down_p_frame mem (addrs:addr_map) heap (p:B.buffer UInt8.t) : Lemma
  (forall p'. B.disjoint p p' /\ correct_down_p mem addrs heap p' ==>       
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) = 
  let rec aux (p':B.buffer UInt8.t) : Lemma 
    (B.disjoint p p' /\ correct_down_p mem addrs heap p' ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
        let new_heap = write_vale_mem contents length addr 0 heap in
	frame_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux

let correct_down (#a:Type0) mem (addrs:addr_map) (ptrs: list (B.buffer a)) heap =
  forall p. List.memP p ptrs ==> correct_down_p mem addrs heap p

(* Takes a Low* Hyperstack and two buffers (for the moment) and create a vale memory + keep track of the vale addresses *)
val down_mem: (mem:HS.mem) -> (addrs: addr_map) -> (ptrs:list (B.buffer UInt8.t){list_disjoint_or_eq ptrs}) -> GTot (heap :Vale_Sem.heap {correct_down mem addrs ptrs heap})

let down_mem mem addrs ptrs =
  (* Dummy heap *)
  let heap : heap = FStar.Map.const (UInt8.uint_to_t 0) in
  let rec aux ps (accu:list (B.buffer UInt8.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
    (h:Vale_Sem.heap{correct_down mem addrs accu h}) : GTot (heap:Vale_Sem.heap{correct_down mem addrs ptrs heap}) = match ps with
    | [] -> h
    | a::q ->
      let length = B.length a in
      let contents = B.as_seq mem a in
      let addr = addrs.[(B.as_addr a, B.idx a, B.length a)] in
      let new_heap = write_vale_mem contents length addr 0 h in
      load_store_write_vale_mem contents length addr 0 h;
      correct_down_p_cancel mem addrs h a;
      correct_down_p_frame mem addrs h a;
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
      aux q (a::accu) new_heap
    in
    aux ptrs [] heap

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

let write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (curr_mem:HS.mem{B.live curr_mem buf}) : GTot HS.mem = 
  let s = B.sel curr_mem buf in
  let modified = create_seq heap length addr in
  let lo = Seq.slice s 0 (B.idx buf) in
  let hi = Seq.slice s (B.idx buf + length) (B.max_length buf) in
  let s' = Seq.append lo (Seq.append modified hi) in
  HS.upd curr_mem (B.content buf) s'

let frame_write_low_mem heap length addr (buf:(B.buffer UInt8.t){length = B.length buf}) (mem:HS.mem{B.live mem buf}) : Lemma
  (let new_mem = write_low_mem heap length addr buf mem in
    forall (b:(B.buffer UInt8.t){B.live mem b /\ B.disjoint b buf}). 
    {:pattern (B.equal mem b new_mem b)}
    B.equal mem b new_mem b) =
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

let invariant_write_low_mem heap length addr (b:(B.buffer UInt8.t){length = B.length b}) (mem:HS.mem{B.live mem b}) : Lemma
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
  HS.lemma_heap_equality_upd_with_sel mem (B.content b);
  ()

let cancel_write_low_mem heap length addr (b:B.buffer UInt8.t{length = B.length b}) (mem:HS.mem{B.live mem b}) : Lemma
  (write_low_mem heap length addr b (write_low_mem heap length addr b mem) == write_low_mem heap length addr b mem) =
  let s = B.sel mem b in
  let modified = create_seq heap length addr in
  let lo = Seq.slice s 0 (B.idx b) in
  let hi = Seq.slice s (B.idx b + length) (B.max_length b) in
  let s' = Seq.append lo (Seq.append modified hi) in
  let mem1 = HS.upd mem (B.content b) s' in
  let s1 = B.sel mem1 b in
  let lo1 = Seq.slice s1 0 (B.idx b) in
  let hi1 = Seq.slice s1 (B.idx b + length) (B.max_length b) in
  assert (Seq.equal lo lo1);
  assert (Seq.equal hi hi1);
  HS.lemma_heap_equality_cancel_same_mref_upd mem (B.content b) s' s';
  ()

logic let correct_up_p (addrs:addr_map) new_mem heap p =
  let length = B.length p in
  let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
  (forall i.  0 <= i /\ i < length ==> heap.[addr + i] == Seq.index (B.as_seq new_mem p) i)

let correct_up (addrs:addr_map) ptrs new_mem heap =
  forall p. List.memP p ptrs ==> correct_up_p addrs new_mem heap p

let list_live mem ptrs = forall p. List.memP p ptrs ==> B.live mem p


let correct_up_p_cancel heap (addrs:addr_map) (p:B.buffer UInt8.t) (mem:HS.mem{B.live mem p}) : Lemma
  (forall p'. p == p' ==>       
      (let length = B.length p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_mem = write_low_mem heap length addr p mem in
      correct_up_p addrs new_mem heap p')) = 
  let rec aux (p':B.buffer UInt8.t) : Lemma 
    (p == p'  ==> (let length = B.length p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_mem = write_low_mem heap length addr p mem in
      correct_up_p addrs new_mem heap p')) =
        let length = B.length p in
        let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
        let new_mem = write_low_mem heap length addr p mem in
	load_store_write_low_mem heap length addr p mem
  in
  Classical.forall_intro aux

let correct_up_p_frame heap (addrs:addr_map) (p:B.buffer UInt8.t) (mem:HS.mem{B.live mem p}) : Lemma
  (forall (p':B.buffer UInt8.t). B.live mem p' /\ B.disjoint p p' /\ correct_up_p addrs mem heap p' ==>       
      (let length = B.length p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_mem = write_low_mem heap length addr p mem in
      correct_up_p addrs new_mem heap p')) = 
  let rec aux (p':B.buffer UInt8.t) : Lemma 
    (B.live mem p' /\ B.disjoint p p' /\ correct_up_p addrs mem heap p' ==> (let length = B.length p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_mem = write_low_mem heap length addr p mem in
      correct_up_p addrs new_mem heap p')) =
        let length = B.length p in
        let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
        let new_mem = write_low_mem heap length addr p mem in
	frame_write_low_mem heap length addr p mem;
	assert (B.live mem p' /\ B.disjoint p p' ==> B.equal mem p' new_mem p');
	()
  in
  Classical.forall_intro aux

val up_mem: (heap:Vale_Sem.heap) -> (addrs:addr_map) -> (ptrs: list (B.buffer UInt8.t){list_disjoint_or_eq ptrs}) -> (mem:HS.mem{list_live mem ptrs}) -> GTot (new_mem:HS.mem{correct_up addrs ptrs new_mem heap})

#set-options "--z3rlimit 100 --z3refresh"

let rec up_mem_aux (heap:Vale_Sem.heap) (addrs:addr_map) (ptrs: list (B.buffer UInt8.t){list_disjoint_or_eq ptrs}) (ps:list (B.buffer UInt8.t))
    (accu: list (B.buffer UInt8.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) 
    (m:HS.mem{list_live m ps /\ list_live m accu /\ correct_up addrs accu m heap}) : GTot (new_mem:HS.mem{correct_up addrs ptrs new_mem heap}) = 
  match ps with
    | [] -> m
    | a::q ->
      let length = B.length a in
      let addr = addrs.[(B.as_addr a, B.idx a, B.length a)] in
      let new_mem = write_low_mem heap length addr a m in
      load_store_write_low_mem heap length addr a m;
      correct_up_p_cancel heap addrs a m;
      correct_up_p_frame heap addrs a m;
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
      up_mem_aux heap addrs ptrs q (a::accu) new_mem

let up_mem heap addrs ptrs mem =  up_mem_aux heap addrs ptrs ptrs [] mem

let rec invariant_up_mem_aux (heap:Vale_Sem.heap) (addrs:addr_map) (ptrs: list (B.buffer UInt8.t){list_disjoint_or_eq ptrs}) (ps:list (B.buffer UInt8.t))
    (accu: list (B.buffer UInt8.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) 
    (m:HS.mem{list_live m ps /\ list_live m accu /\ correct_up addrs accu m heap}) : Lemma
  (requires (forall b. List.memP b ptrs ==> (forall i. 0 <= i /\ i < B.length b ==> Seq.index (B.as_seq m b) i == heap.[addrs.[(B.as_addr b, B.idx b, B.length b)] + i])))
  (ensures (m == up_mem_aux heap addrs ptrs ps accu m)) 
  [SMTPat (m == up_mem_aux heap addrs ptrs ps accu m)] =
  match ps with 
    | [] -> ()
    | a::q ->  
      let length = B.length a in
      let addr = addrs.[(B.as_addr a, B.idx a, B.length a)] in
      let new_mem = write_low_mem heap length addr a m in
      invariant_write_low_mem heap length addr a m;
      invariant_up_mem_aux heap addrs ptrs q (a::accu) new_mem

val down_up_identity: (mem:HS.mem) -> (addrs:addr_map) -> (ptrs:list (B.buffer UInt8.t){list_disjoint_or_eq ptrs /\ list_live mem ptrs }) -> Lemma 
  (let heap = down_mem mem addrs ptrs in 
   let new_mem = up_mem heap addrs ptrs mem in
    mem == new_mem)

let down_up_identity mem addrs ptrs =
  let heap = down_mem mem addrs ptrs in 
  let new_mem = up_mem heap addrs ptrs mem in
  assert (forall (p:B.buffer UInt8.t{List.memP p ptrs}). correct_up_p addrs mem heap p);
  invariant_up_mem_aux heap addrs ptrs ptrs [] mem;
  ()
