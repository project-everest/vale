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

#set-options "--z3rlimit 60"

let rec write_vale_mem64 (contents:Seq.seq UInt64.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:Vale_Sem.heap{forall j. {:pattern (Seq.index contents j)} 
	0 <= j /\ j < i ==> get_heap_val (addr + (j `op_Multiply` 8)) curr_heap == UInt64.v (Seq.index contents j)}) : Tot Vale_Sem.heap (decreases %[sub length i]) =
    if i >= length then curr_heap
    else
      write_vale_mem64 contents length addr (i + 1) (update_heap (addr + (i `op_Multiply` 8)) (UInt64.v (FStar.Seq.index contents i)) curr_heap)

#set-options "--z3refresh --z3rlimit 300 --max_fuel 2 --max_ifuel 1"

let rec frame_write_vale_mem64 (contents:Seq.seq UInt64.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:Vale_Sem.heap{forall j. {:pattern (Seq.index contents j)}
	0 <= j /\ j < i ==> get_heap_val (addr + (j `op_Multiply` 8)) curr_heap == UInt64.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem64 contents length addr i curr_heap in
      forall j. j < addr \/ j >= addr + (length `op_Multiply` 8) ==> curr_heap.[j] == new_heap.[j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
      let new_heap = update_heap (addr + (i `op_Multiply` 8)) (UInt64.v (FStar.Seq.index contents i)) curr_heap in
      frame_update_heap (addr + (i `op_Multiply` 8)) (UInt64.v (FStar.Seq.index contents i)) curr_heap;
      let helper(j:nat) : Lemma(0 <= j /\ j < i + 1 ==> j < FStar.Seq.Base.length contents /\ get_heap_val (addr + (j `op_Multiply` 8)) new_heap == UInt64.v (Seq.index contents j)) =
        if 0 <= j && j < i then assert (get_heap_val (addr + (j `op_Multiply` 8)) new_heap == UInt64.v (Seq.index contents j))
	else if j = i then begin
	  correct_update_get (addr + (i `op_Multiply` 8)) (UInt64.v (FStar.Seq.index contents i)) curr_heap;
	  assert (get_heap_val (addr + (i `op_Multiply` 8)) new_heap == UInt64.v (Seq.index contents i));
	  ()
	end
	else ()
      in
      Classical.forall_intro helper;
      let (new_heap : Vale_Sem.heap{(forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i+1 ==> get_heap_val (addr + (j `op_Multiply` 8)) new_heap == UInt64.v (Seq.index contents j))}) = new_heap in
      assert (sub length (i+1) < sub length i);
      frame_write_vale_mem64 contents length addr (i+1) new_heap
      end


let rec load_store_write_vale_mem64 (contents:Seq.seq UInt64.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:Vale_Sem.heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> get_heap_val (addr + (j `op_Multiply` 8)) curr_heap == UInt64.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem64 contents length addr i curr_heap in
      forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < length ==> UInt64.v (Seq.index contents j) == get_heap_val (addr + (j `op_Multiply` 8)) new_heap))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
      let new_heap = update_heap (addr + (i `op_Multiply` 8)) (UInt64.v (FStar.Seq.index contents i)) curr_heap in
      frame_update_heap (addr + (i `op_Multiply` 8)) (UInt64.v (FStar.Seq.index contents i)) curr_heap;
      let helper(j:nat) : Lemma(0 <= j /\ j < i + 1 ==> j < FStar.Seq.Base.length contents /\ get_heap_val (addr + (j `op_Multiply` 8)) new_heap == UInt64.v (Seq.index contents j)) =
        if 0 <= j && j < i then assert (get_heap_val (addr + (j `op_Multiply` 8)) new_heap == UInt64.v (Seq.index contents j))
	else if j = i then begin
	  correct_update_get (addr + (i `op_Multiply` 8)) (UInt64.v (FStar.Seq.index contents i)) curr_heap;
	  assert (get_heap_val (addr + (i `op_Multiply` 8)) new_heap == UInt64.v (Seq.index contents i));
	  ()
	end
	else ()
      in
      Classical.forall_intro helper;
      let (new_heap : Vale_Sem.heap{(forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i+1 ==> get_heap_val (addr + (j `op_Multiply` 8)) new_heap == UInt64.v (Seq.index contents j))}) = new_heap in
      assert (sub length (i+1) < sub length i);
      load_store_write_vale_mem64 contents length addr (i+1) new_heap
      end

let correct_down_p64 mem (addrs:addr_map) heap (p:B.buffer UInt64.t) =
  let length = B.length p in
  let contents = B.as_seq mem p in
  let addr = addrs.[(B.as_addr p, B.idx p, length)] in
  (forall i. {:pattern (Seq.index contents i)} 0 <= i /\ i < length ==> get_heap_val (addr + (i `op_Multiply` 8)) heap == UInt64.v (Seq.index contents i))

#set-options "--z3rlimit 100"

let correct_down_p64_cancel mem (addrs:addr_map) heap (p:B.buffer UInt64.t) : Lemma
  (forall p'. p == p' ==>       
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_heap = write_vale_mem64 contents length addr 0 heap in
      correct_down_p64 mem addrs new_heap p')) = 
  let rec aux (p':B.buffer UInt64.t) : Lemma 
    (p == p'  ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_heap = write_vale_mem64 contents length addr 0 heap in
      correct_down_p64 mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
        let new_heap = write_vale_mem64 contents length addr 0 heap in
	load_store_write_vale_mem64 contents length addr 0 heap
  in
  Classical.forall_intro aux

let correct_down_p64_frame mem (addrs:addr_map) heap (p:B.buffer UInt64.t) : Lemma
  (forall (p':B.buffer UInt64.t). B.disjoint p p' /\ correct_down_p64 mem addrs heap p' ==>       
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_heap = write_vale_mem64 contents length addr 0 heap in
      correct_down_p64 mem addrs new_heap p')) = 
  let rec aux (p':B.buffer UInt64.t) : Lemma 
    (B.disjoint p p' /\ correct_down_p64 mem addrs heap p' ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_heap = write_vale_mem64 contents length addr 0 heap in
      correct_down_p64 mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
	let addr' = addrs.[(B.as_addr p', B.idx p', B.length p')] in
        let new_heap = write_vale_mem64 contents length addr 0 heap in
	frame_write_vale_mem64 contents length addr 0 heap;
	assert (B.disjoint p p' ==> (forall i. 0 <= i /\ i < 8 `op_Multiply` B.length p' ==> addr' + i < addr \/ addr + (8 `op_Multiply` length) < addr' + i));
	assert (B.disjoint p p' ==> (forall i. 0 <= i /\ i < 8 `op_Multiply` B.length p' ==> heap.[addr' + i] == new_heap.[addr' + i]));
	()
  in
  Classical.forall_intro aux


let correct_down64 mem (addrs:addr_map) (ptrs: list (B.buffer UInt64.t)) heap =
  forall p. List.memP p ptrs ==> correct_down_p64 mem addrs heap p

val down_mem64: (mem:HS.mem) -> (addrs:addr_map) -> (ptrs:list (B.buffer UInt64.t){list_disjoint_or_eq ptrs}) -> GTot (heap :Vale_Sem.heap {correct_down64 mem addrs ptrs heap})

#set-options "--z3rlimit 40"

let down_mem64 mem addrs ptrs =
  (* Dummy heap *)
  let heap : heap = FStar.Map.const (UInt8.uint_to_t 0) in
  let rec aux ps (accu:list (B.buffer UInt64.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
    (h:Vale_Sem.heap{correct_down64 mem addrs accu h}) : GTot (heap:Vale_Sem.heap{correct_down64 mem addrs ptrs heap}) = match ps with
    | [] -> h
    | a::q ->
      let length = B.length a in
      let contents = B.as_seq mem a in
      let addr = addrs.[(B.as_addr a, B.idx a, B.length a)] in
      let new_heap = write_vale_mem64 contents length addr 0 h in
      load_store_write_vale_mem64 contents length addr 0 h;
      correct_down_p64_cancel mem addrs h a;
      correct_down_p64_frame mem addrs h a;
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
      aux q (a::accu) new_heap
    in
    aux ptrs [] heap 

let create_seq64 heap length addr : Tot (s':Seq.seq UInt64.t{Seq.length s' = length /\ 
  (forall j. 0 <= j /\ j < length ==> UInt64.v (Seq.index s' j) == get_heap_val (addr + j `op_Multiply` 8) heap)}) =
  let rec aux heap length addr (i:nat{i <= length}) (s:Seq.seq UInt64.t{Seq.length s = i /\ 
    (forall j. 0 <= j /\ j < i ==> UInt64.v (Seq.index s j) == get_heap_val (addr + j `op_Multiply` 8) heap)}) : Tot (s':Seq.seq UInt64.t{Seq.length s' = length /\ 
    (forall j. 0 <= j /\ j < length ==> UInt64.v (Seq.index s' j) == get_heap_val (addr + j `op_Multiply` 8) heap)}) (decreases %[sub length i]) =
  if i = length then s
    else
    let s' = Seq.append s (Seq.create 1 (UInt64.uint_to_t (get_heap_val (addr + i `op_Multiply` 8) heap))) in
    aux heap length addr (i+1) s'
  in aux heap length addr 0 Seq.createEmpty

let write_low_mem64 heap length addr (buf:(B.buffer UInt64.t){length = B.length buf}) (curr_mem:HS.mem{B.live curr_mem buf}) : GTot HS.mem = 
  let s = B.sel curr_mem buf in
  let modified = create_seq64 heap length addr in
  let lo = Seq.slice s 0 (B.idx buf) in
  let hi = Seq.slice s (B.idx buf + length) (B.max_length buf) in
  let s' = Seq.append lo (Seq.append modified hi) in
  HS.upd curr_mem (B.content buf) s'

#set-options "--z3rlimit 100"

let frame_write_low_mem64 heap length addr (buf:(B.buffer UInt64.t){length = B.length buf}) (mem:HS.mem{B.live mem buf}) : Lemma
  (let new_mem = write_low_mem64 heap length addr buf mem in
    forall (b:(B.buffer UInt64.t){B.live mem b /\ B.disjoint b buf}). 
    {:pattern (B.equal mem b new_mem b)}
    B.equal mem b new_mem b) =
    let new_mem = write_low_mem64 heap length addr buf mem in
    let aux (b : B.buffer UInt64.t{B.live mem b /\ B.disjoint b buf}) : Lemma (B.equal mem b new_mem b) =
      if B.as_addr b <> B.as_addr buf || B.frameOf b <> B.frameOf buf then ()
      else begin
        let ty1 = B.lseq UInt64.t (B.max_length b) in
        let ty2 = B.lseq UInt64.t (B.max_length buf) in
        let t1 = Heap.mref ty1 (Heap.trivial_preorder _) in
        let r1 : t1  = B.as_ref b in
        let r2' : Heap.mref ty2 (Heap.trivial_preorder _) = B.as_ref buf in
        let r2 : t1 = r2' in
	ref_extensionality #ty1 #(Heap.trivial_preorder _)  (Map.sel mem.HS.h (B.frameOf b)) r1 r2 ;
	assert (Seq.equal (B.as_seq mem b) (B.as_seq new_mem b))
      end
    in Classical.forall_intro aux

let load_store_write_low_mem64 heap length addr (buf:(B.buffer UInt64.t){length = B.length buf}) (mem:HS.mem{B.live mem buf}) : Lemma
  (let new_mem = write_low_mem64 heap length addr buf mem in
    forall j. 0 <= j /\ j < length ==> UInt64.v (Seq.index (B.as_seq new_mem buf) j) == get_heap_val (addr + j `op_Multiply` 8) heap) = ()

let invariant_write_low_mem64 heap length addr (b:(B.buffer UInt64.t){length = B.length b}) (mem:HS.mem{B.live mem b}) : Lemma
  (requires (forall i. 0 <= i /\ i < B.length b ==> UInt64.v (Seq.index (B.as_seq mem b) i) == get_heap_val (addr + i `op_Multiply` 8) heap))
  (ensures (mem == write_low_mem64 heap length addr b mem)) 
  [SMTPat (mem == write_low_mem64 heap length addr b mem)]
  =
  let new_mem = write_low_mem64 heap length addr b mem in	  
  let s = B.sel mem b in
  let s' = B.sel new_mem b in
  let lo_i = Seq.slice s 0 (B.idx b) in
  let hi_i = Seq.slice s (B.idx b + length) (B.max_length b) in
  let mi_create = create_seq64 heap length addr in
  let s_app = Seq.append lo_i (Seq.append mi_create hi_i) in
  assert (Seq.equal (HS.sel mem (B.content b)) s_app);
  HS.lemma_heap_equality_upd_with_sel mem (B.content b);
  ()

let cancel_write_low_mem64 heap length addr (b:B.buffer UInt64.t{length = B.length b}) (mem:HS.mem{B.live mem b}) : Lemma
  (write_low_mem64 heap length addr b (write_low_mem64 heap length addr b mem) == write_low_mem64 heap length addr b mem) =
  let s = B.sel mem b in
  let modified = create_seq64 heap length addr in
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

logic let correct_up_p64 (addrs:addr_map) new_mem heap p =
  let length = B.length p in
  let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
  (forall i.{:pattern (get_heap_val (addr + i `op_Multiply` 8) heap); (Seq.index (B.as_seq new_mem p) i)}  0 <= i /\ i < length ==> get_heap_val (addr + i `op_Multiply` 8) heap == UInt64.v (Seq.index (B.as_seq new_mem p) i))

let correct_up64 (addrs:addr_map) ptrs new_mem heap =
  forall p. List.memP p ptrs ==> correct_up_p64 addrs new_mem heap p

let list_live mem ptrs = forall p . List.memP p ptrs ==> B.live mem p

let correct_up_p64_cancel heap (addrs:addr_map) (p:B.buffer UInt64.t) (mem:HS.mem{B.live mem p}) : Lemma
  (forall p'. p == p' ==>       
      (let length = B.length p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_mem = write_low_mem64 heap length addr p mem in
      correct_up_p64 addrs new_mem heap p')) = 
  let rec aux (p':B.buffer UInt64.t) : Lemma 
    (p == p'  ==> (let length = B.length p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_mem = write_low_mem64 heap length addr p mem in
      correct_up_p64 addrs new_mem heap p')) =
        let length = B.length p in
        let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
        let new_mem = write_low_mem64 heap length addr p mem in
	load_store_write_low_mem64 heap length addr p mem
  in
  Classical.forall_intro aux

let correct_up_p64_frame heap (addrs:addr_map) (p:B.buffer UInt64.t) (mem:HS.mem{B.live mem p}) : Lemma
  (forall (p':B.buffer UInt64.t). B.live mem p' /\ B.disjoint p p' /\ correct_up_p64 addrs mem heap p' ==>       
      (let length = B.length p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_mem = write_low_mem64 heap length addr p mem in
      correct_up_p64 addrs new_mem heap p')) = 
  let rec aux (p':B.buffer UInt64.t) : Lemma 
    (B.live mem p' /\ B.disjoint p p' /\ correct_up_p64 addrs mem heap p' ==> (let length = B.length p in
      let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
      let new_mem = write_low_mem64 heap length addr p mem in
      correct_up_p64 addrs new_mem heap p')) =
        let length = B.length p in
        let addr = addrs.[(B.as_addr p, B.idx p, B.length p)] in
        let new_mem = write_low_mem64 heap length addr p mem in
	frame_write_low_mem64 heap length addr p mem;
	assert (B.live mem p' /\ B.disjoint p p' ==> B.equal mem p' new_mem p');
	()
  in
  Classical.forall_intro aux

val up_mem64: (heap:Vale_Sem.heap) -> (addrs:addr_map) -> (ptrs: list (B.buffer UInt64.t){list_disjoint_or_eq ptrs}) -> (mem:HS.mem{list_live mem ptrs}) -> GTot (new_mem:HS.mem{correct_up64 addrs ptrs new_mem heap})

let rec up_mem64_aux (heap:Vale_Sem.heap) (addrs:addr_map) (ptrs: list (B.buffer UInt64.t){list_disjoint_or_eq ptrs}) (ps:list (B.buffer UInt64.t))
    (accu: list (B.buffer UInt64.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) 
    (m:HS.mem{list_live m ps /\ list_live m accu /\ correct_up64 addrs accu m heap}) : GTot (new_mem:HS.mem{correct_up64 addrs ptrs new_mem heap}) = 
  match ps with
    | [] -> m
    | a::q ->
      let length = B.length a in
      let addr = addrs.[(B.as_addr a, B.idx a, B.length a)] in
      let new_mem = write_low_mem64 heap length addr a m in
      load_store_write_low_mem64 heap length addr a m;
      correct_up_p64_cancel heap addrs a m;
      correct_up_p64_frame heap addrs a m;
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
      up_mem64_aux heap addrs ptrs q (a::accu) new_mem

let up_mem64 heap addrs ptrs mem =  up_mem64_aux heap addrs ptrs ptrs [] mem


let rec invariant_up_mem64_aux (heap:Vale_Sem.heap) (addrs:addr_map) (ptrs: list (B.buffer UInt64.t){list_disjoint_or_eq ptrs}) (ps:list (B.buffer UInt64.t))
    (accu: list (B.buffer UInt64.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) 
    (m:HS.mem{list_live m ps /\ list_live m accu /\ correct_up64 addrs accu m heap}) : Lemma
  (requires (forall b. List.memP b ptrs ==> (forall i. 0 <= i /\ i < B.length b ==> UInt64.v (Seq.index (B.as_seq m b) i) == get_heap_val (addrs.[(B.as_addr b, B.idx b, B.length b)] + i `op_Multiply` 8) heap)))
  (ensures (m == up_mem64_aux heap addrs ptrs ps accu m)) 
  [SMTPat (m == up_mem64_aux heap addrs ptrs ps accu m)] =
  match ps with 
    | [] -> ()
    | a::q ->  
      let length = B.length a in
      let addr = addrs.[(B.as_addr a, B.idx a, B.length a)] in
      let new_mem = write_low_mem64 heap length addr a m in
      invariant_write_low_mem64 heap length addr a m;
      invariant_up_mem64_aux heap addrs ptrs q (a::accu) new_mem

let rec liveness_up_mem64_aux (heap:Vale_Sem.heap) (addrs:addr_map) (ptrs: list (B.buffer UInt64.t){list_disjoint_or_eq ptrs}) (ps:list (B.buffer UInt64.t))
    (accu: list (B.buffer UInt64.t){forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) 
    (m:HS.mem{list_live m ps /\ list_live m accu /\ correct_up64 addrs accu m heap}) : Lemma
  (forall #a (b:B.buffer a). B.live m b <==> B.live (up_mem64_aux heap addrs ptrs ps accu m) b) =
  match ps with
    | [] -> ()
    | a::q ->
      let length = B.length a in
      let addr = addrs.[(B.as_addr a, B.idx a, B.length a)] in
      let new_mem = write_low_mem64 heap length addr a m in
      load_store_write_low_mem64 heap length addr a m;
      correct_up_p64_cancel heap addrs a m;
      correct_up_p64_frame heap addrs a m;      
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);      
      liveness_up_mem64_aux heap addrs ptrs q (a::accu) new_mem


val down_up_identity64: (mem:HS.mem) -> (addrs:addr_map) -> (ptrs:list (B.buffer UInt64.t){list_disjoint_or_eq ptrs /\ list_live mem ptrs }) -> Lemma 
  (let heap = down_mem64 mem addrs ptrs in 
   let new_mem = up_mem64 heap addrs ptrs mem in
    mem == new_mem)

#set-options "--z3rlimit 200"

let down_up_identity64 mem addrs ptrs =
  let heap = down_mem64 mem addrs ptrs in 
  let new_mem = up_mem64 heap addrs ptrs mem in
  assert (forall (p:B.buffer UInt64.t{List.memP p ptrs}). correct_up_p64 addrs mem heap p);
  assert (forall (p:B.buffer UInt64.t{List.memP p ptrs}). correct_up_p64 addrs new_mem heap p);
  invariant_up_mem64_aux heap addrs ptrs ptrs [] mem;
  ()

val up_mem_liveness64: (heap:Vale_Sem.heap) -> (heap':Vale_Sem.heap) -> (addrs:addr_map) -> (ptrs: list (B.buffer UInt64.t){list_disjoint_or_eq ptrs}) -> (mem:HS.mem{list_live mem ptrs}) -> Lemma
  (let mem1 = up_mem64 heap addrs ptrs mem in
   let mem2 = up_mem64 heap' addrs ptrs mem in
   forall (b:B.buffer UInt64.t). B.live mem1 b ==> B.live mem2 b)

let up_mem_liveness64 heap heap' addrs ptrs mem = 
  liveness_up_mem64_aux heap addrs ptrs ptrs [] mem;
  liveness_up_mem64_aux heap' addrs ptrs ptrs [] mem
