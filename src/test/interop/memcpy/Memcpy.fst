module Memcpy

open FStar.Buffer
open FStar.HyperStack.ST
module HS = FStar.Monotonic.HyperStack

open Vale_Sem
open Machine_int
open Interop64
module B = FStar.Buffer

let buf = buffer UInt64.t

let pre_cond (h:HS.mem) (src:buf) (dest:buf) =
  live h src /\ live h dest /\ disjoint src dest /\ length src == 1 /\ length dest == 1

let post_cond (h:HS.mem) (h':HS.mem) (src:buf) (dest:buf) =
  live h src /\ live h dest /\ live h' src /\ live h' dest /\ disjoint src dest /\ length src == 1 /\ length dest == 1
    /\ Seq.equal (as_seq h src) (as_seq h' dest)

// Ideally, memcpy would have this form, but we cannot compose STATE and GHOST
assume val memcpy: src:buf -> dest:buf ->
  STL unit
    (requires (fun h -> pre_cond h src dest))
    (ensures (fun h0 _ h1 -> post_cond h0 h1 src dest))

// The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

let memcpy_code1 = Mov (OReg Rax) (OMem (MReg Rax 0))
let memcpy_code2 = Mov (OMem (MReg Rbx 0)) (OReg Rax)

#set-options "--z3rlimit 100"

let memcpy_vale (s:state{s.ok}) : (s':state{get_heap_value (eval_reg Rax s) s == get_heap_value (eval_reg Rbx s) s' /\ s'.ok}) = eval_ins memcpy_code2 (eval_ins memcpy_code1 s)

let pre_v (s:state) (src:buf) (dst:buf{disjoint src dst}) (m:HS.mem{live m src /\ live m dst}) = 
  let buffers = [src; dst] in
  pre_cond (up_mem64 s.mem addrs buffers m) src dst
  
let post_v (s1:state) (s2:state) (src:buf) (dst:buf{disjoint src dst}) (m:HS.mem{live m src /\ live m dst}) = 
  let buffers = [src; dst] in
  s2.ok /\
  post_cond (up_mem64 s1.mem addrs buffers m) (up_mem64 s2.mem addrs buffers m) src dst

#set-options "--z3rlimit 300 --initial_fuel 2 --initial_ifuel 1"

let correct_memcpy (s:state{s.ok}) (src:buf) (dst:buf{disjoint src dst}) 
  (m:HS.mem{live m src /\ live m dst}) : Lemma
  (requires (pre_v s src dst m) /\ addrs.[(as_addr src, idx src, length src)] = eval_reg Rax s /\ addrs.[(as_addr dst, idx dst, length dst)] == eval_reg Rbx s)
  (ensures (let s' = memcpy_vale s in post_v s s' src dst m)) =
  let s' = memcpy_vale s in
  let (buffers: list (buffer UInt64.t){list_live m buffers /\ list_disjoint_or_eq buffers}) = [src; dst] in
  up_mem_liveness64 s.mem s'.mem addrs buffers m;
  ()

// Memcpy at the low* level. Should ideally use type ST/STL
let low_memcpy (src:buf) (dst:buf) (h0:HS.mem{pre_cond h0 src dst}) : GTot (h1:HS.mem{post_cond h0 h1 src dst}) =
  let buffers = [src; dst] in
  let s0_heap = down_mem64 h0 addrs buffers in
  let addr1 = addrs.[(as_addr src, idx src, length src)] in
  let addr2 = addrs.[(as_addr dst, idx dst, length dst)] in
  // Not following calling conventions, but good for reduced semantics used here
  let regs = fun x -> if x = Rax then addr1 else addr2 in
  let s0 = {ok = true; regs = regs; mem = s0_heap} in
  down_up_identity64 h0 addrs buffers;
// down_up gives us the following assertion
//  assert (pre_v s0 src dst h0);
  let s1 = memcpy_vale s0 in
  correct_memcpy s0 src dst h0;
// correct_memcpy gives us the following assertion
//  assert (post_v s0 s1 src dst h0);
  let h1 = up_mem64 s1.mem addrs buffers h0 in
// The definition of post_v gives us directly the postcondition
  h1


// assume val memcpy_8: src:buf -> dest:buf ->
//   STL unit 
//   (requires (fun h -> live #UInt8.t h src /\ live #UInt8.t h dest /\ disjoint src dest 
//     /\ length #UInt8.t src == 1 /\ length #UInt8.t dest == 1))
//   (ensures  (fun h0 _ h1 -> live #UInt8.t h0 src /\ live #UInt8.t h0 dest /\ live #UInt8.t h1 dest /\ modifies_1 dest h0 h1
//     /\ length #UInt8.t src == 1 
//     /\ length #UInt8.t dest == 1
//     /\ (let d1 = as_seq #UInt8.t h1 dest in let d0 = as_seq #UInt8.t h0 dest in let s0 = as_seq #UInt8.t h0 src in
//   Seq.slice d1 0 1 ==
// 	    Seq.slice s0 0 1
// 	) ))
  
