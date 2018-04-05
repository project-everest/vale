module Memcpy

open FStar.Buffer
open FStar.HyperStack.ST
module HS = FStar.Monotonic.HyperStack

open Vale_Sem
open Machine_int
open Interop
module B = FStar.Buffer

let bytes = buffer UInt8.t

let pre_cond (h:HS.mem) (src:bytes) (dest:bytes) =
  live h src /\ live h dest /\ disjoint src dest /\ length src == 1 /\ length dest == 1

let post_cond (h:HS.mem) (h':HS.mem) (src:bytes) (dest:bytes) =
  live h src /\ live h dest /\ live h' src /\ live h' dest /\ disjoint src dest /\ length src == 1 /\ length dest == 1

assume val memcpy: src:bytes -> dest:bytes ->
  STL unit
    (requires (fun h -> pre_cond h src dest))
    (ensures (fun h0 _ h1 -> post_cond h0 h1 src dest))

assume val src:bytes
type doeq_src = b:bytes{disjoint_or_eq src b}

assume val dst:doeq_src
assume val addrs: addr_map
type live_mem = m:HS.mem{live m src /\ live m dst}
assume val mem:live_mem

let buffers = [src; dst]
assume val addr1:nat64
assume val addr2:nat64

let memcpy_code = Mov (OMem (MConst addr2)) (OMem (MConst addr1))

let memcpy_vale (s:state) : state = eval_ins memcpy_code s

let pre_v (s:state) = pre_cond (up_mem s.mem addrs buffers mem) src dst
let post_v (s1:state) (s2:state) = post_cond (up_mem s1.mem addrs buffers mem)
  (up_mem s2.mem addrs buffers mem) src dst

let correct_memcpy (s:state) : Lemma
  (requires (pre_v s))
  (ensures (let s' = memcpy_vale s in post_v s s')) =
  assume (addrs.[(as_addr src, idx src, length src)] == addr1);
  assume (addrs.[(as_addr dst, idx dst, length dst)] == addr2);
  let s' = memcpy_vale s in
  let h0 = up_mem s.mem addrs buffers mem in
  let h1 = up_mem s'.mem addrs buffers mem in
  up_mem_liveness s.mem s'.mem addrs buffers mem;
  ()

#set-options "--z3rlimit 200"

let correct_memcpy2 (s:state) : Lemma
  (requires (pre_v s))
  (ensures True) =
  assume (addrs.[(as_addr src, idx src, length src)] == addr1);
  assume (addrs.[(as_addr dst, idx dst, length dst)] == addr2);
  let s' = memcpy_vale s in
  let h0 = up_mem s.mem addrs buffers mem in
  let h1 = up_mem s'.mem addrs buffers mem in
  let d1 = as_seq h1 dst in
  let d0 = as_seq h0 src in
  // The property we actually want to prove
  assert (Seq.equal d0 d1)

// assume val memcpy_8: src:bytes -> dest:bytes ->
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
  
