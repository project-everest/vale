module Memcpy

open FStar.Buffer
open FStar.HyperStack.ST
module HS = FStar.Monotonic.HyperStack

open Interop64
open X64.Semantics_s
module S = X64.Bytes_Semantics_s
open X64.Machine_s
open X64.Memory_i_s
open Words_s
open Types_s
module B = FStar.Buffer

let buf = B.buffer UInt64.t

let pre_cond (h:HS.mem) (src:buf) (dest:buf) =
  live h src /\ live h dest /\ disjoint src dest /\ length src == 1 /\ length dest == 1

let post_cond (h:HS.mem) (h':HS.mem) (src:buf) (dest:buf) =
  live h src /\ live h dest /\ live h' src /\ live h' dest /\ disjoint src dest /\ 
  length src == 1 /\ length dest == 1
    /\ Seq.equal (as_seq h' src) (as_seq h' dest)

// Ideally, memcpy would have this form, but we cannot compose STATE and GHOST
assume val memcpy: src:buf -> dest:buf ->
  STL unit
    (requires (fun h -> pre_cond h src dest))
    (ensures (fun h0 _ h1 -> post_cond h0 h1 src dest))

// The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

let memcpy_code1 = Ins (S.Mov64 (OReg Rax) (OMem (MReg Rax 0)))
let memcpy_code2 = Ins (S.Mov64 (OMem (MReg Rbx 0)) (OReg Rax))

let pre_vale s (src:buffer64) (dst:buffer64) = 
  buffer_readable s.mem src /\
  buffer_readable s.mem dst /\
  buffer_length src == 1 /\
  buffer_length dst == 1 /\
  eval_reg Rax s == buffer_addr src s.mem /\
  eval_reg Rbx s == buffer_addr dst s.mem /\
  s.state.S.ok

let post_vale s s' (src:buffer64) (dst:buffer64) =
  buffer_readable s.mem src /\
  buffer_readable s.mem dst /\
  buffer_readable s'.mem src /\
  buffer_readable s'.mem dst /\
  buffer_length src == 1 /\
  buffer_length dst == 1 /\
  buffer_read src 0 s'.mem == buffer_read dst 0 s'.mem /\
  s'.state.S.ok

assume val memcpy_vale (src:buffer64) (dst:buffer64) (s:state{pre_vale s src dst}) : GTot (s':state{post_vale s s' src dst})

let pre_v (s:state) (src:buf) (dst:buf{disjoint src dst}) = 
  let buffers = [src; dst] in
  pre_cond s.mem.hs src dst
 
let post_v (s1:state) (s2:state) (src:buf) (dst:buf{disjoint src dst}) = 
  let buffers = [src; dst] in
  s2.state.S.ok /\
  post_cond s1.mem.hs s2.mem.hs src dst

#set-options "--z3rlimit 40 --initial_fuel 2 --initial_ifuel 2"

let correct_memcpy (s:state{s.state.S.ok}) 
  (src:buf{buffer_readable #(TBase TUInt64) s.mem src}) 
  (dst:buf{disjoint src dst /\ buffer_readable #(TBase TUInt64) s.mem dst}) : Lemma
  (requires (pre_v s src dst) /\ 
  buffer_addr #(TBase TUInt64) src s.mem = eval_reg Rax s /\ 
  buffer_addr #(TBase TUInt64) dst s.mem == eval_reg Rbx s)
  (ensures (let s' = memcpy_vale src dst s in post_v s s' src dst)) =
  ()

#set-options "--initial_fuel 4"

// Memcpy at the low* level. Should ideally use type ST/STL
let low_memcpy (src:buf) (dst:buf) (h0:HS.mem{pre_cond h0 src dst}) : GTot (h1:HS.mem{post_cond h0 h1 src dst}) =
  let buffers = [src; dst] in
  let s0_heap = down_mem64 h0 addrs buffers in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in 
  let addr1 = addrs.[(as_addr src, idx src, length src)] in
  let addr2 = addrs.[(as_addr dst, idx dst, length dst)] in  
  // Not following calling conventions, but good for reduced semantics used here
  let regs = fun x -> if x = Rax then addr1 else addr2 in
  let n:nat32 = 0 in
  let xmms = fun x -> Mkfour n n n n in
  let bytes_s0 = {S.ok = true; S.regs = regs; S.xmms = xmms; S.flags = 0; S.mem = s0_heap} in
  let s0 = {state = bytes_s0; mem = mem} in

//  down_up_identity64 h0 addrs buffers;
// down_up gives us the following assertion
//  assert (pre_v s0 src dst);
  let s1 = memcpy_vale src dst s0 in
//  correct_memcpy s0 src dst;
// correct_memcpy gives us the following assertion
//  assert (post_v s0 s1 src dst h0);
//  let h1 = up_mem64 s1.mem addrs buffers h0 in
  s1.mem.hs
//  admit()
// The definition of post_v gives us directly the postcondition
//  h1


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
  
