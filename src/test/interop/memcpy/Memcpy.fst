module Memcpy

open FStar.Buffer
open FStar.HyperStack.ST

let bytes = buffer UInt8.t

assume val memcpy_8: src:bytes -> dest:bytes ->
  STL unit 
  (requires (fun h -> live #UInt8.t h src /\ live #UInt8.t h dest /\ disjoint src dest 
    /\ length #UInt8.t src == 1 /\ length #UInt8.t dest == 1))
  (ensures  (fun h0 _ h1 -> live #UInt8.t h0 src /\ live #UInt8.t h0 dest /\ live #UInt8.t h1 dest /\ modifies_1 dest h0 h1
    /\ length #UInt8.t src == 1 
    /\ length #UInt8.t dest == 1
    /\ (let d1 = as_seq #UInt8.t h1 dest in let d0 = as_seq #UInt8.t h0 dest in let s0 = as_seq #UInt8.t h0 src in
  Seq.slice d1 0 1 ==
	    Seq.slice s0 0 1
	) ))
  
