module Memcpy

open FStar.Buffer
open FStar.HyperStack.ST

let bytes = buffer UInt8.t

assume val memcpy_8: src:bytes -> dest:bytes -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live #UInt8.t h src /\ live #UInt8.t h dest /\ disjoint src dest 
    /\ length #UInt8.t src >= UInt32.v len /\ length #UInt8.t dest >= UInt32.v len))
  (ensures  (fun h0 _ h1 -> live #UInt8.t h0 src /\ live #UInt8.t h0 dest /\ live #UInt8.t h1 dest /\ modifies_1 dest h0 h1
    /\ length #UInt8.t src >= UInt32.v len 
    /\ length #UInt8.t dest >= UInt32.v len
    /\ (let d1 = as_seq #UInt8.t h1 dest in let d0 = as_seq #UInt8.t h0 dest in let s0 = as_seq #UInt8.t h0 src in
  Seq.slice d1 0 (UInt32.v len) ==
	    Seq.slice s0 0 (UInt32.v len)
	/\ Seq.slice d1 (UInt32.v len) (length #UInt8.t dest) ==
	    Seq.slice d0 (UInt32.v len) (length #UInt8.t dest)) ))
  
