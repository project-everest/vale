module Views

open LowStar.BufferView
open Words_s
open Types_s

let nat8s_to_nat64 (v1 v2 v3 v4 v5 v6 v7 v8:nat8) : nat64 =
    v1 + 
    v2 `op_Multiply` 0x100 + 
    v3 `op_Multiply` 0x10000 +
    v4 `op_Multiply` 0x1000000 + 
    v5 `op_Multiply` 0x100000000 +
    v6 `op_Multiply` 0x10000000000 +
    v7 `op_Multiply` 0x1000000000000 +
    v8 `op_Multiply` 0x100000000000000

let get64 (s:Seq.lseq UInt8.t 8) =
  UInt64.uint_to_t (
  nat8s_to_nat64
    (UInt8.v (Seq.index s 0))
    (UInt8.v (Seq.index s 1))
    (UInt8.v (Seq.index s 2))    
    (UInt8.v (Seq.index s 3))
    (UInt8.v (Seq.index s 4))
    (UInt8.v (Seq.index s 5))
    (UInt8.v (Seq.index s 6))
    (UInt8.v (Seq.index s 7))    
  )

assume val put64 (a:UInt64.t) : GTot (Seq.lseq UInt8.t 8)
assume val inverses64 (u:unit) : Lemma (inverses get64 put64)

let view64 = inverses64 (); View 8 get64 put64
