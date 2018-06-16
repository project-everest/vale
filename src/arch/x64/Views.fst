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

let get8 (s:Seq.lseq UInt8.t 1) = Seq.index s 0
let put8 (x:UInt8.t) : GTot (Seq.lseq UInt8.t 1) =
  let contents (i:nat{i<1}) = x in
  Seq.init 1 contents

let inverses8 (u:unit) : Lemma (inverses get8 put8) =
  let aux (x:Seq.lseq UInt8.t 1) : Lemma (put8 (get8 x) == x) =
    assert (Seq.equal x (put8 (get8 x)))
  in Classical.forall_intro aux

let view8 = inverses8 (); View 1 get8 put8

let get16 (s:Seq.lseq UInt8.t 2) = UInt16.uint_to_t (
  UInt8.v (Seq.index s 0) + 
  UInt8.v (Seq.index s 1) `op_Multiply` 0x100
  )
let put16 (x:UInt16.t) : GTot (Seq.lseq UInt8.t 2) =
  let s = Seq.create 2 (UInt8.uint_to_t 0) in
  let x = UInt16.v x in
  let s = Seq.upd s 0 (UInt8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 1 (UInt8.uint_to_t (x % 0x100)) in
  s

let inverses16 (u:unit) : Lemma (inverses get16 put16) =
  let aux (x:Seq.lseq UInt8.t 2) : Lemma (put16 (get16 x) == x) =
    assert (Seq.equal x (put16 (get16 x)))
  in Classical.forall_intro aux

let view16 = inverses16 (); View 2 get16 put16

let get32 (s:Seq.lseq UInt8.t 4) = UInt32.uint_to_t (
  UInt8.v (Seq.index s 0) + 
  UInt8.v (Seq.index s 1) `op_Multiply` 0x100 +
  UInt8.v (Seq.index s 2) `op_Multiply` 0x10000 +
  UInt8.v (Seq.index s 3) `op_Multiply` 0x1000000  
  )
let put32 (x:UInt32.t) : GTot (Seq.lseq UInt8.t 4) =
  let s = Seq.create 4 (UInt8.uint_to_t 0) in
  let x = UInt32.v x in
  let s = Seq.upd s 0 (UInt8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 1 (UInt8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 2 (UInt8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 3 (UInt8.uint_to_t (x % 0x100)) in
  s

#set-options "--z3rlimit 20"

let inverses32 (u:unit) : Lemma (inverses get32 put32) =
  let aux (x:Seq.lseq UInt8.t 4) : Lemma (put32 (get32 x) == x) =
    assert (Seq.equal x (put32 (get32 x)))
  in Classical.forall_intro aux

let view32 = inverses32(); View 4 get32 put32

assume val view128: (v:view UInt8.t quad32{View?.n v == 16})
