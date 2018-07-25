module Views

open LowStar.BufferView
open Words_s
open Words.Four_s
open Words.Seq_s
open Words.Seq_i
open Types_s
open Types_i
open Opaque_s

let seq_nat8_to_seq_U8 (b:Seq.seq nat8) : (Seq.seq UInt8.t) =
  Seq.init (Seq.length b) (fun (i:nat { i < Seq.length b }) -> UInt8.uint_to_t (Seq.index b i))

let seq_U8_to_seq_nat8 (b:Seq.seq UInt8.t) : (s:Seq.seq nat8 { Seq.length s == Seq.length b} ) =
  Seq.init (Seq.length b) (fun (i:nat { i < Seq.length b }) -> let n:nat8 = UInt8.v (Seq.index b i) in n)

let seq_nat8_to_seq_U8_to_seq_nat8 (b:Seq.seq nat8) : 
  Lemma (seq_U8_to_seq_nat8 (seq_nat8_to_seq_U8 b) == b)
  [SMTPat (seq_U8_to_seq_nat8 (seq_nat8_to_seq_U8 b))]
  =
  assert (FStar.Seq.equal (seq_U8_to_seq_nat8 (seq_nat8_to_seq_U8 b)) b);
  ()

let seq_U8_to_seq_nat8_to_seq_U8 (b:Seq.seq UInt8.t) : 
  Lemma (seq_nat8_to_seq_U8 (seq_U8_to_seq_nat8 b) == b)
  [SMTPat (seq_nat8_to_seq_U8 (seq_U8_to_seq_nat8 b))]
  =
  assert (FStar.Seq.equal (seq_nat8_to_seq_U8 (seq_U8_to_seq_nat8 b)) b);
  ()

let get8_def (s:Seq.lseq UInt8.t 1) = Seq.index s 0
let put8_def (x:UInt8.t) : GTot (Seq.lseq UInt8.t 1) =
  let contents (i:nat{i<1}) = x in
  Seq.init 1 contents

let get8 = make_opaque get8_def
let put8 = make_opaque put8_def

let inverses8 (u:unit) : Lemma (inverses get8 put8) =
  reveal_opaque get8_def;
  reveal_opaque put8_def;
  let aux (x:Seq.lseq U8.t 1) : Lemma (put8 (get8 x) == x) =
    assert (Seq.equal x (put8 (get8 x)))
  in Classical.forall_intro aux

let view8 = inverses8 (); View 1 get8 put8

let get16_def (s:Seq.lseq U8.t 2) = UInt16.uint_to_t (
  U8.v (Seq.index s 0) + 
  U8.v (Seq.index s 1) `op_Multiply` 0x100
  )
let put16_def (x:UInt16.t) : GTot (Seq.lseq U8.t 2) =
  let s = Seq.create 2 (U8.uint_to_t 0) in
  let x = UInt16.v x in
  let s = Seq.upd s 0 (U8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 1 (U8.uint_to_t (x % 0x100)) in
  s

let get16 = make_opaque get16_def
let put16 = make_opaque put16_def

let inverses16 (u:unit) : Lemma (inverses get16 put16) =
  reveal_opaque get16_def;
  reveal_opaque put16_def;
  let aux (x:Seq.lseq U8.t 2) : Lemma (put16 (get16 x) == x) =
    assert (Seq.equal x (put16 (get16 x)))
  in Classical.forall_intro aux

let view16 = inverses16 (); View 2 get16 put16

let get32_def (s:Seq.lseq UInt8.t 4) = UInt32.uint_to_t (
  four_to_nat 8 
    (Mkfour 
      (UInt8.v (Seq.index s 0))
      (UInt8.v (Seq.index s 1))
      (UInt8.v (Seq.index s 2))
      (UInt8.v (Seq.index s 3))))

let put32_def (x:UInt32.t) : GTot (Seq.lseq UInt8.t 4) =
  seq_nat8_to_seq_U8 (four_to_seq_LE (nat_to_four 8 (UInt32.v x)))

let get32 = make_opaque get32_def
let put32 = make_opaque put32_def

#set-options "--z3rlimit 20"

let inverses32 (u:unit) : Lemma (inverses get32 put32) =
  reveal_opaque get32_def;
  reveal_opaque put32_def;
  let aux (x:Seq.lseq U8.t 4) : Lemma (put32 (get32 x) == x) =
    assert (Seq.equal x (put32 (get32 x)))
  in Classical.forall_intro aux

let view32 = inverses32(); View 4 get32 put32

// TODO: Convert the 64-bit operations below to use the Types and Words definitions, like the 32-bit and 128-bit do
let nat8s_to_nat64 (v1 v2 v3 v4 v5 v6 v7 v8:nat8) : nat64 =
    v1 + 
    v2 `op_Multiply` 0x100 + 
    v3 `op_Multiply` 0x10000 +
    v4 `op_Multiply` 0x1000000 + 
    v5 `op_Multiply` 0x100000000 +
    v6 `op_Multiply` 0x10000000000 +
    v7 `op_Multiply` 0x1000000000000 +
    v8 `op_Multiply` 0x100000000000000

let get64_def (s:Seq.lseq U8.t 8) =
  UInt64.uint_to_t (
  nat8s_to_nat64
    (U8.v (Seq.index s 0))
    (U8.v (Seq.index s 1))
    (U8.v (Seq.index s 2))    
    (U8.v (Seq.index s 3))
    (U8.v (Seq.index s 4))
    (U8.v (Seq.index s 5))
    (U8.v (Seq.index s 6))
    (U8.v (Seq.index s 7))    
  )

private
abstract
let get64_def_alt (s:Seq.lseq U8.t 8) : GTot UInt64.t =
  let open FStar.Mul in
  let s0 = Seq.slice s 0 4 in
  let u0 = get32_def s0 in
  let s1 = Seq.slice s 4 8 in
  let u1 = get32_def s1 in
  UInt64.uint_to_t (UInt32.v u0 +
                    UInt32.v u1 * 0x100000000)

private
let get64_def_alt_equiv (s:Seq.lseq U8.t 8)
  : Lemma (get64_def s == get64_def_alt s)
  = ()

let put64_def (a:UInt64.t) : GTot (Seq.lseq U8.t 8) =
  let u0 = UInt32.uint_to_t (UInt64.v a % 0x100000000) in
  let u1 = UInt32.uint_to_t ((UInt64.v a / 0x100000000) % 0x100000000) in
  let s0 = put32_def u0 in
  let s1 = put32_def u1 in
  Seq.append s0 s1

private
let inverses64_def_aux (x:UInt64.t)
  : Lemma (get64_def (put64_def x) == x)
  = ()

private
let inverses64_def_aux' (x:Seq.lseq U8.t 8)
  : Lemma (put64_def (get64_def x) `Seq.equal` x)
  = reveal_opaque get32_def;
    reveal_opaque put32_def;
    inverses32();
    get64_def_alt_equiv x;
    get64_def_alt_equiv (put64_def (get64_def x));
    inverses64_def_aux (get64_def x)

let get64 = make_opaque get64_def
let put64 = make_opaque put64_def

let inverses64 (u:unit) : Lemma (inverses get64 put64) =
  reveal_opaque get64_def;
  reveal_opaque put64_def;
  Classical.forall_intro inverses64_def_aux;
  Classical.forall_intro inverses64_def_aux'

let view64 = inverses64 (); View 8 get64 put64

let nat8s_to_nat32 (v1 v2 v3 v4:nat8) : nat32 =
    v1 + 
    v2 `op_Multiply` 0x100 + 
    v3 `op_Multiply` 0x10000 +
    v4 `op_Multiply` 0x1000000 

let get128_def (s:Seq.lseq UInt8.t 16) =
  le_bytes_to_quad32 (seq_U8_to_seq_nat8 s)
  
let put128_def (a:quad32) : GTot (Seq.lseq UInt8.t 16) =
  seq_nat8_to_seq_U8 (le_quad32_to_bytes a)

let get128 = make_opaque get128_def
let put128 = make_opaque put128_def

let inverses128 (u:unit) : Lemma (inverses get128 put128) =
  reveal_opaque get128_def;
  reveal_opaque put128_def;
  Classical.forall_intro le_quad32_to_bytes_to_quad32;
  Classical.forall_intro le_bytes_to_quad32_to_bytes;
  ()

let view128 = inverses128 (); View 16 get128 put128

