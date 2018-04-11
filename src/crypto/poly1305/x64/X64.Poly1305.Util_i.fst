module X64.Poly1305.Util_i

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
open Calc
open X64.Vale.State_i   // needed for mem
open X64.Poly1305.Bitvectors_i

(*
open FStar.Mul
open FStar.UInt
open Semantics
lemma_BitwiseAdd64()
lemma_BitwiseMul64()
*)


// private unfold let op_Star = op_Multiply

//#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --eager_inference --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native"

(* Getting a weird error otherwise, will file an issue 
   when this gets merged in fstar branch *)
let poly1305_heap_blocks h pad r s k =
  if 0 <= k && k <= Seq.length s && k % 2 = 0 then
    poly1305_heap_blocks' h pad r s k
  else
    0

let reveal_poly1305_heap_blocks (h:int) (pad:int) (r:int) (s) (k) =
  ()            

// let rec lemma_poly1305_heap_hash_blocks' (h:int) (pad:int) (r:int) (m:mem) (i:int) (len:nat)
//   (k:int{i <= k /\ (k - i) % 16 == 0 /\ k <= i + len /\
//     (forall j . {:pattern (m `Map.contains` j)} i <= j /\ j < i + (len + 15) / 16 * 16 && (j - i) % 8 = 0 ==> m `Map.contains` j)}) :
//   Lemma (requires True)
// 	(ensures (poly1305_heap_blocks h pad r m i k == poly1305_hash_blocks h pad r (heapletTo128 m i len) i k))
//   (decreases (k-i)) =
//     let heapb = poly1305_heap_blocks h pad r m i k in
//     let hashb = poly1305_hash_blocks h pad r (heapletTo128 m i len) i k in
//     if i = k then
//       assert(heapb == hashb)
//     else
//       let kk = k - 16 in
//       assert (i >= 0 ==> precedes (kk - i) (k-i));
//       assert (i < 0 ==> precedes (kk - i) (k-i));
//       lemma_poly1305_heap_hash_blocks' h pad r m i len kk


let lemma_poly1305_heap_hash_blocks (h:int) (pad:int) (r:int) (m:mem) (b) (len) (k)  =
  admit()
  // decreases k - i

