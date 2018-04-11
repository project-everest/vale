module TestBV

open Bv64
open FStar.Tactics
open TacticsBV
open Machine
open Decls


let test1 (x y: nat64) =
assert_by_tactic (bv_tac ()) (logand64 x y == logand64 y x)
let test2 (x y : nat64) = 
  assert_by_tactic (bv_tac ()) (logand64 (logand64 x y) y == logand64 y (logand64 y x))
let test3 (x y : nat64) = 
  assert_by_tactic (bv_tac ()) 
  (logand64 (logand64 (logand64 x y) x) y == logand64 y (logand64 x (logand64 y x)))
let test4 (x y : nat64) = 
  assert_by_tactic (bv_tac ()) 
  (logand64 (logand64 x (logxor64 x y)) y == logand64 y (logand64 x (logxor64 y x)))
