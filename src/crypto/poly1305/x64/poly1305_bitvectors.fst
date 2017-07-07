module Poly1305_bitvectors

open FStar.BV
open FStar.Tactics
open FStar.Tactics.Derived
open FStar.Tactics.BV
module U = FStar.UInt

// val lemma_shr2: x:uint_t' 64 -> Lemma (U.shift_right #64 x 2 == U.udiv #64 x 4)
// let lemma_shr2 x = 
//    assert_by_tactic (bv_tac()) (U.shift_right #64 x 2 == U.udiv #64 x 4)
   
// val lemma_shr4: x:uint_t' 64 -> Lemma (U.shift_right #64 x 4 == U.udiv #64 x 16)
// let lemma_shr4 x =
//   assert_by_tactic (bv_tac ()) (U.shift_right #64 x 4 == U.udiv #64 x 16)

// val lemma_and_mod_n: x:uint_t' 64 -> Lemma (U.logand #64 x 3 == U.mod #64 x 4 /\ 
// 				      U.logand #64 x 15 == U.mod #64 x 16)
// let lemma_and_mod_n x =
//   assert_by_tactic (seq split (bv_tac ())) 
//     (U.logand #64 x 3 == U.mod #64 x 4 /\ U.logand #64 x 15 == U.mod #64 x 16)

// // #reset-options "--z3rlimit_factor 4 --z3rlimit 200 --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --eager_inference --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native"

// #reset-options "--smtencoding.elim_box true --z3cliopt smt.arith.nl=false --z3rlimit 10"
// val lemma_clear_lower_2: x:uint_t' 8 -> Lemma (U.logand #8 x 0xfc == 
// 					U.mul_mod #8 (U.udiv #8 x 4) 4)
// let lemma_clear_lower_2 x =
//   assert_by_tactic (bv_tac ())
//   (U.logand #8 x 0xfc == U.mul_mod #8 (U.udiv #8 x 4) 4)

// val lemma_and_constants: x:uint_t' 64 ->
//   Lemma (U.logand #64 x 0 == 0 /\
// 	U.logand #64 x 0xffffffffffffffff == x)
// let lemma_and_constants x =
//   assert_by_tactic (seq split (bv_tac ()))
//   (U.logand #64 x 0 == (0 <: uint_t' 64) /\ 
//    U.logand #64 x 0xffffffffffffffff == x)

//the problem seems to be that the implicit variable is not resolved.
//one solution would be not to check that it is an arith expression.
// the question is why is it not resolved and will it be later?
val lemma_poly_constants: x:uint_t' 64 -> 
  Lemma (U.logand #64 x 0 < (0 <: uint_t' 64))
let lemma_poly_constants x =
 assert_by_tactic (bv_tac_lt ())
   (squash (U.logand #64 x 0 < (0 <: uint_t' 64)))

// val lemma_poly_constants: x:uint_t' 64 -> 
//   Lemma (U.logand #64 x 0x0ffffffc0fffffff < 0x1000000000000000 /\
// 	U.logand #64 x 0x0ffffffc0ffffffc < 0x1000000000000000 /\
// 	U.mod #64 (U.logand #64 x 0x0ffffffc0ffffffc) 4 == 0)
// let lemma_poly_constants x =
//  assert_by_tactic (split;; split;; 
// 		   bv_tac_lt ();;
// 		   bv_tac_lt ();;
// 		   bv_tac ()) 
//    (U.logand #64 x 0x0ffffffc0fffffff < (0x1000000000000000 <: uint_t' 64) /\
//      U.logand #64 x 0x0ffffffc0ffffffc < (0x1000000000000000 <: uint_t' 64) /\
//      U.mod #64 (U.logand #64 x 0x0ffffffc0ffffffc) 4 == (0 <: uint_t' 64))

// val lemma_and_commutes
