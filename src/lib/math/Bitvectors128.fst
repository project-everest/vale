module Bitvectors128

open FStar.UInt
open FStar.BV
open FStar.Mul
open Calc

#reset-options "--smtencoding.elim_box true --z3cliopt smt.CASE_SPLIT=3 --z3rlimit 25 --z3cliopt smt.arith.nl=true --max_ifuel 0"

let mod2_128 (x:int): uint_t 128 = x % 0x100000000000000000000000000000000

let lemma_bv128_lowerUpper_helper1 (x1:uint_t 64) :
  Lemma (mod2_128(x1 * 0x10000000000000000) == x1 * 0x10000000000000000) =
  ()

let lemma_bv128_lowerUpper x0 x1 =
  calc(
       mod2_128(mod2_128(x1 * 0x10000000000000000) + x0)
    &= mod2_128(x1 * 0x10000000000000000 + x0) &| using 
					 (lemma_bv128_lowerUpper_helper1 x1));
  assume(False)
    // lemma_bv128_lowerUpper_helper1(x1); }
    //               { reveal_mod2_128(); }
    //     x1 * 0x1_0000_0000_0000_0000 + x0;                     { reveal_lowerUpper128(); }
    //     lowerUpper128(x0, x1);
    // }
    
let lemma_bv128_lowerUpper_B128 (x0:uint_t 64) (x1:uint_t 64) = 
  lemma_bv128_lowerUpper x0 x1;
  inverse_vec_lemma #128 (bv128_64_64 (int2bv #64 x1) (int2bv #64 x0));
  admit ()

#reset-options "--smtencoding.elim_box true --z3cliopt smt.CASE_SPLIT=3 --z3rlimit 25 --z3cliopt smt.arith.nl=false --max_ifuel 0"
let lemma_bv128_64_64_and x x0 x1 y y0 y1 z z0 z1 =
  ()
