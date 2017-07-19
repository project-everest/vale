module X64.Poly1305.Bitvectors_i

(*
open FStar.BV
open FStar.Tactics
open FStar.Tactics.Derived
open FStar.Tactics.BV
open FStar.Mul
module U = FStar.UInt

// tweak options?
#reset-options "--smtencoding.elim_box true"

let lemma_shr2 x = 
   assert_by_tactic (bv_tac()) (U.shift_right #64 x 2 == U.udiv #64 x 4)
   
let lemma_shr4 x =
  assert_by_tactic (bv_tac ()) (U.shift_right #64 x 4 == U.udiv #64 x 16)

let lemma_and_mod_n x =
  assert_by_tactic (seq split (bv_tac ())) 
    (U.logand #64 x 3 == U.mod #64 x 4 /\ U.logand #64 x 15 == U.mod #64 x 16)

let lemma_clear_lower_2 x =
  assert_by_tactic (bv_tac ())
  (U.logand #8 x 0xfc == U.mul_mod #8 (U.udiv #8 x 4) 4)

let lemma_and_constants x =
  assert_by_tactic (seq split (bv_tac ()))
  (U.logand #64 x 0 == (0 <: uint_t' 64) /\ 
   U.logand #64 x 0xffffffffffffffff == x)

let lemma_poly_constants x =
 assert_by_tactic (split;; split;; 
		   bv_tac_lt 64;;
		   bv_tac_lt 64;;
		   bv_tac ()) 
   (U.logand #64 x 0x0ffffffc0fffffff < (0x1000000000000000 <: uint_t' 64) /\
     U.logand #64 x 0x0ffffffc0ffffffc < (0x1000000000000000 <: uint_t' 64) /\
     U.mod #64 (U.logand #64 x 0x0ffffffc0ffffffc) 4 == (0 <: uint_t' 64))

let lemma_and_commutes x y =
  assert_by_tactic (bv_tac ())
    (U.logand #64 x y == U.logand #64 y x)

let lemma_bv128_64_64_and_helper x x0 x1 y y0 y1 z z0 z1 =
  ()

let bv128_64_64 x1 x0 = bvor (bvshl (bv_uext #64 #64 x1) 64) (bv_uext #64 #64 x0)

let lemma_bv128_64_64_and x x0 x1 y y0 y1 z z0 z1 =
  ()


(* is lowerUpper128 useful? *)
// val lowerUpper128: l:uint_t' 64 -> u:uint_t' 64 -> Tot (uint_t' 128)
// let lowerUpper128 l u = l + (0x10000000000000000 * u)

// val lemma_lowerUpper128_and: x:uint_t' 128 -> x0:uint_t' 64 -> x1:uint_t' 64 ->
//   y:uint_t' 128 -> y0:uint_t' 64 -> y1:uint_t' 64 ->
//   z:uint_t' 128 -> z0:uint_t' 64 -> z1:uint_t' 64 ->
//   Lemma (requires (z0 == U.logand #64 x0 y0 /\
// 		   z1 == U.logand #64 x1 y1 /\
// 		   x == lowerUpper128 x1 x0 /\
// 		   y == lowerUpper128 y1 y0 /\
// 		   z == lowerUpper128 z1 z0))
// 	(ensures (z == U.logand #128 x y))
// let lemma_lowerUpper128_and x x0 x1 y y0 y1 z z0 z1 =
  

let lemma_bytes_shift_constants () =
  assert_by_tactic (seq split (bv_tac()))
    (U.shift_left #64 0 3 == 0 /\
      U.shift_left #64 1 3 == 8);
  assert_by_tactic (seq split (bv_tac()))
      (U.shift_left #64 2 3 == 16 /\
       U.shift_left #64 3 3 == 24);
  assert_by_tactic (seq split (bv_tac()))
    (U.shift_left #64 4 3 == 32 /\
     U.shift_left #64 5 3 == 40);
  assert_by_tactic (seq split (bv_tac()))
    (U.shift_left #64 6 3 == 48 /\
      U.shift_left #64 7 3 == 56);
  assert_by_tactic (seq split (bv_tac()))
  (U.shift_left #64 1 0 == 0x1 /\
    U.shift_left #64 1 8 == 0x100);
  assert_by_tactic (seq split (bv_tac()))
    (U.shift_left #64 1 16 == 0x10000 /\
      U.shift_left #64 1 24 == 0x1000000);
  assert_by_tactic (seq split (bv_tac()))
    (U.shift_left #64 1 32 == 0x100000000 /\
      U.shift_left #64 1 40 == 0x10000000000);
  assert_by_tactic (seq split (bv_tac()))
    (U.shift_left #64 1 48 == 0x1000000000000 /\
      U.shift_left #64 1 56 == 0x100000000000000);
  ()

let lemma_bytes_and_mod0 x = ()

let lemma_bytes_and_mod1 x = ()

let lemma_bytes_and_mod2 x = ()

let lemma_bytes_and_mod3 x = ()

let lemma_bytes_and_mod4 x = ()

let lemma_bytes_and_mod5 x = ()

let lemma_bytes_and_mod6 x = ()

let lemma_bytes_and_mod7 x = ()

let lemma_bytes_and_mod_bv x y z =
    lemma_bytes_shift_constants ();
    lemma_bytes_and_mod0 x;
    lemma_bytes_and_mod1 x;
    lemma_bytes_and_mod2 x;
    lemma_bytes_and_mod3 x;
    lemma_bytes_and_mod4 x;
    lemma_bytes_and_mod5 x;
    lemma_bytes_and_mod6 x;
    lemma_bytes_and_mod7 x;
    ()

// val lemma_bytes_and_mod: x: bv_t 64 -> y:bv_t 64 -> z:bv_t 64 ->
//   Lemma (requires (bvult #64 y (int2bv #64 8) /\
//   		   z == bvshl #64 (int2bv #64 1) (bv2int (bvshl y 3))))
// 	 (ensures (z <> bv_zero #64 /\ bvult #64 (bvshl y 3) (int2bv #64 64)))
// let lemma_bytes_and_mod_bv x y z =
//     lemma_bytes_and_mod0 x;
//     lemma_bytes_and_mod1 x;
//     lemma_bytes_and_mod2 x;
//     lemma_bytes_and_mod3 x;
//     lemma_bytes_and_mod4 x;
//     lemma_bytes_and_mod5 x;
//     lemma_bytes_and_mod6 x;
//     lemma_bytes_and_mod7 x;
//     ()

let lemma_bytes_power2 () =
  assert_norm (pow2 0 == 0x1);
  assert_norm (pow2 8 == 0x100);
  assert_norm (pow2 16 == 0x10000);
  assert_norm (pow2 24 == 0x1000000);
  assert_norm (pow2 32 == 0x100000000);
  assert_norm (pow2 40 == 0x10000000000);
  assert_norm (pow2 48 == 0x1000000000000);
  assert_norm (pow2 56 == 0x100000000000000);
  ()

let lemma_bytes_shift_power2 y =
  // assert_by_tactic (bv_tac_lt 64) (U.shift_left #64 y 3 < (64 <: uint_t' 64));
  // assert_by_tactic (bv_tac ()) (y * 8 == U.shift_left #64 y 3);
    assume (U.shift_left #64 y 3 < (64 <: uint_t' 64));
    assume (y * 8 == U.shift_left #64 y 3);
    lemma_bytes_shift_constants ();
    lemma_bytes_power2 ()
*)
