module X64.Poly1305.Bitvectors_i
open FStar.BV
open FStar.Tactics
open FStar.Tactics.Derived
open FStar.Tactics.BV
open FStar.Mul
open FStar.UInt
open Vale.Tactics

// tweak options?
#reset-options "--smtencoding.elim_box true"

//NOTE: Using the split tactic seems to slowdown execution by a lot.

let lemma_shr2 x = 
  assert_by_tactic (shift_right #64 x 2 == udiv #64 x 4) bv_tac
   
let lemma_shr4 x =
  assert_by_tactic (shift_right #64 x 4 == udiv #64 x 16) bv_tac

let lemma_and_mod_n x =
  assert_by_tactic (logand #64 x 3 == mod #64 x 4) (bv_tac);
  assert_by_tactic (logand #64 x 15 == mod #64 x 16) (bv_tac)
  // assert_by_tactic (logand #64 x 3 == mod #64 x 4 /\ logand #64 x 15 == mod #64 x 16)
  //                  (fun () -> seq split bv_tac)

let lemma_clear_lower_2 x =
  assert_by_tactic
  (logand #64 x 0xfffffffffffffffc == mul_mod #64 (udiv #64 x 4) 4)
  bv_tac
  

let lemma_and_constants x =
 assert_by_tactic (logand #64 x 0 == (0 <: uint_t 64)) bv_tac;
 assert_by_tactic (logand #64 x 0xffffffffffffffff == x) bv_tac
 // assert_by_tactic 
 // (logand #64 x 0 == (0 <: uint_t 64) /\ 
 //  logand #64 x 0xffffffffffffffff == x)
 // (fun () -> seq split bv_tac)

let lemma_poly_constants x =
 // using split in this seems to hang execution.
  assert_by_tactic  
    (logand #64 x 0x0ffffffc0fffffff < (0x1000000000000000 <: uint_t 64)) 
      (fun () ->  bv_tac_lt 64);
  assert_by_tactic
    (logand #64 x 0x0ffffffc0ffffffc < (0x1000000000000000 <: uint_t 64)) 
      (fun () -> bv_tac_lt 64);
  assert_by_tactic
    (mod #64 (logand #64 x 0x0ffffffc0ffffffc) 4 == (0 <: uint_t 64)) 
      (fun () -> bv_tac ())
// assert_by_tactic  
//   (logand #64 x 0x0ffffffc0fffffff < (0x1000000000000000 <: uint_t 64) /\
//     logand #64 x 0x0ffffffc0ffffffc < (0x1000000000000000 <: uint_t 64) /\
//     mod #64 (logand #64 x 0x0ffffffc0ffffffc) 4 == (0 <: uint_t 64))
//  (fun () -> split(); split (); 
// 		   bv_tac_lt 64;
// 		   bv_tac_lt 64;
// 		   bv_tac ())

let lemma_and_commutes x y =
  assert_by_tactic 
    (logand #64 x y == logand #64 y x)
    bv_tac

let lemma_bv128_64_64_and_helper' (x0:bv_t 64) (x1:bv_t 64) (y0:bv_t 64) (y1:bv_t 64) :
  Lemma (requires True)
	(ensures ((bvor #128 (bvshl #128 (bv_uext #64 #64 (bvand #64 x1 y1)) 64) 
					 (bv_uext #64 #64 (bvand #64 x0 y0))) == 
		   bvand #128 (bvor #128 (bvshl #128 (bv_uext #64 #64 x1) 64) 
						     (bv_uext #64 #64 x0)) 
			      (bvor #128 (bvshl #128 (bv_uext #64 #64 y1) 64)
						     (bv_uext #64 #64 y0)))) = ()

// Rewrite all equalities and then the goal is trivial for Z3.
// Without rewriting this does not go through.
// I believe the reason is related to a previously reported issue with the way
// Z3 bit-blasts through the Boxing/Unboxing functions. I thought this was fixed
// but it may not be the case. Notice that by rewriting with tactics the solver
// only gets to see one big term without any boxing or unboxing inside it.
let lemma_bv128_64_64_and_helper x x0 x1 y y0 y1 z z0 z1 =
  lemma_bv128_64_64_and_helper' x0 x1 y0 y1;
  assert_by_tactic (z == bvand #128 x y) 
		   (fun () -> destruct_conj ();
			   rewrite_eqs_from_context ())

let bv128_64_64 x1 x0 = bvor (bvshl (bv_uext #64 #64 x1) 64) (bv_uext #64 #64 x0)

open FStar.Math.Lemmas

let uint_to_nat (#n:pos) (x:uint_t n) : r:nat{r = x} =
 assert (x < pow2 n);
 modulo_lemma x (pow2 n); 
 x 

let uint_ext (#n : pos) (#m : pos{n < m}) (x : uint_t n) : r:(uint_t m){uint_to_nat r = uint_to_nat x} =
  assert_norm(fits x n);
  pow2_lt_compat m n;
  assert_norm(fits x m);
  modulo_lemma x (pow2 m);
  to_uint_t m x


// let bv128_64_64_spec' (x1 x0 : bv_t 64) :
//   Lemma (bvadd (bv_uext #64 #64 (bvmul (int2bv 0x10000000000000000) x1)) (uint_ext #64 #128 x0) ==
// 	  bv128_64_64 x1 x0) =
//   assert (bvadd (bv_uext #64 #64 (bvmul (int2bv 0x10000000000000000) x1)) (uint_ext #64 #128 x0) ==
// 	  bv128_64_64 x1 x0);
// 	  assume False

// #reset-options "--smtencoding.elim_box true --log_queries --z3refresh --z3rlimit 8"
// let bv128_64_64_spec' (x1 x0 : uint_t 64) :
//   Lemma (int2bv #128 (0x10000000000000000 `op_Multiply` x1 + x0) ==
// 	 (bv128_64_64 (int2bv x1) (int2bv x0))
//   ) =
//   assert (bvadd (bvmul (int2bv #128 0x00000000000000010000000000000000) (uint_ext #64 #128 x1)) 
// 		(int2bv #128 (uint_ext #64 #128 x0)) = bv128_64_64 (int2bv x1) (int2bv x0));
// 	  assume False
  
		   

let lemma_bv128_64_64_and x x0 x1 y y0 y1 z z0 z1 =
  assert_by_tactic (z == bvand #128 x y) 
		   (fun () -> destruct_conj ();
			   rewrite_eqs_from_context ();
			   norm[delta])

#reset-options "--smtencoding.elim_box true --z3cliopt smt.case_split=3"
let lemma_bytes_shift_constants0 x =
  assert_by_tactic (shift_left #64 0 3 == (0 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 0 == (0x1 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants1 x =
  assert_by_tactic (shift_left #64 1 3 == (8 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 8 == (0x100 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants2 x =
  assert_by_tactic (shift_left #64 2 3 == (16 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 16 == (0x10000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants3 x =
  assert_by_tactic (shift_left #64 3 3 == (24 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 24 == (0x1000000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants4 x =
  assert_by_tactic (shift_left #64 4 3 == (32 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 32 == (0x100000000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants5 x =
  assert_by_tactic (shift_left #64 5 3 == (40 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 40 == (0x10000000000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants6 x =
  assert_by_tactic (shift_left #64 6 3 == (48 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 48 == (0x1000000000000 <: uint_t 64)) bv_tac   
let lemma_bytes_shift_constants7 x =
  assert_by_tactic (shift_left #64 7 3 == (56 <: uint_t 64)) bv_tac; 
  assert_by_tactic (shift_left #64 1 56 == (0x100000000000000 <: uint_t 64)) bv_tac

let lemma_bytes_and_mod0 x = 
  assert_by_tactic (logand #64 x (0x1 - 1) == mod #64 x 0x1) bv_tac

let lemma_bytes_and_mod1 x = 
  assert_by_tactic (logand #64 x (0x100 - 1) == mod #64 x 0x100) bv_tac

let lemma_bytes_and_mod2 x = 
  assert_by_tactic (logand #64 x (0x10000 - 1) == mod #64 x 0x10000) bv_tac
let lemma_bytes_and_mod3 x =
  assert_by_tactic (logand #64 x (0x1000000 - 1) == mod #64 x 0x1000000) bv_tac

let lemma_bytes_and_mod4 x = 
  assert_by_tactic (logand #64 x (0x100000000 - 1) == mod #64 x 0x100000000) bv_tac

let lemma_bytes_and_mod5 x = 
  assert_by_tactic (logand #64 x (0x10000000000 - 1) == mod #64 x 0x10000000000) bv_tac

let lemma_bytes_and_mod6 x = 
  assert_by_tactic (logand #64 x (0x1000000000000 - 1) == mod #64 x 0x1000000000000) bv_tac

let lemma_bytes_and_mod7 x = 
  assert_by_tactic (logand #64 x (0x100000000000000 - 1) == mod #64 x 0x100000000000000) bv_tac

let lemma_bytes_and_mod x y =
  match y with
  | 0 ->
      lemma_bytes_shift_constants0 ();
      lemma_bytes_and_mod0 x
  | 1 ->
    lemma_bytes_shift_constants1 ();
    lemma_bytes_and_mod1 x
  | 2 ->
    lemma_bytes_shift_constants2 ();
    lemma_bytes_and_mod2 x    
  | 3 ->
    lemma_bytes_shift_constants3 ();
    lemma_bytes_and_mod3 x
  | 4 -> 
     lemma_bytes_shift_constants4 ();
     lemma_bytes_and_mod4 x
  | 5 ->
    lemma_bytes_shift_constants5 ();
    lemma_bytes_and_mod5 x
  | 6 ->
    lemma_bytes_shift_constants6 ();
    lemma_bytes_and_mod6 x
  | 7 ->
    lemma_bytes_shift_constants7 ();
    lemma_bytes_and_mod7 x
  | _ -> magic ()

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
  (match y with
  | 0 -> 
    lemma_bytes_shift_constants0 ()
  | 1 -> 
    lemma_bytes_shift_constants1 ()
  | 2 ->
    lemma_bytes_shift_constants2 ()
  | 3 ->
    lemma_bytes_shift_constants3 ()
  | 4 ->
    lemma_bytes_shift_constants4 ()
  | 5 ->
    lemma_bytes_shift_constants5 ()
  | 6 ->
    lemma_bytes_shift_constants6 ()
  | 7 ->
    lemma_bytes_shift_constants7 ()
  | _ -> ());
  lemma_bytes_power2 ()


// val lowerUpper128: l:uint_t 64 -> u:uint_t 64 -> Tot (uint_t 128)
// let lowerUpper128 l u = l + (0x10000000000000000 * u)

// val lemma_lowerUpper128_and: x:uint_t 128 -> x0:uint_t 64 -> x1:uint_t 64 ->
//   y:uint_t 128 -> y0:uint_t 64 -> y1:uint_t 64 ->
//   z:uint_t 128 -> z0:uint_t 64 -> z1:uint_t 64 ->
//   Lemma (requires (z0 == logand #64 x0 y0 /\
// 		   z1 == logand #64 x1 y1 /\
// 		   x == lowerUpper128 x1 x0 /\
// 		   y == lowerUpper128 y1 y0 /\
// 		   z == lowerUpper128 z1 z0))
// 	(ensures (z == logand #128 x y))
// let lemma_lowerUpper128_and x x0 x1 y y0 y1 z z0 z1 = ()
