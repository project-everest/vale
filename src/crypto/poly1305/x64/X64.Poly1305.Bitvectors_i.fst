module X64.Poly1305.Bitvectors_i
open FStar.BV
open FStar.Tactics
open FStar.Tactics.Derived
open FStar.Tactics.BV
open FStar.Mul
open FStar.UInt
open FStar.Math.Lemmas
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

let lemma_clear_lower_2 x =
  assert_by_tactic
  (logand #64 x 0xfffffffffffffffc == mul_mod #64 (udiv #64 x 4) 4)
  bv_tac
  

let lemma_and_constants x =
 assert_by_tactic (logand #64 x 0 == (0 <: uint_t 64)) bv_tac;
 assert_by_tactic (logand #64 x 0xffffffffffffffff == x) bv_tac


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

let bv128_64_64 x0 x1 = bvor (bvshl (bv_uext #64 #64 x1) 64) (bv_uext #64 #64 x0)

let uint_to_nat (#n:nat) (x:uint_t n) : r:nat{r = x} =
 assert (x < pow2 n);
 modulo_lemma x (pow2 n); 
 x 
 
let uint_ext (#n : nat) (#m : nat{n <= m}) (x : uint_t n) : r:(uint_t m){uint_to_nat r = uint_to_nat x} =
  assert_norm(fits x n);
  pow2_le_compat m n;
  assert_norm(fits x m);
  modulo_lemma x (pow2 m);
  to_uint_t m x

let mul_bvshl (u:uint_t 64) : 
  Lemma (int2bv #128 (0x10000000000000000 `op_Multiply` u) ==
	 bvshl (bv_uext #64 #64 (int2bv u)) 64) = 
  assert ( 0x10000000000000000 * u < pow2 128);
  modulo_lemma (0x10000000000000000 * u) (pow2 128);
  assert_by_tactic 
    (int2bv #128 (mul_mod #128 0x10000000000000000 (uint_ext #64 #128 u)) ==
    bvmul #128 (int2bv #128 0x10000000000000000) (uint_ext #64 #128 u))
    (fun () -> mapply (`trans); arith_to_bv_tac (); trefl ())

let plus_bvor (u h:bv_t 128) : 
  Lemma (bvand u h = bv_zero ==> bvadd u h == bvor u h) = ()
  
		   
let lemma_bv128_64_64_and x x0 x1 y y0 y1 z z0 z1 =
  assert_by_tactic (z == bvand #128 x y) 
		   (fun () -> destruct_conj ();
			   rewrite_eqs_from_context ();
			   norm[delta])

#reset-options "--smtencoding.elim_box true --z3refresh --z3rlimit 12 --max_ifuel 1 --max_fuel 1"
// this should be provable, but it requires  some non trivial effort due to subtypings.
let int2bv_uext_64_128 (x1 : nat) :
  Lemma  (requires (FStar.UInt.size x1 64))
	 (ensures (bv_uext #64 #64 (int2bv #64 x1) = int2bv #128 (uint_ext #64 #128 x1))) =
   assert (64 <= 128);
   pow2_le_compat 128 64;
   assert (x1 < pow2 128);
   modulo_lemma x1 (pow2 128); // x1 % pow2 128 = x1
   assume False;
   assert_by_tactic (bv_uext #64 #64 (int2bv #64 x1) == int2bv #128 x1)
		(fun () -> dump ".."; 
		norm[delta_only ["X64.Poly1305.Bitvectors_i.uint_ext"; "FStar.UInt.to_uint_t"]];
		 // grewrite (quote (x1 % pow2 128)) (quote x1);
		dump "After norm"; smt ())


// this should be provable, but it requires  some non trivial effort due to subtypings.
let bv128_64_64_lowerUpper128u (x0 x1:nat) :
  Lemma (requires (FStar.UInt.size x0 64 /\ FStar.UInt.size x1 64))
	(ensures (int2bv (lowerUpper128u x0 x1) = bv128_64_64 (int2bv x0) (int2bv x1))) =
  mul_bvshl x0;
  plus_bvor (bvshl (bv_uext #64 #64 (int2bv x0)) 64) (bv_uext #64 #64 (int2bv x1));
  assume ((0x10000000000000000)*x0 + x1 == ((0x10000000000000000)*x0 + x1) % pow2 128);
  assume ((size (0x10000000000000000 * x0) 128));
  let x2 : uint_t 128 = x1 in
  let hi : uint_t 128 = (0x10000000000000000 <: uint_t 128) * x0 in
  assert_by_tactic (int2bv #128 (add_mod hi x2) ==
		    bvadd #128 (int2bv #128 hi) (int2bv #128 x2))
		    (fun () -> mapply (`trans); dump "do trans";
			  apply_lemma (`int2bv_add);
			  dump "do apply lemma";
			  trefl ();
			  trefl ();
			  trefl ();
			  dump "after trefl";
			  ());
  assume False
 // int2bv( 0x10000 * x0) == bvshl (bv_uext (int2bcv x0)) 64
 // bvadd (bvshl (bv_uext (int2bv x0) 64)) (bv_uext (int2bv x1)) = bvor (bvshl (bv_uext (int2bv x0) 64)) ..
 // bvadd (int2bv (0x10000 * x0)) (bv_uext (int2bv x1)) = .. 
 // int2bv ((0x1000 * x0) + x1) = bvadd (int2bv (0x1000 *x0)) (int2bv x1)
  

//this was so flaky, new options helped.
#reset-options "--smtencoding.elim_box true --z3refresh --z3rlimit 12 --max_ifuel 1 --max_fuel 1"
let lemma_lowerUpper128_andu (x:uint_t 128) (x0:uint_t 64) (x1:uint_t 64) (y:uint_t 128) 
    (y0:uint_t 64) (y1:uint_t 64) (z:uint_t 128) (z0:uint_t 64) (z1:uint_t 64) :
    Lemma
  (requires z0 == logand #64 x0 y0 /\
            z1 == logand #64 x1 y1 /\
            x == lowerUpper128u x0 x1 /\
            y == lowerUpper128u y0 y1 /\
            z == lowerUpper128u z0 z1)
	    (ensures z == logand #128 x y) =
  bv128_64_64_lowerUpper128u x0 x1;
  bv128_64_64_lowerUpper128u y0 y1;
  bv128_64_64_lowerUpper128u z0 z1;
  assert_by_tactic (int2bv z0 == bvand (int2bv x0) (int2bv y0))
    (fun () -> destruct_conj (); grewrite (quote z0) (quote (logand x0 y0));
	    mapply (`trans); arith_to_bv_tac (); 
	    trefl ();  trefl ());
  assert_by_tactic (int2bv z1 == bvand (int2bv x1) (int2bv y1))
    (fun () -> destruct_conj (); grewrite (quote z1) (quote (logand x1 y1)); 
	    mapply (`trans); arith_to_bv_tac (); 
	      trefl (); trefl ());
  assert (int2bv x == int2bv (lowerUpper128u x0 x1));
  assert (int2bv y == int2bv (lowerUpper128u y0 y1));

  assert_by_tactic (int2bv z == int2bv (lowerUpper128u z0 z1))
    (fun () -> grewrite (quote z) (quote (lowerUpper128u z0 z1)); trefl (); ());
  assert (int2bv x = bv128_64_64 (int2bv x0) (int2bv x1));
  assert (int2bv y = bv128_64_64 (int2bv y0) (int2bv y1));
  assert (int2bv z = bv128_64_64 (int2bv z0) (int2bv z1));
  lemma_bv128_64_64_and (int2bv x) (int2bv x0) (int2bv x1) (int2bv y)
			(int2bv y0) (int2bv y1) (int2bv z) (int2bv z0) (int2bv z1);
  assert_by_tactic (z == logand #128 x y) bv_tac
    

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
