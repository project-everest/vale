module X64.Poly1305.Bitvectors_i
open FStar.BV
open FStar.Tactics
open FStar.Tactics.BV
open FStar.Mul
open FStar.UInt.Vectors
open FStar.UInt.Types
open FStar.UInt.Base

// tweak options?
#reset-options "--smtencoding.elim_box true"




val lemma_shr2: (x:uint_t 64) -> Lemma
  ((shift_right #64 x 2 == udiv #64 x 4))
  // [SMTPat (shift_right #64 x 2)]
let lemma_shr2 x = 
   assert_by_tactic (bv_tac()) (shift_right #64 x 2 == udiv #64 x 4)

val lemma_shr4: x:uint_t 64 -> Lemma (shift_right #64 x 4 == udiv #64 x 16)
				    // [SMTPat (shift_right #64 x 4)]
let lemma_shr4 x =
  assert_by_tactic (bv_tac ()) (shift_right #64 x 4 == udiv #64 x 16)

val lemma_and_mod_3: x:uint_t 64 -> Lemma (logand #64 x 3 == mod #64 x 4)
				   // [SMTPat (logand #64 x 3)]
let lemma_and_mod_3 x =
  assert_by_tactic (bv_tac ())
    (logand #64 x 3 == mod #64 x 4)
    
val lemma_and_mod_15: x:uint_t 64 -> Lemma (logand #64 x 15 == mod #64 x 16)
				   // [SMTPat (logand #64 x 15)]
let lemma_and_mod_15 x =
  assert_by_tactic (bv_tac ()) 
    (logand #64 x 15 == mod #64 x 16)

let lemma_clear_lower_2 x =
  assert_by_tactic (bv_tac ())
  (logand #8 x 0xfc == mul_mod #8 (udiv #8 x 4) 4)

val lemma_and_0: x:uint_t 64 ->
  Lemma (logand #64 x 0 == 0)
  // [SMTPat (logand #64 x 0)]
let lemma_and_0 x =
  assert_by_tactic (bv_tac ())
  (logand #64 x 0 == (0 <: uint_t 64))

val lemma_and_ones: x:uint_t 64 ->
  Lemma (logand #64 x 0xffffffffffffffff == x)
  // [SMTPat (logand #64 x 0xffffffffffffffff)]
let lemma_and_ones x =
   assert_by_tactic (bv_tac ())
     (logand #64 x 0xffffffffffffffff == x)

val lemma_poly_constants_1: x:uint_t 64 -> 
  Lemma (logand #64 x 0x0ffffffc0fffffff < 0x1000000000000000)
  // [SMTPat (logand #64 x 0x0ffffffc0fffffff)]
let lemma_poly_constants_1 x =
  assert_by_tactic (bv_tac_lt 64)
    (logand #64 x 0x0ffffffc0fffffff < (0x1000000000000000 <: uint_t 64))

val lemma_poly_constants_2: x:uint_t 64 ->
  Lemma (logand #64 x 0x0ffffffc0ffffffc < 0x1000000000000000)
  // [SMTPat (logand #64 x 0x0ffffffc0ffffffc)]
let lemma_poly_constants_2 x =
  assert_by_tactic (bv_tac_lt 64)
    (logand #64 x 0x0ffffffc0ffffffc < (0x1000000000000000 <: uint_t 64))

val lemma_poly_constants_3: x:uint_t 64 ->
  Lemma (mod #64 (logand #64 x 0x0ffffffc0ffffffc) 4 == 0)
  // [SMTPat (logand #64 x 0x0ffffffc0ffffffc)]
let lemma_poly_constants_3 x =
  assert_by_tactic (bv_tac ())
    (mod #64 (logand #64 x 0x0ffffffc0ffffffc) 4 == (0 <: uint_t 64))

val lemma_and_commutes: x:uint_t 64 -> y:uint_t 64 ->
  Lemma (logand #64 x y == logand #64 y x)
  // [SMTPat (logand #64 x y == logand #64 y x)]
let lemma_and_commutes x y =
  assert_by_tactic (bv_tac ())
    (logand #64 x y == logand #64 y x)

// let lemma_bv128_64_64_and_helper x x0 x1 y y0 y1 z z0 z1 =
//   admit ()

// let bv128_64_64 x1 x0 = bvor (bvshl (bv_uext #64 #64 x1) 64) (bv_uext #64 #64 x0)

// let lemma_bv128_64_64_and x x0 x1 y y0 y1 z z0 z1 =
//   admit ()

#reset-options "--smtencoding.elim_box true --z3cliopt smt.case_split=3"
let lemma_bytes_shift_constants0 x =
  assert_by_tactic (bv_tac())
    (shift_left #64 0 3 == (0 <: uint_t 64));
  assert_by_tactic (bv_tac())
    (shift_left #64 1 0 == (0x1 <: uint_t 64))
let lemma_bytes_shift_constants1 x =
  assert_by_tactic (bv_tac())
    (shift_left #64 1 3 == (8 <: uint_t 64));
  assert_by_tactic (bv_tac())
    (shift_left #64 1 8 == (0x100 <: uint_t 64))
let lemma_bytes_shift_constants2 x =
  assert_by_tactic (bv_tac())
    (shift_left #64 2 3 == (16 <: uint_t 64));
  assert_by_tactic (bv_tac())
    (shift_left #64 1 16 == (0x10000 <: uint_t 64))
let lemma_bytes_shift_constants3 x =
  assert_by_tactic (bv_tac())
    (shift_left #64 3 3 == (24 <: uint_t 64));
  assert_by_tactic (bv_tac())
    (shift_left #64 1 24 == (0x1000000 <: uint_t 64))
let lemma_bytes_shift_constants4 x =
  assert_by_tactic (bv_tac())
    (shift_left #64 4 3 == (32 <: uint_t 64));
    assert_by_tactic (bv_tac())
    (shift_left #64 1 32 == (0x100000000 <: uint_t 64))
let lemma_bytes_shift_constants5 x =
  assert_by_tactic (bv_tac())
    (shift_left #64 5 3 == (40 <: uint_t 64));
  assert_by_tactic (bv_tac())
    (shift_left #64 1 40 == (0x10000000000 <: uint_t 64))
let lemma_bytes_shift_constants6 x =
  assert_by_tactic (bv_tac())
    (shift_left #64 6 3 == (48 <: uint_t 64));
  assert_by_tactic (bv_tac())
    (shift_left #64 1 48 == (0x1000000000000 <: uint_t 64))   
let lemma_bytes_shift_constants7 x =
  assert_by_tactic (bv_tac())
    (shift_left #64 7 3 == (56 <: uint_t 64)); 
  assert_by_tactic (bv_tac())
    (shift_left #64 1 56 == (0x100000000000000 <: uint_t 64))

let lemma_bytes_and_mod0 x = 
  assert_by_tactic (bv_tac ()) 
    (logand #64 x (0x1 - 1) == mod #64 x 0x1)

let lemma_bytes_and_mod1 x = 
  assert_by_tactic (bv_tac ()) 
    (logand #64 x (0x100 - 1) == mod #64 x 0x100)

let lemma_bytes_and_mod2 x = 
  assert_by_tactic (bv_tac ()) 
    (logand #64 x (0x10000 - 1) == mod #64 x 0x10000)
let lemma_bytes_and_mod3 x =
  assert_by_tactic (bv_tac ())
    (logand #64 x (0x1000000 - 1) == mod #64 x 0x1000000)

let lemma_bytes_and_mod4 x = 
  assert_by_tactic (bv_tac ()) 
    (logand #64 x (0x100000000 - 1) == mod #64 x 0x100000000)

let lemma_bytes_and_mod5 x = 
  assert_by_tactic (bv_tac ()) 
    (logand #64 x (0x10000000000 - 1) == mod #64 x 0x10000000000)

let lemma_bytes_and_mod6 x = 
  assert_by_tactic (bv_tac ()) 
    (logand #64 x (0x1000000000000 - 1) == mod #64 x 0x1000000000000)

let lemma_bytes_and_mod7 x = 
  assert_by_tactic (bv_tac ()) 
    (logand #64 x (0x100000000000000 - 1) == mod #64 x 0x100000000000000)

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

// let lowerUpper128 l u = l + (0x10000000000000000 * u)
// let lemma_lowerUpper128_and x x0 x1 y y0 y1 z z0 z1 = admit ()

// open X64.Vale.Decls  // needed for shift_right64, logand64
// open X64.Machine_s   // needed for mem

// #reset-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

// let lemma_poly_bits64 () =
//   assert(forall (x:nat64). shift_right #64 x 2 == x / 4);
//   assert(forall (x:nat64) (y:nat64). logand64 x y == logand #64 x y);
//   assert(forall (x:nat64). logand #64 x 3 == mod #64 x 4);
//   assert(forall (x:nat64). logand #64 x 15 == mod #64 x 16);
//   assert(forall (x:nat64). logand #64 x 0 == 0);
//   assert ((forall (x:nat64).	logand #64 x 0xffffffffffffffff == x));
//   assert (forall (x:nat64). logand #64 x 0xfffffffffffffffc == (x / 4) * 4);
//   assert (forall (x:nat64). logand #64 x 0x0ffffffc0fffffff < nat64_max / 16);
//   assert (forall (x:nat64). logand #64 x 0x0ffffffc0ffffffc < nat64_max / 16);
//   assert (forall (x:nat64). mod #64 (logand #64 x 0x0ffffffc0ffffffc) 4 == 0)
