module Poly1305_lemmas

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

(*
open FStar.Mul
open FStar.UInt
open Semantics
lemma_BitwiseAdd64()
lemma_BitwiseMul64()
*)


// private unfold let op_Star = op_Multiply

// these settings make it super slow
// #reset-options "--z3rlimit_factor 4 --z3rlimit 300 --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --eager_inference --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native"



#reset-options "--smtencoding.elim_box true --z3cliopt smt.arith.nl=true"

val lemma_mul_div_comm: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0 /\ a % b = 0))
	  (ensures (a/b)*c == a * (c/b))
let lemma_mul_div_comm a b c =
    ()

val lemma_exact_mul: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0))
	  (ensures ((a*c) % b = 0))
let lemma_exact_mul a b c = 
  (* a*c = c*a *)
  swap_mul a c; 

  (* (c*a)%b = ((c%b)*a)%b *)
  lemma_mod_mul_distr_l c a b;
  ()
  
val lemma_mul_div_sep: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0) /\ (a*c) % b = 0)
	  (ensures (a*c)/b == a * (c/b))
let lemma_mul_div_sep a b c = () 



#reset-options "--smtencoding.elim_box true --z3cliopt smt.arith.nl=false"

val swap_add: a:int -> b:int -> c:int -> Lemma
      (a + b + c = a + c + b)
let swap_add a b c = ()


// p used to be a refinement to p > 0 and r1 a nat.
// There are some assumptions here, which will either go away when the library switches to ints everywhere (for division too)
// or when we switch to nats (which is doable right away)
let lemma_poly_multiply' (n:int) (p:int) (r:int) (h:int) (r0:int) (r1:int) (h0:int) (h1:int) (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) : Lemma (requires 
		     p > 0
		  /\ r1 >= 0
		  /\ n > 0
		  /\ 4 * (n * n) == p + 5
		  /\ r == r1 * n + r0
		  /\ h == h2 * (n * n) + h1 * n + h0
		  /\ s1 == r1 + (r1 / 4)
		  /\ r1 % 4 == 0
		  /\ d0 == h0 * r0 + h1 * s1
		  /\ d1 == h0 * r1 + h1 * r0 + h2 * s1
		  /\ d2 == h2 * r0
		  /\ hh == d2 * (n * n) + d1 * n + d0)
	  (ensures (p > 0) /\ (h * r) % p == hh % p)
  = 
    (* unfold h and r*)
      assert ((h * r) == ((h2 * (n * n) + h1 * n + h0) * (r1*n + r0)));
    
    (* do some math using the canonizer *)
      assert_by_tactic canon (((h2 * (n * n) + h1 * n + h0) * (r1*n + r0)) ==
		       (h2 * n + h1) * ((n*n) * r1) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0);
    
    (* proof that (n*n) = (p+5)/4*)
      slash_star_axiom (n*n) 4 (p+5);

    (* proof that ((p+5)/4)*r1 = (p+5)*(r1/4) *)
      lemma_mul_div_comm (p+5) 4 r1;

    (* use the proof above*)
      assert ((h2 * n + h1) * ((n*n)*r1) = (h2 * n + h1) * ((p+5)*(r1/4)));
      //TODO: check if this style of breaking the equalities is actually faster
    (* we currently rely on Z3 to do the ``rewriting`` so we must be
       very careful if we want to keep non-linear arithmetic off. *) 
       
      assert (((h2 * n + h1) * ((n*n)*r1)) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0 == 
      	   ((h2 * n + h1) * ((p+5)*(r1/4)) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0));
      assert (h*r == (h2 * n + h1) * ((p+5)*(r1/4)) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0);

    // helper_lemma_2 does all the work but takes 100s. It times out if no helper is used.
    let helper_lemma_2 (x:int) : Lemma 
       (ensures ((h2 * n + h1) * ((p+5) * x) + (h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0 ==
     			    (h2 * r0) * (n * n) + (h0 * r1 + h1 * r0 + h2 * (5 * x)) * n + 
    			   (h0 * r0 + h1 * (5 * x)) + ((h2*n + h1) *x)*p)) =
       assert_by_tactic canon ((h2 * n + h1) * ((p+5) * x) == (h2 * n + h1) * 5 * x + ((h2*n + h1)*x)*p);

       (*rewrite the equality *)
       assert((h2 * n + h1) * ((p+5) * x) + ((h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0) == 
    		  (h2 * n + h1) * 5 * x + ((h2*n + h1)*x)*p + ((h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0));
       
       (* this is just swapping things, doing it manually is faster. wrap c in parentheses to get a 10s boost.*)
       swap_add ((h2 * n + h1) * 5 * x) (((h2*n + h1)*x)*p) ((h2 * r0) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0);

       let helper_lemma_3 (y:int) : Lemma
    	 (ensures (((h2 * n + h1) * 5 * x + y + (h1*r0 + h0*r1)*n + h0*r0  ==
       			      (y + (h0 * r1 + h1 * r0 + h2 * (5 * x)) * n + (h0 * r0 + h1 * (5 * x)))))) =
       assert_by_tactic canon ((h2 * n + h1) * 5 * x + y + (h1*r0 + h0*r1)*n + h0*r0  ==
       			      (y + (h0 * r1 + h1 * r0 + h2 * (5 * x)) * n + (h0 * r0 + h1 * (5 * x))))
       in 
    	 helper_lemma_3 ((h2 * r0) * (n*n))
    in
    helper_lemma_2 (r1/4);
   
    (* proof that h*r = result of helper_lemma_2*)
      assert (h*r == (h2 * r0) * (n * n) + (h0 * r1 + h1 * r0 + h2 * (5 * (r1/4))) * n + 
      			   (h0 * r0 + h1 * (5 * (r1/4))) + ((h2*n + h1) *(r1/4))*p);
    
    (* unfold definition of hh *)
      assert (hh == (h2*r0)*(n*n) + (h0*r1+h1*r0+h2*(r1+(r1/4)))*n + h0*r0 + h1*(r1+(r1/4)));
    
    (* proof that r1+(r1/4) = 5*(r1/4) *)
      comm_plus #r1 #(r1/4);
      division_addition_lemma r1 4 r1; // (r1 + r1*4)/4 = (r1/4) + r1
      assert_norm (r1 + 4*r1 == 5*r1);
      lemma_mul_div_sep 5 4 r1;
      assert (r1 + (r1/4) = 5*(r1/4));
      
    (* proof that hh == h*r - ((h2*n+h1)*(r1/4))*p*)
      assert (hh == (h2 * r0) * (n * n) + (h0 * r1 + h1 * r0 + h2 * (5 * (r1/4))) * n + 
    			   h0*r0 + h1 * (5 * (r1/4)));    
    (* proof that ((h2*n + h1)*(r1/4))*p % p = 0 *)

    // not sure how to prove that, and stdlib seems to require that it's nat.
      assume ((h2*n + h1) >= 0); 
      assume ((h2*n+h1)*(r1/4) >= 0);
      multiple_modulo_lemma ((h2*n + h1)*(r1/4)) p;

    (* and (a+b*p)%p = a%p*)
    
      assume ((h2 * r0) * (n * n) + (h0 * r1 + h1 * r0 + h2 * (5 * (r1/4))) * n + (h0 * r0 + h1 * (5 * (r1/4))) >= 0);
      lemma_mod_plus ((h2 * r0) * (n * n) + (h0 * r1 + h1 * r0 + h2 * (5 * (r1/4))) * n + (h0 * r0 + h1 * (5 * (r1/4))))
      	((h2*n + h1) *(r1/4)) p;
      assert ((h*r) % p == hh % p)


let lemma_poly_multiply (n:int) (p:int {p>0}) (r:int) (h:int) (r0:int) (r1:nat) (h0:int) (h1:int) (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) : Lemma (requires 
		   4 * (n * n) == p + 5
		  /\ r == r1 * n + r0
		  /\ h == h2 * (n * n) + h1 * n + h0
		  /\ s1 == r1 + (r1 / 4)
		  /\ r1 % 4 == 0
		  /\ d0 == h0 * r0 + h1 * s1
		  /\ d1 == h0 * r1 + h1 * r0 + h2 * s1
		  /\ d2 == h2 * r0
		  /\ hh == d2 * (n * n) + d1 * n + d0)
	  (ensures (h * r) % p == hh % p)
  = 
  lemma_poly_multiply' n p r h r0 r1 h0 h1 h2 s1 d0 d1 d2 hh; ()


(*
let lemma_poly_reduce (n:int) (p:int{ p > 0 }) (h:nat) (h2:int) (h10:int) (c:int) (hh:int)
   : Lemma (requires 4 * (n * n) == p + 5
             /\ h2 == h / (n * n)
             /\ h10 == h % (n * n)
             /\ c == (h2 / 4) + (h2 / 4) * 4
             /\ hh == h10 + c + (h2 % 4) * (n * n))
       (ensures h % p == hh % p)
   = admit()

let lemma_poly_bits64 ()
  : Lemma (requires true)
      (ensures (forall (x:nat64) . shift_right #64 x 2 == x / 4)
        /\  (forall (x:nat64) . shift_right #64 x 4 == x / 16)
        /\  (forall (x:nat64) . logand #64 x 3 == x % 4)
        /\  (forall (x:nat64) . logand #64 x 15 == x % 16)
        /\  (forall (x:nat64) . logand #64 x 0 == 0)
        /\  (forall (x:nat64) . logand #64 x 0xffffffffffffffff == x)
        /\  (forall (x:nat64) . logand #64 x 0xfffffffffffffffc == (x / 4) * 4)
        /\  (forall (x:nat64) . logand #64 x 0x0ffffffc0fffffff < nat64_max / 16)
        /\  (forall (x:nat64) . logand #64 x 0x0ffffffc0ffffffc < nat64_max / 16)
        /\  (forall (x:nat64) . (logand #64 x 0x0ffffffc0ffffffc) % 4 == 0)   
      )
 = admit()    
*)
