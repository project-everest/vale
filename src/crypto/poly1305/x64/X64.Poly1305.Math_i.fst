module X64.Poly1305.Math_i

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
open Calc
open X64.Vale.State_i   // needed for mem

(*
open FStar.Mul
open FStar.UInt
open Semantics
lemma_BitwiseAdd64()
lemma_BitwiseMul64()
*)


// private unfold let op_Star = op_Multiply

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --eager_inference --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native"


let rec poly1305_heap_blocks' (h:int) (pad:int) (r:int) (m:mem) (i:int) 
        (k:int{i <= k /\ (k - i) % 16 == 0 /\ (forall (j:int) . {:pattern (m `Map.contains` j)} i <= j /\ j < k /\ (j - i) % 8 = 0 ==> m `Map.contains` j)}) : Tot int (decreases (k-i))
    =
    if i = k then h
    else
        let kk = k - 16 in
	assert (i >= 0 ==> precedes (kk - i) (k-i));
	assert (i < 0 ==> precedes (kk - i) (k-i));
	let hh = poly1305_heap_blocks' h pad r m i kk in
        modp((hh + pad + nat64_max * m.[kk + 8] + m.[kk]) * r)

(* Getting a weird error otherwise, will file an issue 
   when this gets merged in fstar branch *)
let poly1305_heap_blocks (h:int) (pad:int) (r:int) (m:mem) (i:int) 
                         (k:int{i <= k /\ (k - i) % 16 == 0 /\ (forall (j:int) . i <= j /\ j < k /\ (j - i) % 8 = 0 ==> m `Map.contains` j)}) : int
 = poly1305_heap_blocks' h pad r m i k


#reset-options "--smtencoding.elim_box true --z3cliopt smt.arith.nl=true --max_fuel 1 --max_ifuel 1 --z3rlimit 100 --using_facts_from Prims --using_facts_from FStar.Math"

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

val swap_add: a:int -> b:int -> c:int -> Lemma
      (a + b + c = a + c + b)
let swap_add a b c = ()


#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"

let lemma_poly_multiply (n:int) (p:pos) (r:int) (h:int) (r0:int) (r1:nat) (h0:int) (h1:int) 
			(h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) =
  let helper_lemma (x:nat) (y:int) : Lemma 
    (ensures ((h2*n + h1)*((p+5)*x) + y + (h1*r0 + h0*r1)*n + h0*r0 ==
     	      y + (h0*r1 + h1*r0 + h2*(5*x))* n + 
    	      (h0*r0 + h1*(5*x)) + ((h2*n + h1)*x)*p)) =
     assert_by_tactic ((h2*n+h1)*((p+5)*x) == (h2*n+h1)*5*x + ((h2*n+h1)*x)*p) canon;
    calc (
      (h2*n + h1)*((p+5)*x) + (y + (h1*r0 + h0*r1)*n + h0*r0)
      &= (h2*n + h1)*5*x + ((h2*n + h1)*x)*p + (y + (h1*r0 + h0*r1)*n + h0*r0) &| using z3
      &= (h2*n + h1)*5*x + (y + (h1*r0 + h0*r1)*n + h0*r0) + ((h2*n + h1)*x)*p &| 
      	 using (swap_add ((h2*n + h1)*5*x) 
			 (((h2*n + h1)*x)*p)
      			 ((h2*r0)*(n*n) + (h1*r0 + h0*r1)*n + h0*r0))
      &= y + (h0*r1 + h1*r0 + h2*(5*x))*n + (h0*r0 + h1*(5*x)) + ((h2*n + h1)*x)*p &|| canon
      )
  in
    calc(  
      h*r 
      &= (h2*(n*n) + h1*n + h0)*(r1*n + r0) &| using z3
      &= (h2*n+h1)*((n*n)*r1)+(h2*r0)*(n*n)+(h1*r0+h0*r1)*n+h0*r0 &|| canon
      &= ((h2*n+h1)*((p+5)*(r1/4)))+(h2*r0)*(n*n)+ 
    	 (h1*r0+h0*r1)*n + h0*r0 &| using (slash_star_axiom (n*n) 4 (p+5);
					   lemma_mul_div_comm (p+5) 4 r1; 
					   z3)
      &= (h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + 
      	 (h0*r0 + h1*(5*(r1/4))) + ((h2*n + h1)*(r1/4))*p  &| using (helper_lemma (r1/4)
								       ((h2*r0)*(n*n)); z3)
     );
      calc(
      	r1 + (r1/4) 
      	&= 5*(r1/4) &| using (comm_plus #r1 #(r1/4);
      		              division_addition_lemma r1 4 r1;
      			      lemma_mul_div_sep 5 4 r1)
      );
    // assumptions due to library requiring nats, can we switch to nats?
      assume ((h2*n + h1) >= 0); 
      assume ((h2*n+h1)*(r1/4) >= 0);
      assume ((h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + (h0*r0 + h1*(5*(r1/4))) >= 0);
      assert (hh == (h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + 
    			   h0*r0 + h1*(5*(r1/4)));
    (* proof that ((h2*n + h1)*(r1/4))*p % p = 0 *)
      multiple_modulo_lemma ((h2*n + h1)*(r1/4)) p;
    (* and (a+b*p)%p = a%p*)
      lemma_mod_plus ((h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + (h0*r0 + h1*(5*(r1/4))))
      	((h2*n + h1)*(r1/4)) p;
      assert ((h*r) % p == hh % p)

let lemma_poly_reduce (n:int) (p:pos) (h:nat) (h2:nat) (h10:int) (c:int) (hh:int) =
  lemma_div_mod h (n*n);
  assert (h == (n*n)*h2 + h10);
  calc(
    h 
      &= (n*n)*h2 + h10 &| using (lemma_div_mod h (n*n))
      &= (n*n)*((h2 / 4) * 4 + h2 % 4) + h10 &| using z3
      &= h10 + (h2 % 4)*(n*n) + (h2 / 4) * (p+5) &|| 
					(paren_mul_right (h2/4) 4 (n*n); canon)
      &= h10 + (h2 % 4)*(n*n) + (h2/4)*5 + p*(h2/4) &|| canon
      &= h10 + (h2 % 4)*(n*n) + c + p*(h2/4) &| using z3
      &= hh + p*(h2/4) &| using z3);
  assume (hh >= 0); // this is provable in this case, but so annoying
  lemma_mod_plus hh (h2/4) p
 
let lemma_poly_bits64 =
  admit()

let lemma_mul_strict_upper_bound (x:nat) (x_bound:int) (y:nat) (y_bound:int) =
  admit()

let lemma_bytes_shift_power2 (y:nat64) =
  admit()

let lemma_bytes_and_mod (x:nat64) (y:nat64) =
  admit()

let lemma_mod_power2_lo (x0:nat64) (x1:nat64) (y:int) (z:int) =
  admit()

let lemma_power2_add64 (n:nat) =
  admit()

let lemma_mod_hi (x0:nat64) (x1:nat64) (z:nat64) =
  admit()

let lemma_poly_demod (p:int) (h:int) (x:int) (r:int) =
  admit()

let lemma_reduce128  (h:int) (h2:nat64) (h1:nat64) (h0:nat64) (g:int) (g2:nat64) (g1:nat64) (g0:nat64) =
  admit()

let lemma_add_key (old_h0:nat64) (old_h1:nat64) (h_in:int) (key_s0:nat64) (key_s1:nat64) (key_s:int) (h0:nat64) (h1:nat64) = 
  admit()

let lemma_lowerUpper128_and (x:nat128) (x0:nat64) (x1:nat64) (y:nat128) (y0:nat64) (y1:nat64) (z:nat128) (z0:nat64) (z1:nat64) =
  admit()

let lemma_poly1305_heap_hash_blocks (h) (pad) (r) (m) (i) (k) (len) =
  admit()
  // decreases k - i
