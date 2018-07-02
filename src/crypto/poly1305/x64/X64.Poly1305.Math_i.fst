module X64.Poly1305.Math_i

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
// open Calc
open X64.Vale.State_i   // needed for mem
open X64.Poly1305.Bitvectors_i

// private unfold let op_Star = op_Multiply

#reset-options "--smtencoding.elim_box true --z3cliopt smt.arith.nl=true --max_fuel 1 --max_ifuel 1 --smtencoding.nl_arith_repr native --z3rlimit 100 --using_facts_from Prims --using_facts_from FStar.Math.Lemmas"

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

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=true --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 15"

let lemma_mul_increases(x y:pos) :
  Lemma (y <= y * x) = ()

val multiplication_order_lemma_int: a:int -> b:int -> p:pos ->
    Lemma (a < b <==> p * a < p * b)
let multiplication_order_lemma_int a b p = ()

val multiplication_order_eq_lemma_int: a:int -> b:int -> p:pos ->
    Lemma (a <= b <==> p * a <= p * b)
let multiplication_order_eq_lemma_int a b p = ()

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"

let lemma_poly_multiply (n:int) (p:int) (r:int) (h:int) (r0:int) (r1:int) (h0:int) (h1:int) 
			(h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) =
  let r1:nat = r1 in
  let helper_lemma (x:nat) (y:int) : Lemma 
    (ensures ((h2*n + h1)*((p+5)*x) + y + (h1*r0 + h0*r1)*n + h0*r0 ==
     	      y + (h0*r1 + h1*r0 + h2*(5*x))* n + 
    	      (h0*r0 + h1*(5*x)) + ((h2*n + h1)*x)*p)) =
     assert_by_tactic ((h2*n+h1)*((p+5)*x) == (h2*n+h1)*5*x + ((h2*n+h1)*x)*p) canon;
     assert((h2*n + h1)*((p+5)*x) + (y + (h1*r0 + h0*r1)*n + h0*r0) =
               (h2*n + h1)*5*x + ((h2*n + h1)*x)*p + (y + (h1*r0 + h0*r1)*n + h0*r0));

     (* by swap_add *)
     swap_add ((h2*n + h1)*5*x) (((h2*n + h1)*x)*p)
      			 ((h2*r0)*(n*n) + (h1*r0 + h0*r1)*n + h0*r0);
     assert((h2*n + h1)*5*x + ((h2*n + h1)*x)*p + (y + (h1*r0 + h0*r1)*n + h0*r0) =
             (h2*n + h1)*5*x + (y + (h1*r0 + h0*r1)*n + h0*r0) + ((h2*n + h1)*x)*p);

     assert_by_tactic ((h2*n + h1)*5*x + (y + (h1*r0 + h0*r1)*n + h0*r0) + ((h2*n + h1)*x)*p =
		      y + (h0*r1 + h1*r0 + h2*(5*x))*n + (h0*r0 + h1*(5*x)) + ((h2*n + h1)*x)*p)
		      canon
     in
     assert (h*r = (h2*(n*n) + h1*n + h0)*(r1*n + r0));
     assert_by_tactic ((h2*(n*n) + h1*n + h0)*(r1*n + r0) =
                        (h2*n+h1)*((n*n)*r1)+(h2*r0)*(n*n)+(h1*r0+h0*r1)*n+h0*r0) canon;

     (* by slash_star_axiom and lemma_mul_div_comm *)
     slash_star_axiom (n*n) 4 (p+5);
     lemma_mul_div_comm (p+5) 4 r1;
     assert((h2*n+h1)*((n*n)*r1)+(h2*r0)*(n*n)+(h1*r0+h0*r1)*n+h0*r0 =
            ((h2*n+h1)*((p+5)*(r1/4)))+(h2*r0)*(n*n)+ (h1*r0+h0*r1)*n + h0*r0);

    (* by helper_lemma *)
     helper_lemma (r1/4) ((h2*r0)*(n*n));
     assert(((h2*n+h1)*((p+5)*(r1/4)))+(h2*r0)*(n*n)+ (h1*r0+h0*r1)*n + h0*r0 =
              (h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n +
	      (h0*r0 + h1*(5*(r1/4))) + ((h2*n + h1)*(r1/4))*p);

     (*by comm_plus, division_addition_lemma, lemma_mul_div_sep *)
      comm_plus #r1 #(r1/4);
      division_addition_lemma r1 4 r1;
      lemma_mul_div_sep 5 4 r1;
      assert(r1 + (r1/4) = 5*(r1/4));
      assert (hh == (h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + 
    			   h0*r0 + h1*(5*(r1/4)));
     (* proof that ((h2*n + h1)*(r1/4))*p % p = 0 *)
     // assumptions due to library requiring nats (because some operator is nat only)
     //can we switch to nats?
      assume ((h2*n + h1) >= 0); 
      assume ((h2*n+h1)*(r1/4) >= 0);
      assume ((h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + (h0*r0 + h1*(5*(r1/4))) >= 0);
      multiple_modulo_lemma ((h2*n + h1)*(r1/4)) p;
      (* and (a+b*p)%p = a%p*)
      lemma_mod_plus ((h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + (h0*r0 + h1*(5*(r1/4))))
      	((h2*n + h1)*(r1/4)) p;
      assert ((h*r) % p == hh % p)

let lemma_poly_reduce_nat (n:int) (p:pos) (h:nat) (h2:nat) (h10:int) (c:int) (hh:int) : Lemma
  (requires
    p > 0 /\
    n * n > 0 /\
    h2 >= 0 /\  // TODO: Shouldn't need to add this
    4 * (n * n) == p + 5 /\
    h2 == h / (n * n) /\
    h10 == h % (n * n) /\
    c == (h2 / 4) + (h2 / 4) * 4 /\
    hh == h10 + c + (h2 % 4) * (n * n))
  (ensures h % p == hh % p)
  = 
   lemma_div_mod h (n*n);
   assert (h == (n*n)*h2 + h10);

   assert ((n*n)*h2 + h10 == (n*n)*((h2 / 4) * 4 + h2 % 4) + h10);
   assert_by_tactic ((n*n)*((h2 / 4) * 4 + h2 % 4) + h10 == 
		     (h2 / 4) * (n * n * 4) + (h2 % 4) * (n*n) + h10) canon;
   assert_by_tactic (n * n * 4 = 4 * (n * n)) canon;
   assert ((h2 / 4) * (n * n * 4) + (h2 % 4) * (n*n) + h10 == 
		    (h2 / 4) * (p+5) + (h2 % 4) * (n*n) + h10);
   assert_by_tactic ((h2 / 4) * (p+5) + (h2 % 4) * (n*n) + h10 == 
	    h10 + (h2 % 4) * (n*n) + c + p*(h2 / 4)) canon;
   assert (h10 + (h2 % 4) * (n*n) + c + p*(h2 / 4) == hh + p*(h2/4));
   lemma_mod_lt h2 4;
   lemma_mul_nat_pos_is_nat (h2 % 4) (n*n);
   lemma_mod_lt h (n*n);
   assert (hh >= 0); 
   lemma_mod_plus hh (h2/4) p
      

let lemma_poly_reduce (n:int) (p:int) (h:int) (h2:int) (h10:int) (c:int) (hh:int) =
  lemma_poly_reduce_nat n p h h2 h10 c hh

(* Provable, when we merge the UInt branch and use the lemmas 
   from Poly1305_Bitvectors - operations here are abstract?*)
let lemma_poly_bits64 () =
  admit ()

let lemma_mul_strict_upper_bound (x:int) (x_bound:int) (y:int) (y_bound:int) =
  lemma_mult_lt_right y x x_bound;
  if x_bound = 0 || y_bound = 0 then ()
  else 
    if y = 0 then
    begin
      assert_norm(x*0 = 0); 
      pos_times_pos_is_pos x_bound y_bound
    end
    else
      lemma_mult_lt_left x_bound y y_bound 

// Again provable from Poly1305_Bitvectors
let lemma_bytes_shift_power2 (y:nat64) =
  admit()

//Same
let lemma_bytes_and_mod (x:nat64) (y:nat64) =
  admit()

let lemma_mod_factors(x0:nat) (x1:nat) (y:nat) (z:pos) :
  Lemma ((x0 + (y * z) * x1) % z == (x0 % z)) =
  nat_times_nat_is_nat y x1;
  lemma_mod_plus x0 (y*x1) z;
  assert_by_tactic ((y*z)*x1 == (y*x1)*z) canon

#reset-options "--initial_fuel 0 --max_fuel 0 --smtencoding.elim_box true"
let lemma_mul_pos_pos_is_pos_inverse (x:pos) (y:int) :
  Lemma (requires y*x > 0)
	(ensures y > 0) = 
  if y = 0 then assert_norm (0*x == 0)
  else if y < 0 then assume(False)
  else ()
  
#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"
let lemma_mod_factor_lo(x0:nat64) (x1:nat64) (y:int) (z:pos) :
  Lemma (requires z < 0x10000000000000000 /\
		  y * z == 0x10000000000000000)
	(ensures ((x0 % z) < pow2_64) /\ 
		 lowerUpper128 x0 x1 % z == lowerUpper128 (x0 % z) 0) =
  lemma_mul_pos_pos_is_pos_inverse z y;
  modulo_range_lemma x0 z;
  lemma_mod_factors x0 x1 y z;
  assert_norm(lowerUpper128 x0 x1 % z == lowerUpper128 (x0 % z) 0)

let lemma_mod_power2_lo (x0:nat64) (x1:nat64) (y:int) (z:int) =
    assert (z > 0);
    lemma_mod_factor_lo x0 x1 0x10000000000000000 0x1;
    lemma_mod_factor_lo x0 x1 0x100000000000000 0x100;
    lemma_mod_factor_lo x0 x1 0x1000000000000 0x10000;
    lemma_mod_factor_lo x0 x1 0x10000000000 0x1000000;
    lemma_mod_factor_lo x0 x1 0x100000000 0x100000000;
    lemma_mod_factor_lo x0 x1 0x1000000 0x10000000000;
    lemma_mod_factor_lo x0 x1 0x10000 0x1000000000000;
    lemma_mod_factor_lo x0 x1 0x100 0x100000000000000;
    lemma_bytes_power2 ();
    reveal_opaque (lowerUpper128)

let lemma_power2_add64 (n:nat) =
  pow2_plus 64 n;
  FStar.UInt.pow2_values 64

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=true --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 15"

let lemma_mul_increases(x y:pos) :
  Lemma (y <= y * x) = ()

val multiplication_order_lemma_int: a:int -> b:int -> p:pos ->
    Lemma (a < b <==> p * a < p * b)
let multiplication_order_lemma_int a b p = ()

val multiplication_order_eq_lemma_int: a:int -> b:int -> p:pos ->
    Lemma (a <= b <==> p * a <= p * b)
let multiplication_order_eq_lemma_int a b p = ()

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"

(* lemma_div_mod <-> lemma_fundamental_div_mod *)
let lemma_part_bound1(a:nat) (b:pos) (c:pos):
  Lemma(0<b*c /\ b*(a/b) % (b*c) <= b * (c-1)) =
    lemma_mul_pos_pos_is_pos b c;
    lemma_div_mod (b*(a/b)) (b*c);
    assert (b*(a/b) % (b*c) = b*(a/b) - (b*c)*((b*(a/b))/(b*c)));
    assert_by_tactic (b*(a/b) - (b*c)*((b*(a/b))/(b*c)) == b*(a/b) - b*(c*((b*(a/b))/(b*c)))) 
		     canon; // associativity of mul
    distributivity_sub_right b (a/b) (c*((b*(a/b))/(b*c)));
    assert (b*(a/b) - b*(c*((b*(a/b))/(b*c))) == b*((a/b) - (c*((b*(a/b))/(b*c)))));

    lemma_mod_lt (b*(a/b)) (b*c);
    assert (b*(a/b) % (b*c) < b*c);
    assert (b*((a/b) - (c*((b*(a/b))/(b*c)))) < b*c);
    multiplication_order_lemma_int (((a/b) - (c*((b*(a/b))/(b*c))))) c b;
    assert (((a/b) - (c*((b*(a/b))/(b*c)))) < c);
    assert (((a/b) - (c*((b*(a/b))/(b*c)))) <= c-1);
    multiplication_order_eq_lemma_int ((a/b) - (c*((b*(a/b))/(b*c)))) (c-1) b;
    assert (b*((a/b) - (c*((b*(a/b))/(b*c)))) <= b*(c-1));
    assert (b*(a/b) % (b*c) <= b*(c-1))

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"

let lemma_lt_le_trans (a : nat) (b c : pos) :
  Lemma (requires (a < b) /\ b <= c)
	(ensures a < c) = ()

let lemma_part_bound2 (a : nat) (b c: pos) :
    Lemma(0 < b*c /\ (a%b)%(b*c) < b) = 
    pos_times_pos_is_pos b c; 
    lemma_mod_lt a b; // a%b < b
    assert (0 <= a%b);
    lemma_mul_increases c b; // b <= b * c
    assert (a%b < b);
    lemma_lt_le_trans (a%b) b (b*c);
    assert (a%b < b * c);
    modulo_lemma (a%b) (b*c)  

let lemma_truncate_middle (x:nat) (b c:pos) :
  Lemma (0 < b * c /\ (b*x)%(b*c) == b*(x%c)) =
    pos_times_pos_is_pos b c;
    nat_times_nat_is_nat b x; // or x%c
    lemma_div_mod (b*x) (b*c);
    assert (b*x == (b*c)*((b*x)/(b*c)) + (b*x)%(b*c));

    division_multiplication_lemma (b*x) b c;
    assert ((b*c)*((b*x)/(b*c)) + (b*x)%(b*c) == (b*c)*(((b*x)/b)/c) + (b*x)%(b*c));
    swap_mul b x;
    multiple_division_lemma x b;
    assert((b*c)*(((b*x)/b)/c) + (b*x)%(b*c) == (b*c)*(x/c) + (b*x)%(b*c));

    lemma_div_mod x c;
    assert (b*x == b*(c*(x/c) + x%c));
    distributivity_add_right b (c*(x/c)) (b*(x%c));
    paren_mul_right b c (x/c)

let lemma_mod_breakdown (a:nat) (b:pos) (c:pos) :
  Lemma(0<b*c /\ a%(b*c) == b * ((a/b)%c) + a%b) =
  lemma_mul_pos_pos_is_pos b c;
  nat_over_pos_is_nat a b;

  lemma_part_bound1 a b c;
  assert ((b*(a/b)) % (b*c) + (a%b) % (b*c) <= b*(c-1) + (a%b) % (b*c));
  lemma_part_bound2 a b c;
  assert (b*(c-1) + (a%b) % (b*c) <  b*(c-1) + b);
  assert_by_tactic (b*(c-1) + b == b*c) canon;
  assert ((b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c);

  lemma_div_mod a b;
  assert(a% (b*c) == (b*(a/b) + a%b) % (b*c));
  lemma_mod_lt a b;
  nat_over_pos_is_nat a b;
  nat_times_nat_is_nat b (a/b);
  assert ((b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c);
  modulo_lemma ((b*(a/b)) % (b*c) + (a%b) % (b*c)) (b*c);
  modulo_distributivity (b*(a/b)) (a%b) (b*c); // ((b*(a/b))%(b*c) + (a%b)%(b*c))%(b*c) = ((b*(a/b)) + 
											  //(a%b))%(b*c)
  assert ((b*(a/b) + a%b) % (b*c) == (b*(a/b)) % (b*c) + (a%b) % (b*c));
  lemma_mul_increases c b; // b <= b*c
  
  swap_mul b (a/b);
  modulo_lemma (a%b) (b*c);
  assert ((a%b) % (b*c) == a%b);
  assert ((b*(a/b)) % (b*c) + (a%b) % (b*c) == (b*(a/b)) % (b*c) + a%b);
  lemma_truncate_middle (a/b) b c 
  

#reset-options "--smtencoding.elim_box true --z3rlimit 8 --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"
// using calc it was not even proving the first equation, look into this later
let lemma_mod_hi (x0:nat64) (x1:nat64) (z:nat64) =
  let n = 0x10000000000000000 in   
  assert(lowerUpper128 x0 x1 % lowerUpper128 0 z = (x1 * n + x0) % (z * n));
  lemma_mod_breakdown (x1 * n + x0) n z;  
  assert ((x1 * n + x0) % (z * n) == n * (((x1 * n + x0) / n) % z) + (x1 * n + x0) % n);
  lemma_mod_plus x0 x1 n;
  assert (n * (((x1 * n + x0) / n) % z) + (x1 * n + x0) % n == n * (((x1 * n + x0) / n) % z) + x0 % n);
  assert(n * (((x1 * n + x0) / n) % z) + x0 % n == n * (x1 % z) + x0);
  admit()
  
let lemma_poly_demod (p:pos) (h:int) (x:int) (r:int) =
  admit()


#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 50"
let lemma_reduce128  (h:int) (h2:nat64) (h1:nat64) (h0:nat64) (g:int) (g2:nat64) (g1:nat64) (g0:nat64) =
      admit()
      (*
      reveal_opaque mod2_128';
      assert_norm (mod2_128(g - 0x400000000000000000000000000000000) == mod2_128(g));
      if (g2<4) then
      begin
	assert(h < 0x3fffffffffffffffffffffffffffffffb);
	assert(h >= 0);
        calc(
	     mod2_128(modp(h))
          &= mod2_128(h) &| using (assert (modp(h) == h % 0x3fffffffffffffffffffffffffffffffb)));
	  assert_norm (mod2_128(h) == lowerUpper128 h0 h1) // TODO: assert_norm for Calc
      end
      else
      begin
       assert (0 <= h);
       assert (h - 0x3fffffffffffffffffffffffffffffffb < 
		 0x3fffffffffffffffffffffffffffffffb);
       calc(
            mod2_128(modp(h))
         &= mod2_128(h - 0x3fffffffffffffffffffffffffffffffb) &| 
			  using (assert (modp(h) == h % 0x3fffffffffffffffffffffffffffffffb);
				 assert (h - 0x3fffffffffffffffffffffffffffffffb == h % 
					                 0x3fffffffffffffffffffffffffffffffb))
	 &= mod2_128(g - 0x400000000000000000000000000000000) &| using z3
	 &= mod2_128(g) &| using z3);
       assert_norm (mod2_128(g) == lowerUpper128 g0 g1)
      end;
      *)

let lemma_add_key (old_h0:nat64) (old_h1:nat64) (h_in:int) (key_s0:nat64) (key_s1:nat64) (key_s:int) (h0:nat64) (h1:nat64) = 
  admit()

let lemma_lowerUpper128_and (x:nat128) (x0:nat64) (x1:nat64) (y:nat128) (y0:nat64) (y1:nat64) (z:nat128) (z0:nat64) (z1:nat64) =
  admit()

let lemma_add_mod128 (x y :int) =
  reveal_opaque mod2_128'
