module Bv

(* Define bitwise operators with new type BitVector. *)
val vsize : pos
val bv: Type0

(* Constants *)
val zero_vec: bv
val ones_vec: bv

(* Conversion between nat-bv_t *)
unfold let bv_max = pow2 vsize

val nat_to_bv: x:nat{x < bv_max} -> Tot bv
val bv_to_nat: i:bv -> Tot nat

(* Bitwise operators *)
val logand_vec: a:bv -> b:bv -> Tot bv
val logxor_vec: a:bv -> b:bv -> Tot bv  
val logor_vec :  a:bv -> b:bv -> Tot bv
val lognot_vec: a:bv -> Tot bv

(* Shift operators *)
val shift_left_vec:  a:bv -> s:nat -> Tot bv
val shift_right_vec: a:bv -> s:nat -> Tot bv

val logand_vec_comm (x:bv) (y:bv)
  : Lemma (ensures (logand_vec x y == logand_vec y x))
          [SMTPat (logand_vec x y)]

val logxor_vec_comm (x:bv) (y:bv)
  : Lemma (ensures (logxor_vec x y == logxor_vec y x))
          [SMTPat (logxor_vec x y)]
