module Bv64

// open FStar.Mul

(* Define bitwise operators with new type BitVector. *)
assume new type bv64: Type0

(* Constants *)
assume val zero_vec: bv64
assume val ones_vec: bv64

(* Conversion between nat-bv_t *)
unfold let nat64_max = 0x10000000000000000

assume val nat_to_bv: x:nat{x < nat64_max} -> Tot bv64
assume val bv_to_nat: i:bv64 -> Tot nat

(* Bitwise operators *)
assume val logand_vec: a:bv64 -> b:bv64 -> Tot (bv64)
assume val logxor_vec: a:bv64 -> b:bv64 -> Tot (bv64)  
assume val logor_vec:  a:bv64 -> b:bv64 -> Tot (bv64)
assume val lognot_vec: a:bv64 -> Tot (bv64)

(* Shift operators *)
assume val shift_left_vec:  a:bv64 -> s:nat -> Tot (bv64)
assume val shift_right_vec: a:bv64 -> s:nat -> Tot (bv64)

assume val logand_vec_comm (x:bv64) (y:bv64)
  : Lemma (ensures (logand_vec x y == logand_vec y x))
          [SMTPat (logand_vec x y)]

assume val logxor_vec_comm (x:bv64) (y:bv64)
  : Lemma (ensures (logxor_vec x y == logxor_vec y x))
          [SMTPat (logxor_vec x y)]
