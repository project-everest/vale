module Words.Seq_i

open FStar.Seq
open Words_s
open Words.Four_s
open Words.Seq_s
open FStar.Mul

(*
let le_quad32_to_bytes (b:quad32) : seqn 16 nat8 =
  seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE b))

let le_bytes_to_seq_quad32 (b:seq nat8{length b % 16 == 0}) : seq quad32 =
  seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE b)

Goal: le_bytes_to_seq_quad32 ( le_quad32_to_bytes b) == b

      seq_to_seq_four_LE (
       seq_map (four_to_nat 8) (seq_to_seq_four_LE      
			       (seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE b)))))  = b
*)

let seq_to_seq_four_to_seq_LE  (#a:Type) (x:seq (four a)) :
  Lemma (seq_to_seq_four_LE (seq_four_to_seq_LE x) == x)
  [SMTPat (seq_to_seq_four_LE (seq_four_to_seq_LE x))]
  =
  let bytes = seq_four_to_seq_LE x in
  let fours = seq_to_seq_four_LE bytes in
  assert (equal fours x);
  ()

let four_to_seq_to_four_LE (#a:Type) (x:seq4 a) :
  Lemma (four_to_seq_LE (seq_to_four_LE x) == x)
  =
  assert (equal (four_to_seq_LE (seq_to_four_LE x)) x);
  ()

let seq_four_to_seq_to_seq_four_LE (#a:Type) (x:seq a{length x % 4 == 0}) :
  Lemma (seq_four_to_seq_LE (seq_to_seq_four_LE x) == x)
  =
  assert (equal (seq_four_to_seq_LE (seq_to_seq_four_LE x)) x);
  ()

unfold let pow2_24 = 16777216 //normalize_term (pow2 24)

let lemma_fundamental_div_mod_4 (x:nat32) :
  Lemma (x = x % pow2_8 + pow2_8 * ((x / pow2_8) % pow2_8) + pow2_16 * ((x / pow2_16) % pow2_8) + pow2_24 * ((x / pow2_24) % pow2_8))
  =
  ()

let four_to_nat_to_four_8 (x:natN (pow2_norm 32)) :
  Lemma (four_to_nat 8 (nat_to_four 8 x) == x)
  [SMTPat (four_to_nat 8 (nat_to_four 8 x))]
  =
  let size = 8 in
  let n1 = pow2_norm size in
  let n2 = pow2_norm (2 * size) in
  let n3 = pow2_norm (3 * size) in
  let n4 = pow2_norm (4 * size) in
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 0x10000);
  assert_norm (pow2 24 == 0x1000000);
  assert_norm (pow2 32 == 0x100000000);
  let fourX = nat_to_four 8 x in
  assert_norm (nat_to_four 8 x == Mkfour (x % n1) ((x / n1) % n1) ((x / n2) % n1) ((x / n3) % n1));
  let Mkfour x0 x1 x2 x3 = fourX in
  let x' = x0 + x1 * n1 + x2 * n2 + x3 * n3 in
  assert_norm (four_to_nat 8 fourX == int_to_natN n4 (x0 + x1 * n1 + x2 * n2 + x3 * n3));  
  lemma_fundamental_div_mod_4 x;
  ()

let nat_to_four_to_nat (x:four (natN (pow2_norm 8))) :
  Lemma (nat_to_four 8 (four_to_nat 8 x) == x)
  [SMTPat (nat_to_four 8 (four_to_nat 8 x) == x)]
  =
    let size = 8 in
  let n1 = pow2_norm size in
  let n2 = pow2_norm (2 * size) in
  let n3 = pow2_norm (3 * size) in
  let n4 = pow2_norm (4 * size) in
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 0x10000);
  assert_norm (pow2 24 == 0x1000000);
  assert_norm (pow2 32 == 0x100000000);
  let x' = four_to_nat 8 x in
  assert_norm (nat_to_four 8 x' == Mkfour (x' % n1) ((x' / n1) % n1) ((x' / n2) % n1) ((x' / n3) % n1));
  let Mkfour x0 x1 x2 x3 = x in
  let x' = x0 + x1 * n1 + x2 * n2 + x3 * n3 in
  assert_norm (four_to_nat 8 x == int_to_natN n4 (x0 + x1 * n1 + x2 * n2 + x3 * n3));
  lemma_fundamental_div_mod_4 x';
  ()


(*
let seq_four_to_seq_LE (#a:Type) (x:seq (four a)) : seq a =
  let f (n:nat{n < length x * 4}) = four_select (index x (n / 4)) (n % 4) in
  init (length x * 4) f

val four_to_seq_LE (#a:Type) (x:four a) : Pure (seq4 a)
  (requires True)
  (ensures fun s ->
    index s 0 == x.lo0 /\
    index s 1 == x.lo1 /\
    index s 2 == x.hi2 /\
    index s 3 == x.hi3
  )
*)

let four_to_seq_LE_is_seq_four_to_seq_LE(#a:Type) (x:four a) : 
  Lemma (four_to_seq_LE x == seq_four_to_seq_LE (create 1 x))
  =
  let s0 = four_to_seq_LE x  in
  let s1 = seq_four_to_seq_LE (create 1 x) in
  assert (equal s0 s1);
  ()
