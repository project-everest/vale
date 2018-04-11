module TypesNative_i
open Words_s
open Types_s
open TypesNative_s
open FStar.Seq

unfold let nth (#n:pos) (a:UInt.uint_t n) (i:nat{i < n}) : bool = index (UInt.to_vec #n a) i
unfold let natN = Words_s.natN
unfold let pow2_norm = Words_s.pow2_norm

val lemma_equal_nth (n:pos) (x y:natN (pow2_norm n)) : Lemma
  (requires (forall (i:nat).{:pattern (nth #n x i) \/ (nth #n y i)} i < n ==> nth #n x i == nth #n y i))
  (ensures x == y)

val lemma_zero_nth (n:nat) : Lemma
  (forall (i:nat{i < n}).{:pattern (nth #n 0 i)} not (nth #n 0 i))

val lemma_quad32_vec_equal (a b:quad32) : Lemma
  (requires (
    let Mkfour a0 a1 a2 a3 = a in
    let Mkfour b0 b1 b2 b3 = b in
    equal (UInt.to_vec #32 a0) (UInt.to_vec #32 b0) /\
    equal (UInt.to_vec #32 a1) (UInt.to_vec #32 b1) /\
    equal (UInt.to_vec #32 a2) (UInt.to_vec #32 b2) /\
    equal (UInt.to_vec #32 a3) (UInt.to_vec #32 b3)
  ))
  (ensures a == b)

val lemma_iand_nth_i (n:pos) (x y:natN (pow2_norm n)) (i:nat{i < n}) : Lemma
  (nth #n (iand x y) i == (nth #n x i && nth #n y i))

val lemma_ixor_nth_i (n:pos) (x y:natN (pow2_norm n)) (i:nat{i < n}) : Lemma
  (nth #n (ixor x y) i == (nth #n x i <> nth #n y i))

val lemma_ior_nth_i (n:pos) (x y:natN (pow2_norm n)) (i:nat{i < n}) : Lemma
  (nth #n (ior x y) i == (nth #n x i || nth #n y i))

val lemma_inot_nth_i (n:pos) (x:natN (pow2_norm n)) (i:nat{i < n}) : Lemma
  (nth #n (inot x) i == not (nth #n x i))

val lemma_ishl_nth_i (n:pos) (x:natN (pow2_norm n)) (y:nat) (i:nat{i < n}) : Lemma
  (nth #n (ishl x y) i == (i + y < n && nth #n x (i + y)))

val lemma_ishr_nth_i (n:pos) (x:natN (pow2_norm n)) (y:nat) (i:nat{i < n}) : Lemma
  (nth #n (ishr x y) i == (i - y >= 0 && nth #n x (i - y)))

val lemma_iand_nth (n:pos) (x y:natN (pow2_norm n)) : Lemma
  (forall (i:nat{i < n}).{:pattern (nth #n (iand x y) i)}
    nth #n (iand x y) i == (nth #n x i && nth #n y i))

val lemma_ixor_nth (n:pos) (x y:natN (pow2_norm n)) : Lemma
  (forall (i:nat{i < n}).{:pattern (nth #n (ixor x y) i)}
    nth #n (ixor x y) i == (nth #n x i <> nth #n y i))

val lemma_ior_nth (n:pos) (x y:natN (pow2_norm n)) : Lemma
  (forall (i:nat{i < n}).{:pattern (nth #n (ior x y) i)}
    nth #n (ior x y) i == (nth #n x i || nth #n y i))

val lemma_inot_nth (n:pos) (x:natN (pow2_norm n)) : Lemma
  (forall (i:nat{i < n}).{:pattern (nth #n (inot x) i)}
    nth #n (inot x) i == not (nth #n x i))

val lemma_ishl_nth (n:pos) (x:natN (pow2_norm n)) (y:nat) : Lemma
  (forall (i:nat{i < n}).{:pattern (nth #n (ishl x y) i)}
    nth #n (ishl x y) i == (i + y < n && nth #n x (i + y)))

val lemma_ishr_nth (n:pos) (x:natN (pow2_norm n)) (y:nat) : Lemma
  (forall (i:nat{i < n}).{:pattern (nth #n (ishr x y) i)}
    nth #n (ishr x y) i == (i - y >= 0 && nth #n x (i - y)))

val lemma_iand_nth_all (n:pos) : Lemma
  (forall (x y:natN (pow2_norm n)).{:pattern (iand x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (iand x y) i)}
      nth #n (iand x y) i == (nth #n x i && nth #n y i)))

val lemma_ixor_nth_all (n:pos) : Lemma
  (forall (x y:natN (pow2_norm n)).{:pattern (ixor x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (ixor x y) i)}
      nth #n (ixor x y) i == (nth #n x i <> nth #n y i)))

val lemma_ior_nth_all (n:pos) : Lemma
  (forall (x y:natN (pow2_norm n)).{:pattern (ior x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (ior x y) i)}
      nth #n (ior x y) i == (nth #n x i || nth #n y i)))

val lemma_inot_nth_all (n:pos) : Lemma
  (forall (x:natN (pow2_norm n)).{:pattern (inot x)}
    (forall (i:nat{i < n}).{:pattern (nth #n (inot x) i)}
      nth #n (inot x) i == not (nth #n x i)))

val lemma_ishl_nth_all (n:pos) : Lemma
  (forall (x:natN (pow2_norm n)) (y:nat).{:pattern (ishl x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (ishl x y) i)}
      nth #n (ishl x y) i == (i + y < n && nth #n x (i + y))))

val lemma_ishr_nth_all (n:pos) : Lemma
  (forall (x:natN (pow2_norm n)) (y:nat).{:pattern (ishr x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (ishr x y) i)}
      nth #n (ishr x y) i == (i - y >= 0 && nth #n x (i - y))))

val reveal_iand_all (n:pos) : Lemma
  (forall (x y:natN (pow2_norm n)).{:pattern (iand x y)}
    iand x y == UInt.logand #n x y)

val reveal_ixor_all (n:pos) : Lemma
  (forall (x y:natN (pow2_norm n)).{:pattern (ixor x y)}
    ixor x y == UInt.logxor #n x y)

val reveal_ior_all (n:pos) : Lemma
  (forall (x y:natN (pow2_norm n)).{:pattern (ior x y)}
    ior x y == UInt.logor #n x y)

val reveal_inot_all (n:pos) : Lemma
  (forall (x:natN (pow2_norm n)).{:pattern (inot x)}
    inot x == UInt.lognot #n x)

val reveal_ishl_all (n:pos) : Lemma
  (forall (x:natN (pow2_norm n)) (y:nat).{:pattern (ishl x y)}
    ishl x y == UInt.shift_left #n x y)

val reveal_ishr_all (n:pos) : Lemma
  (forall (x:natN (pow2_norm n)) (y:nat).{:pattern (ishr x y)}
    ishr x y == UInt.shift_right #n x y)

