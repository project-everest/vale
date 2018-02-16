module TypesNative_s

assume val reveal_logand (n:pos) (x y:Types_s.natN (normalize_term (pow2 n))) : Lemma
  (requires True)
  (ensures Types_s.logand x y == FStar.UInt.logand #n x y)

assume val reveal_logxor (n:pos) (x y:Types_s.natN (normalize_term (pow2 n))) : Lemma
  (requires True)
  (ensures Types_s.logxor x y == FStar.UInt.logxor #n x y)

assume val reveal_logor (n:pos) (x y:Types_s.natN (normalize_term (pow2 n))) : Lemma
  (requires True)
  (ensures Types_s.logor x y == FStar.UInt.logor #n x y)

assume val reveal_lognot (n:pos) (x:Types_s.natN (normalize_term (pow2 n))) : Lemma
  (requires True)
  (ensures Types_s.lognot x == FStar.UInt.lognot #n x)

assume val reveal_shift_left (n:pos) (x:Types_s.natN (normalize_term (pow2 n))) (y:nat) : Lemma
  (requires True)
  (ensures Types_s.shift_left x y == FStar.UInt.shift_left #n x y)

assume val reveal_shift_right (n:pos) (x:Types_s.natN (normalize_term (pow2 n))) (y:nat) : Lemma
  (requires True)
  (ensures Types_s.shift_right x y == FStar.UInt.shift_right #n x y)
