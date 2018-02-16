module TypesNative_s

assume val reveal_iand (n:pos) (x y:Types_s.natN (normalize_term (pow2 n))) : Lemma
  (requires True)
  (ensures Types_s.iand x y == FStar.UInt.logand #n x y)

assume val reveal_ixor (n:pos) (x y:Types_s.natN (normalize_term (pow2 n))) : Lemma
  (requires True)
  (ensures Types_s.ixor x y == FStar.UInt.logxor #n x y)

assume val reveal_ior (n:pos) (x y:Types_s.natN (normalize_term (pow2 n))) : Lemma
  (requires True)
  (ensures Types_s.ior x y == FStar.UInt.logor #n x y)

assume val reveal_inot (n:pos) (x:Types_s.natN (normalize_term (pow2 n))) : Lemma
  (requires True)
  (ensures Types_s.inot x == FStar.UInt.lognot #n x)

assume val reveal_ishl (n:pos) (x:Types_s.natN (normalize_term (pow2 n))) (y:nat) : Lemma
  (requires True)
  (ensures Types_s.ishl x y == FStar.UInt.shift_left #n x y)

assume val reveal_ishr (n:pos) (x:Types_s.natN (normalize_term (pow2 n))) (y:nat) : Lemma
  (requires True)
  (ensures Types_s.ishr x y == FStar.UInt.shift_right #n x y)
