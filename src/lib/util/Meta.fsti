module Meta

val generic_injective_proof : #a:eqtype -> #b:eqtype -> f:(a->b) -> g:(b->a) -> l:(x:a -> Lemma (g (f x) == x)) 
  -> Lemma (forall (x x':a) . f x == f x' ==> x == x')
