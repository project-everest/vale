module Meta

let generic_injective_proof #a #b f g l =
  let helper (x x':a) : Lemma (f x == f x' ==> x == x')
    =
    if f x = f x' then
      if not (x = x') then (
        let y = f x in
        let y' = f x' in
        assert (y == y');
        let z = g y in
        let z' = g y' in
        assert (z == z');
        l x;
        assert (z == x);
        l x';
        assert (z' == x');
        ()        
      ) else ()
    else
      ()
  in
  FStar.Classical.forall_intro_2 helper;
  ()
