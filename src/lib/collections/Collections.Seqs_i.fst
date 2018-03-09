module Collections.Seqs_i

let lemma_empty_ambient (#a:Type) (s:seq a) :
  Lemma (length s = 0 ==> s == createEmpty #a) 
  [SMTPat (length s = 0)]
  = lemma_empty s

let lemma_append_empty_ambient (#a:Type) (s:seq a) :
  Lemma (append s createEmpty == s /\ append createEmpty s == s)
  [SMTPatOr [ 
    [SMTPat (append s createEmpty)]; 
    [SMTPat (append createEmpty s)]
  ]]
  = append_empty_l s; append_empty_r s

let lemma_slice_first_exactly_in_append (#a:eqtype) (x y:seq a) :
  Lemma (slice (append x y) 0 (length x) == x) =
  let xy = append x y in
  let xy_slice = slice xy 0 (length x) in
  let x_slice = slice x 0 (length x) in
  assert(eq xy_slice x_slice);   // OBSERVE: extensionality
  //assert(eq x_slice x);
  ()

let lemma_all_but_last_append (#t:eqtype) (a:seq t) (b:seq t{length b > 0}) :
  Lemma (all_but_last (append a b) == append a (all_but_last b)) =
  let ab = all_but_last (append a b) in
  let app_a_b = append a (all_but_last b) in
  (*
  assert(length ab == length app_a_b);
  let helper (i:int) : Lemma (0 <= i /\ i < length ab ==> index ab i == index app_a_b i) =
    if 0 <= i && i < length ab then (
      if i < length a then ()
      else ()
    ) else ()
  in
  FStar.Classical.forall_intro helper;
  *)
  assert (eq ab app_a_b)  // OBSERVE: extensionality


//#reset-options "--use_two_phase_tc true"  // Needed for some assertions below
let rec reverse_seq_append (#a:eqtype) (s:seq a) (t:seq a) : 
  Lemma(ensures reverse_seq (append s t) == append (reverse_seq t) (reverse_seq s))
       (decreases %[length s])
  =
  if length s = 0 then ()
  else (
    let (st:seq a{length s > 0}) = append s t in
    //assert(length st > 0);  
    let head_seq = create 1 (head st) in
    lemma_head_append s t;
    //assert (head s == head st);
    //assert (reverse_seq st == append (reverse_seq (tail st)) head_seq); 
    lemma_tail_append s t; 
    //assert (tail st == append (tail s) t);    
    //assert (reverse_seq #a (tail st) == reverse_seq (append (tail s) t));
    reverse_seq_append (tail s) t;
    //assert(reverse_seq (append (tail s) t) == append (reverse_seq t) (reverse_seq (tail s)));
    append_assoc (reverse_seq t) (reverse_seq (tail s)) head_seq;
    ()
  )

#reset-options "--initial_fuel 2 --max_fuel 2"
let rec reverse_reverse_seq (#a:eqtype) (s:seq a) : 
  Lemma(ensures reverse_seq (reverse_seq s) == s)
       (decreases %[length s]) 
  =
  if length s = 0 then ()
  else (    
    assert(length s > 0);
    let h = create 1 (head s) in
    let t = tail s in 
    reverse_reverse_seq t;
    //assert ( reverse_seq s == append (reverse_seq t) h);
    //assert ( reverse_seq (reverse_seq t) == t );
    reverse_seq_append (reverse_seq t) h;
    //assert ( reverse_seq (append (reverse_seq t) h) ==
    //	     append (reverse_seq (reverse_seq h)) 
    //		    (reverse_seq (reverse_seq t)));
    //append_empty_l h;		      
    //assert (reverse_seq h == h);
    //assert (reverse_seq (reverse_seq h) == h);
    //assert ( reverse_seq (append (reverse_seq t) h) ==
    //	     append h t);
    cons_head_tail s;
    //assert (append h t == s);	       
    ()
  )
