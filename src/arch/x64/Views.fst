module Views

let inverses8 (u:unit) =
  reveal_opaque get8_def;
  reveal_opaque put8_def;
  let aux (x:Seq.lseq UInt8.t 1) : Lemma (put8 (get8 x) == x) =
    assert (Seq.equal x (put8 (get8 x)))
  in Classical.forall_intro aux

let inverses16 (u:unit) =
  reveal_opaque get16_def;
  reveal_opaque put16_def;
  let aux (x:Seq.lseq UInt8.t 2) : Lemma (put16 (get16 x) == x) =
    assert (Seq.equal x (put16 (get16 x)))
  in Classical.forall_intro aux

#set-options "--z3rlimit 20"

let inverses32 (u:unit) =
  reveal_opaque get32_def;
  reveal_opaque put32_def;
  let aux (x:Seq.lseq UInt8.t 4) : Lemma (put32 (get32 x) == x) =
    assert (Seq.equal x (put32 (get32 x)))
  in Classical.forall_intro aux

// TODO
let inverses64 (u:unit) = admit()

let inverses128 (u:unit) =
  reveal_opaque get128_def;
  reveal_opaque put128_def;
  reveal_opaque put32_def;
  reveal_opaque get32_def;
  inverses32 ();
  let aux1 (x:Seq.lseq UInt8.t 16) : Lemma (put128 (get128 x) == x) =
    let vg = get128 x in
    let vp = put128 vg in
    assert (vg.lo0 == UInt32.v (get32 (Seq.slice x 0 4)));
    assert (vg.lo1 == UInt32.v (get32 (Seq.slice x 4 8)));
    assert (vg.hi2 == UInt32.v (get32 (Seq.slice x 8 12)));
    assert (vg.hi3 == UInt32.v (get32 (Seq.slice x 12 16)));
    assert (Seq.equal x vp)
  in
  let aux2 (x:quad32) : Lemma (get128 (put128 x) == x) =
    let vp = put128 x in
    let vg = get128 vp in
    assert (vg.lo0 == UInt32.v (get32 (Seq.slice vp 0 4)));
    assert (vg.lo1 == UInt32.v (get32 (Seq.slice vp 4 8)));
    assert (vg.hi2 == UInt32.v (get32 (Seq.slice vp 8 12)));
    assert (vg.hi3 == UInt32.v (get32 (Seq.slice vp 12 16)));
    ()
  in
  Classical.forall_intro aux1;
  Classical.forall_intro aux2

