module Words.Seq_s
open Words_s
open FStar.Seq

let seqn (n:nat) (a:Type) : Type = s:seq a{length s == n}
let seq2 (a:Type) = seqn 2 a
let seq4 (a:Type) = seqn 4 a
let seq8 (a:Type) = seqn 8 a

let seq_to_two_LE (#a:Type) (s:seq2 a) : two a =
  Mktwo (index s 0) (index s 1)

let seq_to_two_BE (#a:Type) (s:seq2 a) : two a =
  Mktwo (index s 1) (index s 0)

let seq_to_four_LE (#a:Type) (s:seq4 a) : four a =
  Mkfour (index s 0) (index s 1) (index s 2) (index s 3)

let seq_to_four_BE (#a:Type) (s:seq4 a) : four a =
  Mkfour (index s 3) (index s 2) (index s 1) (index s 0)

val two_to_seq_LE (#a:Type) (x:two a) : Pure (seq2 a)
  (requires True)
  (ensures fun s ->
    index s 0 == x.lo /\
    index s 1 == x.hi
  )

val two_to_seq_BE (#a:Type) (x:two a) : Pure (seq2 a)
  (requires True)
  (ensures fun s ->
    index s 1 == x.lo /\
    index s 0 == x.hi
  )

val four_to_seq_LE (#a:Type) (x:four a) : Pure (seq4 a)
  (requires True)
  (ensures fun s ->
    index s 0 == x.lo0 /\
    index s 1 == x.lo1 /\
    index s 2 == x.hi2 /\
    index s 3 == x.hi3
  )

val four_to_seq_BE (#a:Type) (x:four a) : Pure (seq4 a)
  (requires True)
  (ensures fun s ->
    index s 3 == x.lo0 /\
    index s 2 == x.lo1 /\
    index s 1 == x.hi2 /\
    index s 0 == x.hi3
  )

