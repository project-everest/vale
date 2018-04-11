module Types_s

open Words_s
open Words.Four_s
open Words.Seq_s
open Collections.Seqs_s

unfold let nat8 = Words_s.nat8
unfold let nat16 = Words_s.nat16
unfold let nat32 = Words_s.nat32
unfold let nat64 = Words_s.nat64

let add_wrap (#n:nat) (x:natN n) (y:natN n) : natN n = if x + y < n then x + y else x + y - n

// abstract bitwise operations on integers:
assume val iand : #n:nat -> a:natN n -> b:natN n -> natN n
assume val ixor : #n:nat -> a:natN n -> b:natN n -> natN n
assume val ior : #n:nat -> a:natN n -> b:natN n -> natN n
assume val inot : #n:nat -> a:natN n  -> natN n
assume val ishl : #n:nat -> a:natN n -> s:int -> natN n
assume val ishr : #n:nat -> a:natN n -> s:int -> natN n

// Alias
unfold let nat32_xor (x y:nat32) : nat32 = ixor x y

type twobits = natN 4
type bits_of_byte = four twobits

unfold let byte_to_twobits (b:nat8) : bits_of_byte = nat_to_four_unfold 2 b

type double32 = two nat32
type quad32 = four nat32

let quad32_xor (x y:quad32) : quad32 = four_map2 nat32_xor x y

let select_word (q:quad32) (selector:twobits) : nat32 = four_select q selector
let insert_nat32 (q:quad32) (n:nat32) (i:twobits) : quad32 = four_insert q n i

open FStar.Seq

let be_bytes_to_nat32 (b:seq4 nat8) : Tot nat32 =
  four_to_nat 8 (seq_to_four_BE b)

let nat32_to_be_bytes (n:nat32) : Tot (b:seq4 nat8 { be_bytes_to_nat32 b == n }) =
  let b = four_to_seq_BE (nat_to_four 8 n) in
  assume (be_bytes_to_nat32 b == n);
  b

assume val be_bytes_to_nat32_to_be_bytes (b:seq nat8 {length b == 4}) : 
  Lemma (nat32_to_be_bytes (be_bytes_to_nat32 b) == b)

let reverse_bytes_nat32 (n:nat32) : Tot (nat32) =
  be_bytes_to_nat32 (reverse_seq (nat32_to_be_bytes n))

let reverse_bytes_quad32 (q:quad32) : quad32 =
  four_reverse (four_map reverse_bytes_nat32 q)

// Reverses the bytes in each nat32, but not the nat32s themselves
let reverse_bytes_nat32_seq (s:seq nat32) : s':seq nat32 { length s == length s' } =
  seq_map reverse_bytes_nat32 s
