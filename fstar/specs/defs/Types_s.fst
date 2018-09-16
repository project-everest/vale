module Types_s

open Opaque_s
open Words_s
open Words.Two_s
open Words.Four_s

unfold let nat8 = Words_s.nat8
unfold let nat16 = Words_s.nat16
unfold let nat32 = Words_s.nat32
unfold let nat64 = Words_s.nat64

let add_wrap (#n:nat) (x:natN n) (y:natN n) : natN n = if x + y < n then x + y else x + y - n

// abstract bitwise operations on integers:
assume val iand (#n:nat) (a:natN n) (b:natN n) : natN n
assume val ixor (#n:nat) (a:natN n) (b:natN n) : natN n
assume val ior (#n:nat) (a:natN n) (b:natN n) : natN n
assume val inot (#n:nat) (a:natN n) : natN n
assume val ishl (#n:nat) (a:natN n) (s:int) : natN n
assume val ishr (#n:nat) (a:natN n) (s:int) : natN n

unfold let nat32_xor (x y:nat32) : nat32 = ixor x y

type twobits = natN 4
type bits_of_byte = four twobits

let byte_to_twobits (b:nat8) : bits_of_byte = nat_to_four_unfold 2 b

type double32 = two nat32
type quad32 = four nat32

let quad32_xor (x y:quad32) : quad32 = four_map2 nat32_xor x y

let select_word (q:quad32) (selector:twobits) : nat32 = four_select q selector
let insert_nat32 (q:quad32) (n:nat32) (i:twobits) : quad32 = four_insert q n i
let insert_nat64 (q:quad32) (n:nat64) (i:nat1) : quad32 =
  two_two_to_four (two_insert (four_to_two_two q) (nat_to_two 32 n) i)

