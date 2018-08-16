module Types_i

open Types_s
open Words_s
open Words.Four_s
open Words.Two_s

let lo64 (q:quad32) : nat64 = two_to_nat 32 (two_select (four_to_two_two q) 0)
let hi64 (q:quad32) : nat64 = two_to_nat 32 (two_select (four_to_two_two q) 1)
