module AES_s

open Types_s
open FStar.List

assume val mix_columns (q:quad32) : quad32
assume val inv_mix_columns (q:quad32) : quad32
assume val sub_bytes (q:quad32) : quad32
assume val inv_sub_bytes (q:quad32) : quad32
assume val shift_rows (q:quad32) : quad32
assume val inv_shift_rows (q:quad32) : quad32
assume val rot_word (w:nat32) : nat32
assume val sub_word (w:nat32) : nat32

type algorithm = | AES_128 | AES_192 | AES_256

let aes_rcon (i:int) =
    if i = 0 then 0x01 else if i = 1 then 0x02 else if i = 2 then 0x04 else if i = 3 then 0x08 else if i = 4 then 0x10 else if i = 5 then 0x20 else if i = 6 then 0x40 else if i = 7 then 0x80 else if i = 8 then 0x1b else 0x36

// AES fixes Rijndael's block size at 4 32-bit words
let nb = 4

// Number of key words
unfold let nk(alg:algorithm) =
  match alg with
  | AES_128 -> 4
  | AES_192 -> 6
  | AES_256 -> 8

// Number of rounds
unfold let nr(alg:algorithm) =
  match alg with
  | AES_128 -> 10
  | AES_192 -> 12
  | AES_256 -> 14

let round (state round_key:quad32) =
  let s = sub_bytes state in
  let s = shift_rows s in
  let s = mix_columns s in
  let s = quad32_xor s round_key in
  s

// TODO: I'm surprised I have to define this
let rec last (l:list 'a {length l >= 1}) =
  match l with
  | x :: [] -> x
  | x :: tl -> last tl

let rec rounds (state:quad32) (round_keys:list quad32 { length round_keys >= 1}) : Tot (quad32*quad32) (decreases %[length round_keys]) =
  match round_keys with
  | final_rk :: [] -> state, final_rk
  | rk :: tl -> rounds (round state rk) tl

let cipher (alg:algorithm) (input:quad32) (round_keys:list quad32{length round_keys == (nr alg) + 1}) = 
  let state = quad32_xor input (hd round_keys) in
  let state, final_rk = rounds state (tl round_keys) in
  let state = sub_bytes state in
  let state = shift_rows state in
  let state = quad32_xor state final_rk in
  state

let nat32_xor (x y:nat32) : nat32 = FStar.UInt.logxor #32 x y


// Need more fuel to prove the match is complete based on length of w
#reset-options "--max_fuel 5 --initial_fuel 5"
open FStar.Mul
let rec expand_key (alg:algorithm) (w:list nat32 { length w >= 4}) : Tot (list nat32) (decreases %[nb * ((nr alg) + 1) - length w]) =
  if length w = 4 then
    rev w
  else if length w >= nb * ((nr alg) + 1) then
    rev w
  else
    match w with
    | last :: _ :: _ :: old :: rest ->  // TODO: This isn't quite right: For AES_192, we look back 6, and for AES_256 we look back 8
      let i = length w in
      let temp = 
	if i % (nk alg) = 0 then
          nat32_xor (sub_word (rot_word last)) (aes_rcon ((i / (nk alg)) - 1))
	else if nk alg > 6 && i % (nk alg) = 4 then
          sub_word last
	else
          last
      in 
	nat32_xor old temp :: w

// Need more fuel to calculate the length of tl below
#reset-options "--max_fuel 5 --initial_fuel 5"
let rec key_schedule_to_round_keys (w:list nat32 {length w % 4 == 0}) =
  match w with
  | [] -> []
  | a :: b :: c :: d :: tl -> 
    Quad32 a b c d :: key_schedule_to_round_keys tl
#reset-options ""  

let aes_encrypt (alg:algorithm) (key:list nat32 {length key == nk alg}) (input:quad32) =
  cipher alg input (key_schedule_to_round_keys (expand_key alg key))

