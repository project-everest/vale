module AES_s

open Types_s
open FStar.Seq
open FStar.Mul

assume val mix_columns (q:quad32) : quad32
assume val inv_mix_columns (q:quad32) : quad32
assume val sub_bytes (q:quad32) : quad32
assume val inv_sub_bytes (q:quad32) : quad32
assume val shift_rows (q:quad32) : quad32
assume val inv_shift_rows (q:quad32) : quad32
assume val rot_word (w:nat32) : nat32
assume val sub_word (w:nat32) : nat32

type algorithm = | AES_128 | AES_192 | AES_256

let aes_rcon (i:int) : nat32 =
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

let rec rounds (state:quad32) (round_keys:seq quad32)
               (start:nat) (last:nat{start <= last /\ last < length round_keys}) : Tot quad32 (decreases %[last - start]) =
  if start = last then 
    state
  else
    rounds (round state (index round_keys start)) round_keys (start + 1) last

let cipher (alg:algorithm) (input:quad32) (round_keys:seq quad32{length round_keys == (nr alg) + 1}) = 
  let state = quad32_xor input (index round_keys 0) in
  let state = rounds state round_keys 1 (nr alg) in
  let state = sub_bytes state in
  let state = shift_rows state in
  let state = quad32_xor state (index round_keys (nr alg)) in
  state

let nat32_xor (x y:nat32) : nat32 = ixor x y

let rec expand_key (alg:algorithm) (key:seq nat32 { length key == nk alg}) (size:nat{size <= (nb * ((nr alg) + 1))})
  : (ek:seq nat32 {length ek == size}) =
  if size = 0 then createEmpty
  else
    let w = expand_key alg key (size - 1) in
    let i = size - 1 in
    if 0 <= i && i < nk alg then
      append w (create 1 (index key i))
    else
      let temp = 
        if i % (nk alg) = 0 then
	  nat32_xor (sub_word (rot_word (index w (i-1)))) (aes_rcon ((i / (nk alg)) - 1))
	else if nk alg > 6 && i % (nk alg) = 4 then
	  sub_word (index w (i-1))
	else
	  index w (i-1)
      in 
      append w (create 1 (nat32_xor (index w (i - (nk alg))) temp))
	 
let rec key_schedule_to_round_keys (rounds:nat) (w:seq nat32 {length w >= 4 * rounds}) 
  : (round_keys:seq quad32 {length round_keys == rounds}) =
  if rounds = 0 then createEmpty
  else 
    let round_keys = key_schedule_to_round_keys (rounds - 1) w in
    let rk = Quad32 (index w (4 * rounds - 4)) (index w (4 * rounds - 3)) (index w (4 * rounds - 2)) (index w (4 * rounds - 1)) in
    append round_keys (create 1 rk)

let aes_encrypt (alg:algorithm) (key:seq nat32 {length key == nk alg}) (input:quad32) =
  cipher alg input (key_schedule_to_round_keys (nr alg + 1) (expand_key alg key (nb * (nr alg + 1))))

#reset-options "--max_fuel 5 --initial_fuel 5"
abstract let quad32_to_seq (q:quad32) : 
  Tot (s:seq nat32 { length s == 4 /\ 
                     (let q' = Quad32 (index s 0) (index s 1) (index s 2) (index s 3) in
                      q == q')           
                   }) =
  let l = [q.lo; q.mid_lo; q.mid_hi; q.hi] in
  let s = of_list l in
  //assert (List.length l == 4);
  lemma_of_list_length s l; 
  lemma_of_list s l 0;
  lemma_of_list s l 1;
  lemma_of_list s l 2;
  lemma_of_list s l 3;  
  of_list l

