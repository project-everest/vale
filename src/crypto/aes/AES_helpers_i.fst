module AES_helpers_i

open Types_s
open FStar.Seq
open AES_s

let rec key_expansion_specific (alg:algorithm) (key:seq nat32 { length key == nk alg})
                               (w:seq nat32) (i:nat{i < length w}) =
    if 0 <= i && i < nk alg then
      index w i == index key i
    else
      let temp = 
        if i % (nk alg) = 0 then
	  nat32_xor (sub_word (rot_word (index w (i-1)))) (aes_rcon ((i / (nk alg)) - 1))
	else if nk alg > 6 && i % (nk alg) = 4 then
	  sub_word (index w (i-1))
	else
	  index w (i-1)
      in 
      index w i == nat32_xor (index w (i - (nk alg))) temp


let key_expansion_partial (alg:algorithm) (key:seq nat32 { length key == nk alg}) 
                          (w:seq nat32) (end_index:nat{end_index <= length w}) = 
  forall i . 0 <= i /\ i < end_index ==> key_expansion_specific alg key w i

let lemma_selector255 (selector:nat8) (bits:bits_of_byte) : Lemma
  (requires selector == 255 /\ bits == byte_to_twobits selector)
  (ensures Bits_of_Byte?.lo bits == 3 /\ Bits_of_Byte?.mid_lo == 3 /\
           Bits_of_Byte?.mid_hi == 3 /\ Bits_of_Byte?.hi == 3)
  =
  ()
  
