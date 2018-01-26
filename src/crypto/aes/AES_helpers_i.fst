module AES_helpers_i

open Types_s
open FStar.Seq
open AES_s
open FStar.Mul

// syntax for seq accesses, s.[index] and s.[index] <- value
unfold
let op_String_Access (#a:Type) (s:seq a) (i:nat{ i < length s}) : Tot a = index s i

unfold
let op_String_Assignment = Seq.upd

let foo (x:int) = x

let rec key_expansion_specific (alg:algorithm) (key:seq nat32 { length key == nk alg})
                               (w:seq nat32) (i:nat{i < length w}) =
    if 0 <= i && i < nk alg then
      w.[i] == key.[i]
    else
      let temp = 
        if i % (nk alg) = 0 then
	  nat32_xor (sub_word (rot_word w.[i-1])) (aes_rcon ((i / (nk alg)) - 1))
	else if nk alg > 6 && i % (nk alg) = 4 then
	  sub_word w.[i-1]
	else
	  w.[i-1]
      in 
      w.[i] == nat32_xor w.[i - (nk alg)] temp


let key_expansion_partial (alg:algorithm) (key:seq nat32 { length key == nk alg}) 
                          (w:seq nat32) (end_index:nat{end_index <= length w}) = 
  forall i . 0 <= i /\ i < end_index ==> key_expansion_specific alg key w i

let lemma_selector255 (selector:nat8) (bits:bits_of_byte) : Lemma
  (requires selector == 255 /\ bits == byte_to_twobits selector)
  (ensures Bits_of_Byte?.lo bits == 3 /\ Bits_of_Byte?.mid_lo bits == 3 /\
           Bits_of_Byte?.mid_hi bits == 3 /\ Bits_of_Byte?.hi bits == 3)
  =
  ()

let lemma_KeyExpansionRoundHelper (alg:algorithm) (key:seq nat32 { length key == nk alg})
                                  (w_init w_final:seq nat32) (completed_bytes:int)
                                  (xmm1_v0 xmm2_v1 xmm2_v2 xmm3_v3 xmm1_v4 xmm3_v5 xmm1_v6 xmm3_v7 xmm1_v8 xmm1_v9 : quad32) 
                                  : Lemma
  (requires 4 <= completed_bytes /\ completed_bytes <= 40 /\
            alg == AES_128 /\
            length w_init == 44 /\ length w_init == nb * (nr alg + 1) /\
            key_expansion_partial alg key w_init completed_bytes /\
            completed_bytes % 4 == 0 /\
            length w_final == length w_init /\
            xmm1_v0 == Quad32 w_final.[completed_bytes-4] 
                              w_final.[completed_bytes-3] 
                              w_final.[completed_bytes-2]
                              w_final.[completed_bytes-1] /\

            (let rcon = aes_rcon((completed_bytes / nk(alg)) - 1) in

            xmm2_v1 == Quad32 (sub_word xmm1_v0.mid_lo) (nat32_xor (rot_word (sub_word xmm1_v0.mid_lo)) rcon) (sub_word xmm1_v0.hi) (nat32_xor (rot_word (sub_word xmm1_v0.hi)) rcon)) /\

            (let bits = byte_to_twobits 255 in
            xmm2_v2 == Quad32 (select_word xmm2_v1 (Bits_of_Byte?.lo bits)) 
                              (select_word xmm2_v1 (Bits_of_Byte?.mid_lo bits))
                              (select_word xmm2_v1 (Bits_of_Byte?.mid_hi bits))
                              (select_word xmm2_v1 (Bits_of_Byte?.hi bits))) /\
            xmm3_v3 == Quad32 0 xmm1_v0.lo xmm1_v0.mid_lo xmm1_v0.mid_hi /\
            xmm1_v4 == quad32_xor xmm1_v0 xmm3_v3 /\
            xmm3_v5 == Quad32 0 xmm1_v4.lo xmm1_v4.mid_lo xmm1_v4.mid_hi /\
            xmm1_v6 == quad32_xor xmm1_v4 xmm3_v5 /\
            xmm3_v7 == Quad32 0 xmm1_v6.lo xmm1_v6.mid_lo xmm1_v6.mid_hi /\
            xmm1_v8 == quad32_xor xmm1_v6 xmm3_v7 /\
            xmm1_v9 == quad32_xor xmm1_v8 xmm2_v2 /\
            
            (w_final == (let w = w_init.[completed_bytes]     <- xmm1_v9.lo in
                         let w =      w.[completed_bytes + 1] <- xmm1_v9.mid_lo in
                         let w =      w.[completed_bytes + 2] <- xmm1_v9.mid_hi in
                         let w =      w.[completed_bytes + 3] <- xmm1_v9.hi in
                         w)))
  (ensures (key_expansion_partial alg key w_final (completed_bytes + 4)))
  =                               
  admit();
  ()

(*
{
    var important_value := BitwiseXor(RotWord(SubWord(w_init[completedBytes-1])), AES_Rcon()[ (completedBytes / Nk(alg))-1 ]);
    var bits := byte_to_bits(255);
    lemma_Selector255(255, bits);
    calc {
        xmm2_v2.mid_lo;
        select_word(xmm2_v1, bits.mid_lo);
        xmm2_v1.hi;
        important_value;
    }
    calc {
        xmm2_v2.mid_hi;
        select_word(xmm2_v1, bits.mid_hi);
        xmm2_v1.hi;
        important_value;
    }
    lemma_BitwiseXorWithZero(w[completedBytes-4]);
    lemma_BitwiseXorCommutative(w[completedBytes-3], w[completedBytes-4]);
    lemma_double_xor_negates(w[completedBytes-4], w[completedBytes-3], 0);
    lemma_BitwiseXorCommutative(w[completedBytes-2], w[completedBytes-3]);
    lemma_double_xor_negates(w[completedBytes-3], w[completedBytes-2], w[completedBytes-4]);
    calc {
        BitwiseXor(BitwiseXor(w[completedBytes-1], w[completedBytes-2]), BitwiseXor(w[completedBytes-2], w[completedBytes-3]));
            { lemma_BitwiseXorCommutative(w[completedBytes-1], w[completedBytes-2]); }
        BitwiseXor(BitwiseXor(w[completedBytes-2], w[completedBytes-1]), BitwiseXor(w[completedBytes-2], w[completedBytes-3]));
            { lemma_double_xor_negates(w[completedBytes-2], w[completedBytes-1], w[completedBytes-3]); }
        BitwiseXor(w[completedBytes-1], w[completedBytes-3]);
            { lemma_BitwiseXorCommutative(w[completedBytes-1], w[completedBytes-3]); }
        BitwiseXor(w[completedBytes-3], w[completedBytes-1]);
    }
    calc {
        BitwiseXor(BitwiseXor(w[completedBytes-2], w[completedBytes-4]), w[completedBytes-3]);
            { lemma_BitwiseXorAssociative(w[completedBytes-2], w[completedBytes-4], w[completedBytes-3]); }
        BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3]));
    }
    calc {
        BitwiseXor(BitwiseXor(w[completedBytes-3], w[completedBytes-1]), BitwiseXor(w[completedBytes-2], w[completedBytes-4]));
            { lemma_BitwiseXorCommutative(w[completedBytes-3], w[completedBytes-1]); }
        BitwiseXor(BitwiseXor(w[completedBytes-1], w[completedBytes-3]), BitwiseXor(w[completedBytes-2], w[completedBytes-4]));
            { lemma_BitwiseXorAssociative2(w[completedBytes-1], w[completedBytes-3], w[completedBytes-2], w[completedBytes-4]); }
        BitwiseXor(BitwiseXor(w[completedBytes-1], w[completedBytes-2]), BitwiseXor(w[completedBytes-3], w[completedBytes-4]));
        BitwiseXor(BitwiseXor(w[completedBytes-1], w[completedBytes-2]), BitwiseXor(w[completedBytes-4], w[completedBytes-3]));
            { lemma_BitwiseXorAssociative(w[completedBytes-1], w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3])); }
        BitwiseXor(w[completedBytes-1], BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3])));
    }
    lemma_KeyExpansionRoundHelperHelper(key, alg, w_init, completedBytes, xmm1_v9, important_value, w);
}
*)
