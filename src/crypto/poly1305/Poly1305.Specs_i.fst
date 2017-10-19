module X64.Poly1305.Spec_Refinement_i

open X64.Poly1305.Spec_s
open Spec.Poly1305

open FStar.Math.Lib
open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness
open Spec.Poly1305.Lemmas

let bytes_to_nat128 (b:bytes) : (int -> nat128) =
  fun offset -> 
    let b_start = offset * 16 in
    let b_end = min (b_start + 16) (length b) in
    if 0 <= b_start && b_start < length b then
      little_endian (slice b b_start b_end)
    else
      42

let lemma_encode_bytes_to_nat128 (b:bytes) (n:nat {n < length (encode_bytes b)} ) : Lemma
  (requires True)
  (ensures (let inverse_offset:nat = length (encode_bytes b) - n - 1 in
            let bytes_subset = index (encode_bytes b) inverse_offset in
            bytes_to_nat128 b n = little_endian bytes_subset))
  =
  admit()

let lemma_refinement (msg:bytes) (k:key) : Lemma
  (requires True)
  (ensures little_endian (poly1305 msg k) == 
           poly1305_hash (little_endian (slice k  0 16)) 
                         (little_endian (slice k 16 32))
                         (bytes_to_nat128 msg)
                         0 // start
                         (Seq.length msg))
  =
  admit()
                        
