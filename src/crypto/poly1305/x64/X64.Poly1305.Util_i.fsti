module X64.Poly1305.Util_i

open FStar.Mul
open Opaque_s
open Poly1305.Spec_s
open X64.Machine_s
open X64.Poly1305.Math_i
open X64.Vale.Decls_i
open Opaque_s
open X64.Memory_i

// Note, we need the len parameter, as using buffer_length pushes everything into ghost, including Poly1305 spec
let heapletTo128 (s:Seq.seq nat64) (len:nat{ len % 2 == 0 /\ len <= Seq.length s}) : int->nat128 =
  fun index -> if 0 <= index && index < len / 2 then 
               (Seq.index s (2*index)) + 0x10000000000000000 * (Seq.index s (2*index + 1)) 
            else 42

let applyHeapletTo128 (s:Seq.seq nat64) (len:nat{ len % 2 == 0 /\ len <= Seq.length s}) (index:int) : nat128 =
  heapletTo128 s len index 

let rec poly1305_heap_blocks' (h:int) (pad:int) (r:int) (s:Seq.seq nat64)
        (k:int{0 <= k /\ k <= Seq.length s /\ k % 2 == 0})
        : Tot int (decreases k)
    =
    if k = 0 then h
    else
        let kk = k - 2 in
	//assert (i >= 0 ==> precedes (kk - i) (k-i));
	//assert (i < 0 ==> precedes (kk - i) (k-i));
	let hh = poly1305_heap_blocks' h pad r s kk in
        modp((hh + pad + pow2_64 * (Seq.index s (kk + 1)) + (Seq.index s kk)) * r)

val poly1305_heap_blocks (h:int) (pad:int) (r:int) (s:Seq.seq nat64) (k:int) : int

val reveal_poly1305_heap_blocks (h:int) (pad:int) (r:int) (s:Seq.seq nat64) (k:int) : Lemma
  (requires 0 <= k /\ k <= Seq.length s /\ k % 2 == 0)
  (ensures poly1305_heap_blocks h pad r s k = poly1305_heap_blocks' h pad r s k)

val lemma_poly1305_heap_hash_blocks (h:int) (pad:int) (r:int)  (m:mem) (b:buffer64) // { buffer_length b % 2 == 0 }) 
        (len:nat{ len % 2 == 0 /\ len <= buffer_length b})
        (k:int{0 <= k /\ k <= buffer_length b /\ k % 2 == 0}) : Lemma
  (requires True)
//i <= k && k <= i + len /\
 //           (k - i) % 16 == 0 /\
 //           validSrcAddrs m i  64 ((len + 15) / 16 * 16))
           // (forall j . i <= j /\ j < i + (len + 15) / 16 * 16 && (j - i) % 8 = 0 ==> m `Map.contains` j))
  (ensures poly1305_heap_blocks h pad r (buffer64_as_seq m b) k == poly1305_hash_blocks h pad r (heapletTo128 (buffer64_as_seq m b) len) k)

type t_seqTo128 = int -> nat128
let seqTo128 (s:Seq.seq nat64) : t_seqTo128 =
  let f (i:int) : nat128 =
    let open FStar.Mul in
    if 0 <= i && i < Seq.length s / 2 then
      (Seq.index s (2 * i)) + 0x10000000000000000 * (Seq.index s (2 * i + 1))
    else
      42
  in f

let lemma_poly1305_heap_hash_blocks_alt (h:int) (pad:int) (r:int) (m:mem) (b:buffer64) (n:int) : Lemma
  (requires 0 <= n /\ n + n <= buffer_length b /\ n + n <= Seq.length (buffer64_as_seq m b))
  (ensures
    ((n + n) % 2) == 0 /\ // REVIEW
    poly1305_heap_blocks h pad r (buffer64_as_seq m b) (n + n) ==
    poly1305_hash_blocks h pad r (seqTo128 (buffer64_as_seq m b)) n)
  =
  assume False

let rec buffers_readable (h: mem) (l: list buffer64) : GTot Type0 (decreases l) =
match l with
| [] -> True
| b :: l'  -> buffer_readable h b /\ buffers_readable h l'

unfold let modifies_buffer (b:buffer64) (h1 h2:mem) = modifies_mem (loc_buffer b) h1 h2

let validSrcAddrs64 (m:mem) (addr:int) (b:buffer64) (len:int) =
    buffer_readable m b /\
    len <= buffer_length b /\
    buffer_addr b m == addr

let modifies_buffer_specific (b:buffer64) (h1 h2:mem) (start last:nat) : GTot Type0 =
    modifies_buffer b h1 h2 /\
    // TODO: Consider replacing this with: modifies (loc_buffer (gsub_buffer b i len)) h1 h2
    (forall (i:nat) . {:pattern (Seq.index (buffer_as_seq h2 b) i)}
                        0 <= i /\ i < buffer_length b 
                     /\ (i < start || i > last) 
                    ==> buffer64_read b i h1
                     == buffer64_read b i h2)

unfold let buffers_disjoint (b1 b2:buffer64) =
    locs_disjoint [loc_buffer b1; loc_buffer b2]

let readable_words (len:nat) =
    ((len + 15) / 16) `op_Multiply` 2 // 2 == 16 for rounding /8 for 8-byte words
