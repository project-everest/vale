module GF128_i
open Types_s
open GF128_s
open Math.Poly2_s
open Math.Poly2.Bits_s
open Math.Poly2_i
open Math.Poly2.Lemmas_i
open FStar.Seq
open FStar.Mul

val lemma_to_of_quad32 (q:quad32) : Lemma (to_quad32 (of_quad32 q) == q)

val lemma_of_to_quad32 (a:poly) : Lemma
  (requires degree a < 128)
  (ensures of_quad32 (to_quad32 a) == a)

let quad32_shift_left_1 (q:quad32) : quad32 =
  let l = quad32_map (fun (i:nat32) -> ishl i 1) q in
  let r = quad32_map (fun (i:nat32) -> ishr i 31) q in
  let Quad32 r0 r1 r2 r3 = r in
  quad32_xor l (Quad32 0 r0 r1 r2)

let quad32_shift_2_left_1 (qa qb:quad32) : tuple2 quad32 quad32 =
  let la = quad32_map (fun (i:nat32) -> ishl i 1) qa in
  let lb = quad32_map (fun (i:nat32) -> ishl i 1) qb in
  let ra = quad32_map (fun (i:nat32) -> ishr i 31) qa in
  let rb = quad32_map (fun (i:nat32) -> ishr i 31) qb in
  let Quad32 ra0 ra1 ra2 ra3 = ra in
  let Quad32 rb0 rb1 rb2 rb3 = rb in
  let qa' = quad32_xor la (Quad32 0 ra0 ra1 ra2) in
  let qb' = quad32_xor lb (quad32_xor (Quad32 ra3 0 0 0) (Quad32 0 rb0 rb1 rb2)) in
  (qa', qb')

val lemma_shift_left_1 (a:poly) : Lemma
  (requires degree a < 127)
  (ensures to_quad32 (shift a 1) == quad32_shift_left_1 (to_quad32 a))

val lemma_shift_2_left_1 (lo hi:poly) : Lemma
  (requires degree hi < 127 /\ degree lo < 128)
  (ensures (
    let n = monomial 128 in
    let a = hi *. n +. lo in
    let a' = shift a 1 in
    let (lo', hi') = quad32_shift_2_left_1 (to_quad32 lo) (to_quad32 hi) in
    lo' == to_quad32 (a' %. n) /\
    hi' == to_quad32 (a' /. n)
  ))

val lemma_gf128_degree (_:unit) : Lemma
  (ensures
    degree gf128_modulus_low_terms == 7 /\
    degree (monomial 128) == 128 /\
    degree gf128_modulus == 128
  )

// Compute 128-bit multiply in terms of 64-bit multiplies
val lemma_gf128_mul (a b c d:poly) (n:nat) : Lemma
  (ensures (
    let m = monomial n in
    let ab = a *. m +. b in
    let cd = c *. m +. d in
    let ac = a *. c in
    let ad = a *. d in
    let bc = b *. c in
    let bd = b *. d in
    ab *. cd ==
      shift (ac +. bc /. m +. ad /. m) (n + n) +.
      ((bc %. m) *. m +. (ad %. m) *. m +. bd)
  ))

// Compute (a * b) % g, where g = n + h and %. n is easy to compute (e.g. n = x^128)
val lemma_gf128_reduce (a b g n h:poly) : Lemma
  (requires
    degree h >= 0 /\
    degree n > 2 * degree h /\
    degree g == degree n /\
    degree a <= degree n /\
    degree b <= degree n /\
    g == n +. h
  )
  (ensures (
    let d = (a *. b) /. n in
    let dh = d *. h in
    degree ((dh /. n) *. h) <= 2 * degree h /\
    (a *. b) %. g == (dh /. n) *. h +. dh %. n +. (a *. b) %. n
  ))

