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

let quad32_shift_left_1 (q:quad32) =
  let Quad32 q0 q1 q2 q3 = q in
  let l0 = ishl q0 1 in
  let l1 = ishl q1 1 in
  let l2 = ishl q2 1 in
  let l3 = ishl q3 1 in
  let r0 = ishr q0 31 in
  let r1 = ishr q1 31 in
  let r2 = ishr q2 31 in
  let r3 = ishr q3 31 in
  let x0 = ixor l0 0 in
  let x1 = ixor l1 r0 in
  let x2 = ixor l2 r1 in
  let x3 = ixor l3 r2 in
  Quad32 x0 x1 x2 x3

val lemma_shift_left_1 (a:poly) : Lemma
  (requires degree a < 127)
  (ensures to_quad32 (shift a 1) == quad32_shift_left_1 (to_quad32 a))

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

