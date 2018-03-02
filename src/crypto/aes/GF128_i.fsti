module GF128_i
open GF128_s
open Math.Poly2_s
open Math.Poly2_i
open Math.Poly2.Lemmas_i
open FStar.Seq
open FStar.Mul

val lemma_gf128_degree (_:unit) : Lemma
  (ensures
    degree gf128_modulus_low_terms == 7 /\
    degree (monomial 128) == 128 /\
    degree gf128_modulus == 128
  )

// Compute 128-bit multiply in terms of 64-bit multiplies
val lemma_gf128_mul (a b c d n:poly) : Lemma
  (requires degree n >= 0)
  (ensures (
    let ab = a *. n +. b in
    let cd = c *. n +. d in
    let ac = a *. c in
    let ad = a *. d in
    let bc = b *. c in
    let bd = b *. d in
    ab *. cd ==
      ((ac /. n) *. n +. (ac %. n +. bc /. n +. ad /. n)) *. (n *. n) +.
      ((bc %. n +. ad %. n +. bd /. n) *. n +. bd %. n)
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

