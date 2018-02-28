module Math.Poly2_s
open FStar.Seq

let poly = D.poly
let degree p = D.degree p
let zero = D.zero
let one = D.one
let monomial n = D.monomial n
let shift p n = D.shift p n
let poly_index p n = D.poly_index p n
let of_seq s = D.of_seq s
let of_fun len f = D.of_fun len f
let add a b = D.add a b
let mul a b = D.mul a b
let div a b = zero // TODO
let mod a b = zero // TODO
let reveal_defs () = ()
