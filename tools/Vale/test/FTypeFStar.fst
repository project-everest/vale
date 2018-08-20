module FTypeFStar

let byte = i:int{0 <= i /\ i < 0x100}
let nat32 = i:int{0 <= i /\ i < 0x100000000}
let id x = x
//TODO?: let list = Prims.list
//TODO: let list a = Prims.list a
//type list (a:Type0) : Type0 = | Nil : list a | Cons : a -> list a -> list a
let nil = Nil
let cons = Cons

assume val xeq2 (#a:Type) (x:a) (y:a) : prop
assume val ff1 (z:int) : Lemma (xeq2 10 20 /\ (match z with 3 -> True | _ -> False))
assume val ff2 (z:int) : Pure int (requires True) (ensures fun _ -> xeq2 10 20 /\ (match z with 3 -> True | _ -> False))

let natN (n:nat) = x:nat{x < n}
let nat8 = natN 256

type myrec = {r1:int; r2:bool}
