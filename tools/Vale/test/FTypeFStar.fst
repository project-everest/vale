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
assume val ff3 (z:int) : Ghost int (requires True) (ensures fun y -> xeq2 10 20 /\ (match z with 3 -> True | _ -> False))
assume val ff4 (_:unit) : Lemma True
// TODO: Ghost returning tuple should be converted to multiple return values

assume val ffreq2 (z:int) : Pure int (requires z > 0) (ensures fun _ -> True)
//assume val ffreq2 (z:int) : Pure int (requires True) (ensures fxeq2)

let natN (n:nat) = x:nat{x < n}
let nat8 = natN 256

type myrec = {r1:int; r2:bool}

assume val buf_typ : Type0
assume val bt32 : buf_typ
assume val bt64 : buf_typ
assume val buf (bt:buf_typ) : Type0
let buf32 : Type0 = buf bt32
let buf64 : Type0 = buf bt64
assume val buf_len (#bt:buf_typ) (b:buf bt):int
