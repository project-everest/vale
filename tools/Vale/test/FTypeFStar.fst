module FTypeFStar

let byte = i:int{0 <= i /\ i < 0x100}
let nat32 = i:int{0 <= i /\ i < 0x100000000}
let id x = x
//TODO?: let list = Prims.list
//TODO: let list a = Prims.list a
//type list (a:Type0) : Type0 = | Nil : list a | Cons : a -> list a -> list a
let nil = Nil
let cons = Cons
