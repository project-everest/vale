open Prims
type 'Aa raise0 =
  | Ret of 'Aa 
let uu___is_Ret : 'Aa . 'Aa raise0 -> Prims.bool = fun projectee  -> true 
let __proj__Ret__item___0 : 'Aa . 'Aa raise0 -> 'Aa =
  fun projectee  -> match projectee with | Ret _0 -> _0 
type 'Aa raise_t = 'Aa raise0
let raise_val : 'Aa . 'Aa -> 'Aa raise_t = fun x  -> Ret x 
let downgrade_val : 'Aa . 'Aa raise_t -> 'Aa =
  fun x  -> match x with | Ret x0 -> x0 