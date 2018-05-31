open Prims























let rec rev' : 'a . 'a Prims.list -> 'a Prims.list =
  fun uu___51_238  ->
    match uu___51_238 with
    | [] -> []
    | hd1::tl1 -> FStar_List_Tot_Base.op_At (rev' tl1) [hd1]
  
let rev'T :
  'Auu____251 . unit -> 'Auu____251 Prims.list -> 'Auu____251 Prims.list =
  fun uu____259  -> rev' 















let rec sorted : 'a . ('a -> 'a -> Prims.bool) -> 'a Prims.list -> Prims.bool
  =
  fun f  ->
    fun uu___54_445  ->
      match uu___54_445 with
      | [] -> true
      | uu____452::[] -> true
      | x::y::tl1 -> (f x y) && (sorted f (y :: tl1))
  
type ('Aa,'Af) total_order = unit









































