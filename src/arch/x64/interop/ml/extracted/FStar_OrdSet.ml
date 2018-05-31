open Prims
type ('Aa,'Af) total_order = unit
type 'Aa cmp = 'Aa -> 'Aa -> Prims.bool
let rec sorted : 'Aa . 'Aa cmp -> 'Aa Prims.list -> Prims.bool =
  fun f  ->
    fun l  ->
      match l with
      | [] -> true
      | x::[] -> true
      | x::y::tl1 -> ((f x y) && (x <> y)) && (sorted f (y :: tl1))
  
type ('Aa,'Af) ordset = 'Aa Prims.list

let as_list : 'Aa . 'Aa cmp -> ('Aa,unit) ordset -> 'Aa Prims.list =
  fun f  -> fun s  -> s 
let mem : 'Aa . 'Aa cmp -> 'Aa -> ('Aa,unit) ordset -> Prims.bool =
  fun f  -> fun x  -> fun s  -> FStar_List_Tot_Base.mem x s 


let empty : 'Aa . 'Aa cmp -> ('Aa,unit) ordset = fun f  -> [] 
let rec insert' :
  'Aa . 'Aa cmp -> 'Aa -> ('Aa,unit) ordset -> ('Aa,unit) ordset =
  fun f  ->
    fun x  ->
      fun s  ->
        match s with
        | [] -> [x]
        | hd1::tl1 ->
            if x = hd1
            then hd1 :: tl1
            else
              if f x hd1 then x :: hd1 :: tl1 else hd1 :: (insert' f x tl1)
  
let rec union :
  'Aa .
    'Aa cmp -> ('Aa,unit) ordset -> ('Aa,unit) ordset -> ('Aa,unit) ordset
  =
  fun f  ->
    fun s1  ->
      fun s2  ->
        match s1 with | [] -> s2 | hd1::tl1 -> union f tl1 (insert' f hd1 s2)
  
let rec intersect :
  'Aa .
    'Aa cmp -> ('Aa,unit) ordset -> ('Aa,unit) ordset -> ('Aa,unit) ordset
  =
  fun f  ->
    fun s1  ->
      fun s2  ->
        match s1 with
        | [] -> []
        | hd1::tl1 ->
            if mem f hd1 s2
            then insert' f hd1 (intersect f tl1 s2)
            else intersect f tl1 s2
  
let choose :
  'Aa . 'Aa cmp -> ('Aa,unit) ordset -> 'Aa FStar_Pervasives_Native.option =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | x::uu____5555 -> FStar_Pervasives_Native.Some x
  
let rec remove' :
  'Aa . 'Aa cmp -> 'Aa -> ('Aa,unit) ordset -> ('Aa,unit) ordset =
  fun f  ->
    fun x  ->
      fun s  ->
        match s with
        | [] -> []
        | hd1::tl1 -> if x = hd1 then tl1 else hd1 :: (remove' f x tl1)
  
let remove : 'Aa . 'Aa cmp -> 'Aa -> ('Aa,unit) ordset -> ('Aa,unit) ordset =
  fun f  -> fun x  -> fun s  -> remove' f x s 
let size : 'Aa . 'Aa cmp -> ('Aa,unit) ordset -> Prims.nat =
  fun f  -> fun s  -> FStar_List_Tot_Base.length s 
let rec subset :
  'Aa . 'Aa cmp -> ('Aa,unit) ordset -> ('Aa,unit) ordset -> Prims.bool =
  fun f  ->
    fun s1  ->
      fun s2  ->
        match (s1, s2) with
        | ([],uu____8238) -> true
        | (hd1::tl1,hd'::tl') ->
            if (f hd1 hd') && (hd1 = hd')
            then subset f tl1 tl'
            else
              if (f hd1 hd') && (Prims.op_Negation (hd1 = hd'))
              then false
              else subset f s1 tl'
        | (uu____8716,uu____8717) -> false
  
let singleton : 'Aa . 'Aa cmp -> 'Aa -> ('Aa,unit) ordset =
  fun f  -> fun x  -> [x] 
type ('Aa,'Af,'As1,'As2) equal = unit


















let rec fold :
  'Aa 'Aacc .
    'Aa cmp -> ('Aacc -> 'Aa -> 'Aacc) -> 'Aacc -> ('Aa,unit) ordset -> 'Aacc
  =
  fun f  ->
    fun g  -> fun init1  -> fun s  -> FStar_List_Tot_Base.fold_left g init1 s
  
let rec map_internal :
  'Aa 'Ab .
    'Aa cmp ->
      'Ab cmp -> ('Aa -> 'Ab) -> ('Aa,unit) ordset -> ('Ab,unit) ordset
  =
  fun fa  ->
    fun fb  ->
      fun g  ->
        fun sa  ->
          match sa with
          | [] -> []
          | x::xs ->
              let y = g x  in
              let ys = map_internal fa fb g xs  in
              if
                (Prims.op_Negation (Prims.uu___is_Cons ys)) ||
                  ((Prims.__proj__Cons__item__hd ys) <> y)
              then y :: ys
              else ys
  
let map :
  'Aa 'Ab .
    'Aa cmp ->
      'Ab cmp -> ('Aa -> 'Ab) -> ('Aa,unit) ordset -> ('Ab,unit) ordset
  = fun fa  -> fun fb  -> fun g  -> fun sa  -> map_internal fa fb g sa 
let rec remove_le :
  'Aa . 'Aa cmp -> 'Aa -> ('Aa,unit) ordset -> ('Aa,unit) ordset =
  fun f  ->
    fun x  ->
      fun s  ->
        match s with
        | [] -> []
        | y::ys -> if (f x y) && (x <> y) then s else remove_le f x ys
  
let rec minus' :
  'Aa .
    'Aa cmp ->
      'Aa -> ('Aa,unit) ordset -> ('Aa,unit) ordset -> ('Aa,unit) ordset
  =
  fun f  ->
    fun x  ->
      fun s1  ->
        fun s2  ->
          match s1 with
          | [] -> []
          | x1::xs1 ->
              (match s2 with
               | [] -> s1
               | x2::xs2 ->
                   if x1 = x2
                   then minus' f x xs1 xs2
                   else x1 :: (minus' f x1 xs1 (remove_le f x1 s2)))
  
let minus :
  'Aa .
    'Aa cmp -> ('Aa,unit) ordset -> ('Aa,unit) ordset -> ('Aa,unit) ordset
  =
  fun f  ->
    fun s1  ->
      fun s2  ->
        match s1 with
        | [] -> []
        | x1::xs1 -> minus' f x1 xs1 (remove_le f x1 s2)
  
let strict_subset :
  'Aa . 'Aa cmp -> ('Aa,unit) ordset -> ('Aa,unit) ordset -> Prims.bool =
  fun f  -> fun s1  -> fun s2  -> (s1 <> s2) && (subset f s1 s2) 









let rec as_set : 'Aa . 'Aa cmp -> ('Aa,unit) ordset -> 'Aa FStar_Set.set =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Set.empty
      | hd1::tl1 -> FStar_Set.union (FStar_Set.singleton hd1) (as_set f tl1)
  

