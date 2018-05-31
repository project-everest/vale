open Prims
let rec map2 :
  'Aa1 'Aa2 'Ab .
    ('Aa1 -> 'Aa2 -> 'Ab) ->
      'Aa1 Prims.list -> 'Aa2 Prims.list -> 'Ab Prims.list
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        match (l1, l2) with
        | ([],[]) -> []
        | (x1::xs1,x2::xs2) -> (f x1 x2) :: (map2 f xs1 xs2)
  
let rec map3 :
  'Aa1 'Aa2 'Aa3 'Ab .
    ('Aa1 -> 'Aa2 -> 'Aa3 -> 'Ab) ->
      'Aa1 Prims.list -> 'Aa2 Prims.list -> 'Aa3 Prims.list -> 'Ab Prims.list
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        fun l3  ->
          match (l1, l2, l3) with
          | ([],[],[]) -> []
          | (x1::xs1,x2::xs2,x3::xs3) -> (f x1 x2 x3) :: (map3 f xs1 xs2 xs3)
  
let zip :
  'Aa1 'Aa2 .
    'Aa1 Prims.list ->
      'Aa2 Prims.list ->
        ('Aa1,'Aa2) FStar_Pervasives_Native.tuple2 Prims.list
  = fun l1  -> fun l2  -> map2 (fun x  -> fun y  -> (x, y)) l1 l2 
let zip3 :
  'Aa1 'Aa2 'Aa3 .
    'Aa1 Prims.list ->
      'Aa2 Prims.list ->
        'Aa3 Prims.list ->
          ('Aa1,'Aa2,'Aa3) FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun l1  ->
    fun l2  ->
      fun l3  -> map3 (fun x  -> fun y  -> fun z  -> (x, y, z)) l1 l2 l3
  