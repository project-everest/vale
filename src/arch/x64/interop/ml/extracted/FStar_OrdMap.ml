open Prims
type ('Aa,'Af) total_order = unit
type 'Aa cmp = 'Aa -> 'Aa -> Prims.bool
type ('Ak,'Av,'Af,'Ad) map_t = 'Ak -> 'Av FStar_Pervasives_Native.option
type ('Ak,'Av,'Af) ordmap =
  | Mk_map of ('Ak,unit) FStar_OrdSet.ordset * ('Ak,'Av,unit,unit) map_t 
let uu___is_Mk_map : 'Ak 'Av . 'Ak cmp -> ('Ak,'Av,unit) ordmap -> Prims.bool
  = fun f  -> fun projectee  -> true 
let __proj__Mk_map__item__d :
  'Ak 'Av .
    'Ak cmp -> ('Ak,'Av,unit) ordmap -> ('Ak,unit) FStar_OrdSet.ordset
  = fun f  -> fun projectee  -> match projectee with | Mk_map (d,m) -> d 
let __proj__Mk_map__item__m :
  'Ak 'Av . 'Ak cmp -> ('Ak,'Av,unit) ordmap -> ('Ak,'Av,unit,unit) map_t =
  fun f  -> fun projectee  -> match projectee with | Mk_map (d,m) -> m 
let empty : 'Ak 'Av . 'Ak cmp -> ('Ak,'Av,unit) ordmap =
  fun f  ->
    let d = FStar_OrdSet.empty f  in
    let g x = FStar_Pervasives_Native.None  in Mk_map (d, g)
  
let const_on :
  'Ak 'Av .
    'Ak cmp -> ('Ak,unit) FStar_OrdSet.ordset -> 'Av -> ('Ak,'Av,unit) ordmap
  =
  fun f  ->
    fun d  ->
      fun x  ->
        let g y =
          if FStar_OrdSet.mem f y d
          then FStar_Pervasives_Native.Some x
          else FStar_Pervasives_Native.None  in
        Mk_map (d, g)
  
let select :
  'Ak 'Av .
    'Ak cmp ->
      'Ak -> ('Ak,'Av,unit) ordmap -> 'Av FStar_Pervasives_Native.option
  = fun f  -> fun x  -> fun m  -> __proj__Mk_map__item__m f m x 
let insert :
  'Aa .
    'Aa cmp ->
      'Aa -> ('Aa,unit) FStar_OrdSet.ordset -> ('Aa,unit) FStar_OrdSet.ordset
  =
  fun f  ->
    fun x  -> fun s  -> FStar_OrdSet.union f (FStar_OrdSet.singleton f x) s
  
let update :
  'Ak 'Av .
    'Ak cmp -> 'Ak -> 'Av -> ('Ak,'Av,unit) ordmap -> ('Ak,'Av,unit) ordmap
  =
  fun f  ->
    fun x  ->
      fun y  ->
        fun m  ->
          let s' = insert f x (__proj__Mk_map__item__d f m)  in
          let g' x' =
            if x' = x
            then FStar_Pervasives_Native.Some y
            else __proj__Mk_map__item__m f m x'  in
          Mk_map (s', g')
  
let contains :
  'Ak 'Av . 'Ak cmp -> 'Ak -> ('Ak,'Av,unit) ordmap -> Prims.bool =
  fun f  ->
    fun x  -> fun m  -> FStar_OrdSet.mem f x (__proj__Mk_map__item__d f m)
  
let dom :
  'Ak 'Av .
    'Ak cmp -> ('Ak,'Av,unit) ordmap -> ('Ak,unit) FStar_OrdSet.ordset
  = fun f  -> fun m  -> __proj__Mk_map__item__d f m 
let remove :
  'Ak 'Av . 'Ak cmp -> 'Ak -> ('Ak,'Av,unit) ordmap -> ('Ak,'Av,unit) ordmap
  =
  fun f  ->
    fun x  ->
      fun m  ->
        let s' = FStar_OrdSet.remove f x (__proj__Mk_map__item__d f m)  in
        let g' x' =
          if x' = x
          then FStar_Pervasives_Native.None
          else __proj__Mk_map__item__m f m x'  in
        Mk_map (s', g')
  
let choose :
  'Ak 'Av .
    'Ak cmp ->
      ('Ak,'Av,unit) ordmap ->
        ('Ak,'Av) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun m  ->
      match FStar_OrdSet.choose f (__proj__Mk_map__item__d f m) with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x ->
          FStar_Pervasives_Native.Some
            (x,
              (FStar_Pervasives_Native.__proj__Some__item__v
                 (__proj__Mk_map__item__m f m x)))
  
let size : 'Ak 'Av . 'Ak cmp -> ('Ak,'Av,unit) ordmap -> Prims.nat =
  fun f  -> fun m  -> FStar_OrdSet.size f (__proj__Mk_map__item__d f m) 
type ('Ak,'Av,'Af,'Am1,'Am2) equal = unit























