open Prims
type ('Aa,'Ab) rel =
  | R of 'Aa * 'Ab 
let uu___is_R : 'Aa 'Ab . ('Aa,'Ab) rel -> Prims.bool =
  fun projectee  -> true 
let __proj__R__item__l : 'Aa 'Ab . ('Aa,'Ab) rel -> 'Aa =
  fun projectee  -> match projectee with | R (l,r) -> l 
let __proj__R__item__r : 'Aa 'Ab . ('Aa,'Ab) rel -> 'Ab =
  fun projectee  -> match projectee with | R (l,r) -> r 
type 'At double = ('At,'At) rel
type 'At eq = 'At double
let twice : 'Auu____121 . 'Auu____121 -> ('Auu____121,'Auu____121) rel =
  fun x  -> R (x, x) 
let (tu : (unit,unit) rel) = twice () 
let rel_map1T : 'a 'b . ('a -> 'b) -> 'a double -> 'b double =
  fun f  ->
    fun uu____171  -> match uu____171 with | R (x1,x2) -> R ((f x1), (f x2))
  
let rel_map2Teq :
  'Aa 'Ab 'Ac . ('Aa -> 'Ab -> 'Ac) -> 'Aa double -> 'Ab double -> 'Ac double
  =
  fun f  ->
    fun uu____241  ->
      fun uu____242  ->
        match (uu____241, uu____242) with
        | (R (x1,x2),R (y1,y2)) -> R ((f x1 y1), (f x2 y2))
  
let rel_map2T :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a double -> 'b double -> 'c double =
  fun f  ->
    fun uu____343  ->
      fun uu____344  ->
        match (uu____343, uu____344) with
        | (R (x1,x2),R (y1,y2)) -> R ((f x1 y1), (f x2 y2))
  

let rel_map3T :
  'a 'b 'c 'd .
    ('a -> 'b -> 'c -> 'd) ->
      'a double -> 'b double -> 'c double -> 'd double
  =
  fun f  ->
    fun uu____475  ->
      fun uu____476  ->
        fun uu____477  ->
          match (uu____475, uu____476, uu____477) with
          | (R (x1,x2),R (y1,y2),R (z1,z2)) -> R ((f x1 y1 z1), (f x2 y2 z2))
  

let (op_Hat_Plus : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x  -> fun y  -> x + y) 
let (op_Hat_Minus : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x  -> fun y  -> x - y) 
let (op_Hat_Star : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x  -> fun y  -> x * y) 
let (op_Hat_Slash :
  Prims.int double -> Prims.nonzero double -> Prims.int double) =
  rel_map2T (fun x  -> fun y  -> x / y) 
let tl_rel : 'Aa . 'Aa Prims.list double -> 'Aa Prims.list double =
  fun uu____687  ->
    match uu____687 with | R (uu____694::xs,uu____696::ys) -> R (xs, ys)
  
let cons_rel :
  'Auu____728 'Auu____729 .
    ('Auu____728,'Auu____729) rel ->
      ('Auu____728 Prims.list,'Auu____729 Prims.list) rel ->
        ('Auu____728 Prims.list,'Auu____729 Prims.list) rel
  =
  fun uu____758  ->
    fun uu____759  ->
      match (uu____758, uu____759) with
      | (R (x,y),R (xs,ys)) -> R ((x :: xs), (y :: ys))
  
let pair_rel :
  'Auu____836 'Auu____837 'Auu____838 'Auu____839 .
    ('Auu____836,'Auu____837) rel ->
      ('Auu____838,'Auu____839) rel ->
        (('Auu____836,'Auu____838) FStar_Pervasives_Native.tuple2,('Auu____837,
                                                                    'Auu____839)
                                                                    FStar_Pervasives_Native.tuple2)
          rel
  =
  fun uu____868  ->
    fun uu____869  ->
      match (uu____868, uu____869) with
      | (R (a,b),R (c,d)) -> R ((a, c), (b, d))
  
let triple_rel :
  'Auu____942 'Auu____943 'Auu____944 'Auu____945 'Auu____946 'Auu____947 .
    ('Auu____942,'Auu____943) rel ->
      ('Auu____944,'Auu____945) rel ->
        ('Auu____946,'Auu____947) rel ->
          (('Auu____942,'Auu____944,'Auu____946)
             FStar_Pervasives_Native.tuple3,('Auu____943,'Auu____945,
                                              'Auu____947)
                                              FStar_Pervasives_Native.tuple3)
            rel
  =
  fun uu____988  ->
    fun uu____989  ->
      fun uu____990  ->
        match (uu____988, uu____989, uu____990) with
        | (R (a,b),R (c,d),R (e,f)) -> R ((a, c, e), (b, d, f))
  
let fst_rel :
  'Auu____1056 'Auu____1057 .
    unit ->
      ('Auu____1056,'Auu____1057) FStar_Pervasives_Native.tuple2 double ->
        'Auu____1056 double
  = fun uu____1070  -> rel_map1T FStar_Pervasives_Native.fst 
let snd_rel :
  'Auu____1086 'Auu____1087 .
    unit ->
      ('Auu____1086,'Auu____1087) FStar_Pervasives_Native.tuple2 double ->
        'Auu____1087 double
  = fun uu____1100  -> rel_map1T FStar_Pervasives_Native.snd 
let (and_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2T (fun x  -> fun y  -> x && y) 
let (or_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2T (fun x  -> fun y  -> x || y) 
let (eq_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2Teq (fun x  -> fun y  -> x = y) 
let (and_irel : (Prims.bool,Prims.bool) rel -> Prims.bool) =
  fun uu____1188  -> match uu____1188 with | R (a,b) -> a && b 
let (or_irel : (Prims.bool,Prims.bool) rel -> Prims.bool) =
  fun uu____1206  -> match uu____1206 with | R (a,b) -> a || b 
let eq_irel : 'At . ('At,'At) rel -> Prims.bool =
  fun x  -> match x with | R (a,b) -> a = b 
