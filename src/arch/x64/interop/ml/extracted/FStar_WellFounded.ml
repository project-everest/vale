open Prims
type ('Aa,'Ar,'Ax) acc =
  | AccIntro of ('Aa -> 'Ar -> ('Aa,'Ar,unit) acc) 
let uu___is_AccIntro : 'Aa 'Ar . 'Aa -> ('Aa,'Ar,unit) acc -> Prims.bool =
  fun x  -> fun projectee  -> true 
let __proj__AccIntro__item___0 :
  'Aa 'Ar . 'Aa -> ('Aa,'Ar,unit) acc -> 'Aa -> 'Ar -> ('Aa,'Ar,unit) acc =
  fun x  -> fun projectee  -> match projectee with | AccIntro _0 -> _0 
type ('Aa,'Ar) well_founded = 'Aa -> ('Aa,'Ar,unit) acc
let acc_inv :
  'Aaa 'Ar .
    'Aaa -> ('Aaa,'Ar,unit) acc -> 'Aaa -> 'Ar -> ('Aaa,'Ar,unit) acc
  = fun x  -> fun a  -> match a with | AccIntro h1 -> h1 

let apply : 'Aa 'Ab . ('Aa -> 'Ab) -> 'Aa -> 'Ab = fun f  -> fun x  -> f x 
let rec fix_F :
  'Aaa 'Ar 'Ap .
    ('Aaa -> ('Aaa -> 'Ar -> 'Ap) -> 'Ap) ->
      'Aaa -> ('Aaa,'Ar,unit) acc -> 'Ap
  =
  fun f  ->
    fun x  -> fun a  -> f x (fun y  -> fun h  -> fix_F f y (acc_inv x a y h))
  
let fix :
  'Aaa 'Ar .
    ('Aaa,'Ar) well_founded ->
      unit -> ('Aaa -> ('Aaa -> 'Ar -> Obj.t) -> Obj.t) -> 'Aaa -> Obj.t
  = fun rwf  -> fun p  -> fun f  -> fun x  -> fix_F f x (rwf x) 