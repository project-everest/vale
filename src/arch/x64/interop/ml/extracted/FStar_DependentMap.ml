open Prims
type ('Akey,'Avalue) t = {
  mappings: 'Akey -> 'Avalue }
let __proj__Mkt__item__mappings :
  'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> 'Avalue =
  fun projectee  ->
    match projectee with
    | { mappings = __fname__mappings;_} -> __fname__mappings
  
let create : 'Akey 'Avalue . ('Akey -> 'Avalue) -> ('Akey,'Avalue) t =
  fun f  -> { mappings = f } 
let sel : 'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> 'Avalue =
  fun m  -> fun k  -> m.mappings k 

let upd :
  'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> 'Avalue -> ('Akey,'Avalue) t
  =
  fun m  ->
    fun k  ->
      fun v  ->
        { mappings = (fun k'  -> if k' = k then v else m.mappings k') }
  


type ('Akey,'Avalue,'Am1,'Am2) equal = unit


let restrict : 'Akey 'Avalue 'Ap . ('Akey,'Avalue) t -> ('Akey,'Avalue) t =
  fun m  -> { mappings = (m.mappings) } 

type ('Akey1,'Avalue1,'Akey2,'Avalue2,'Ak) concat_value = Obj.t
let concat_mappings :
  'Akey1 'Avalue1 'Akey2 'Avalue2 .
    ('Akey1 -> 'Avalue1) ->
      ('Akey2 -> 'Avalue2) ->
        ('Akey1,'Akey2) FStar_Pervasives.either -> Obj.t
  =
  fun m1  ->
    fun m2  ->
      fun k  ->
        match k with
        | FStar_Pervasives.Inl k1 -> Obj.repr (m1 k1)
        | FStar_Pervasives.Inr k2 -> Obj.repr (m2 k2)
  
let concat :
  'Akey1 'Avalue1 'Akey2 'Avalue2 .
    ('Akey1,'Avalue1) t ->
      ('Akey2,'Avalue2) t ->
        (('Akey1,'Akey2) FStar_Pervasives.either,Obj.t) t
  =
  fun m1  ->
    fun m2  -> { mappings = (concat_mappings m1.mappings m2.mappings) }
  


type ('Akey1,'Avalue1,'Akey2,'Aren,'Ak) rename_value = 'Avalue1
let rename :
  'Akey1 'Avalue1 .
    ('Akey1,'Avalue1) t ->
      unit ->
        (Obj.t -> 'Akey1) ->
          (Obj.t,('Akey1,'Avalue1,Obj.t,unit,unit) rename_value) t
  =
  fun m  ->
    fun key2  -> fun ren  -> { mappings = (fun k2  -> m.mappings (ren k2)) }
  

let map :
  'Akey 'Avalue1 'Avalue2 .
    ('Akey -> 'Avalue1 -> 'Avalue2) ->
      ('Akey,'Avalue1) t -> ('Akey,'Avalue2) t
  = fun f  -> fun m  -> { mappings = (fun k  -> f k (sel m k)) } 

