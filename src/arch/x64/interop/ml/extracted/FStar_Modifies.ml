open Prims
type loc_aux =
  | LocBuffer of unit * Obj.t FStar_Buffer.buffer 
  | LocUnion of loc_aux * loc_aux 
let (uu___is_LocBuffer : loc_aux -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocBuffer (t,b) -> true | uu____37 -> false
  
type 'Aprojectee __proj__LocBuffer__item__t = Obj.t
let (__proj__LocBuffer__item__b : loc_aux -> Obj.t FStar_Buffer.buffer) =
  fun projectee  -> match projectee with | LocBuffer (t,b) -> b 
let (uu___is_LocUnion : loc_aux -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocUnion (l1,l2) -> true | uu____106 -> false
  
let (__proj__LocUnion__item__l1 : loc_aux -> loc_aux) =
  fun projectee  -> match projectee with | LocUnion (l1,l2) -> l1 
let (__proj__LocUnion__item__l2 : loc_aux -> loc_aux) =
  fun projectee  -> match projectee with | LocUnion (l1,l2) -> l2 

type loc' =
  | Loc of unit * unit * unit * unit 
let (uu___is_Loc : loc' -> Prims.bool) = fun projectee  -> true 




type loc = loc'
let (loc_none : loc) = Loc ((), (), (), ()) 

























type ('As1,'As2) loc_includes = unit






















type ('Al1,'Al2) loc_disjoint' = unit
type ('As1,'As2) loc_disjoint = unit












type ('As,'Ah1,'Ah2) modifies_preserves_mreferences = unit
type ('As,'Ah1,'Ah2) modifies_preserves_buffers = unit
type ('As,'Ah1,'Ah2) modifies' = unit
type ('As,'Ah1,'Ah2) modifies = unit

































type ('Ah,'Ara) does_not_contain_addr' = unit
type ('Ah,'Ara) does_not_contain_addr = unit













