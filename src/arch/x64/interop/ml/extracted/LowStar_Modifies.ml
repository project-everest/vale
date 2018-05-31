open Prims
type abuffer =
  | ABuffer of unit * Prims.nat * unit 
let (uu___is_ABuffer : abuffer -> Prims.bool) = fun projectee  -> true 
let (__proj__ABuffer__item__region :
  abuffer -> FStar_Monotonic_HyperHeap.rid) =
  fun projectee  ->
    match projectee with | ABuffer (region,addr,buffer) -> region
  
let (__proj__ABuffer__item__addr : abuffer -> Prims.nat) =
  fun projectee  ->
    match projectee with | ABuffer (region,addr,buffer) -> addr
  


type loc' =
  | Loc of unit * unit * unit * unit * unit * unit 
let (uu___is_Loc : loc' -> Prims.bool) = fun projectee  -> true 






type loc = loc'
let (loc_none : loc) = Loc ((), (), (), (), (), ()) 






type ('At,'At','Af1,'Af2) fun_set_equal = unit

type ('As1,'As2) loc_equal = Obj.t












type ('Ab0,'Ab) abuffer_includes = unit
type ('As,'Ab) loc_aux_includes_buffer = unit
type ('As1,'As2) loc_aux_includes = unit











type ('As1,'As2) loc_includes = unit













type ('Ab1,'Ab2) abuffer_disjoint = Obj.t

type ('Al1,'Al2) loc_aux_disjoint = unit





type ('Al1,'Al2) loc_disjoint_region_liveness_tags = unit
type ('Al1,'Al2) loc_disjoint_addrs = unit
type ('Al1,'Al2) loc_disjoint_aux = unit
type ('Al1,'Al2) loc_disjoint' = unit
type ('As1,'As2) loc_disjoint = unit











type ('As,'Ah1,'Ah2) modifies_preserves_mreferences = unit

type ('As,'Ah1,'Ah2) modifies_preserves_buffers = unit

type ('As,'Ah1,'Ah2) modifies_preserves_regions = unit
type ('As,'Ah1,'Ah2) modifies' = unit
type ('As,'Ah1,'Ah2) modifies = unit





























type ('Ah,'Ara) does_not_contain_addr' = unit
type ('Ah,'Ara) does_not_contain_addr = unit













