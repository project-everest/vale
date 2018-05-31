open Prims
let (is_in :
  FStar_Monotonic_HyperHeap.rid ->
    FStar_Monotonic_HyperHeap.hmap -> Prims.bool)
  = fun r  -> fun h  -> FStar_Map.contains h r 

let (is_eternal_color : Prims.int -> Prims.bool) =
  fun c  -> c <= (Prims.parse_int "0") 

type sid = unit





type 'Am map_invariant_predicate = unit
type 'Am map_invariant = unit
type 'Ah downward_closed_predicate = unit
type 'Ah downward_closed = unit
type ('Atip,'Ah) tip_top_predicate = unit
type ('Atip,'Ah) tip_top = unit
type ('Atip,'Ah) is_tip = unit

type ('Ah,'An) rid_ctr_pred_predicate = unit
type ('Ah,'An) rid_ctr_pred = unit
type ('Ah,'Actr,'Atip) is_wf_with_ctr_and_tip = unit
type mem =
  | HS of Prims.int * FStar_Monotonic_HyperHeap.hmap * unit 
let (uu___is_HS : mem -> Prims.bool) = fun projectee  -> true 
let (__proj__HS__item__rid_ctr : mem -> Prims.int) =
  fun projectee  -> match projectee with | HS (rid_ctr,h,tip) -> rid_ctr 
let (__proj__HS__item__h : mem -> FStar_Monotonic_HyperHeap.hmap) =
  fun projectee  -> match projectee with | HS (rid_ctr,h,tip) -> h 
let (__proj__HS__item__tip : mem -> FStar_Monotonic_HyperHeap.rid) =
  fun projectee  -> match projectee with | HS (rid_ctr,h,tip) -> tip 







let (empty_mem : FStar_Monotonic_HyperHeap.hmap -> mem) =
  fun m  ->
    let empty_map = FStar_Map.restrict FStar_Set.empty m  in
    let h = FStar_Map.upd empty_map () FStar_Monotonic_Heap.emp  in
    let tip = ()  in HS ((Prims.parse_int "1"), h, ())
  

let (poppable : mem -> Prims.bool) =
  fun m  -> (__proj__HS__item__tip m) <> () 
let remove_elt : 'Aa . 'Aa FStar_Set.set -> 'Aa -> 'Aa FStar_Set.set =
  fun s  ->
    fun x  ->
      FStar_Set.intersect s (FStar_Set.complement (FStar_Set.singleton x))
  
type ('Am0,'Am1) popped = unit
let (pop : mem -> mem) =
  fun m0  ->
    let dom =
      remove_elt (FStar_Map.domain (__proj__HS__item__h m0))
        (__proj__HS__item__tip m0)
       in
    let h0 = __proj__HS__item__h m0  in
    let h1 = FStar_Map.restrict dom (__proj__HS__item__h m0)  in
    let tip0 = __proj__HS__item__tip m0  in
    let tip1 = ()  in HS ((__proj__HS__item__rid_ctr m0), h1, ())
  
type ('Aa,'Arel) mreference' =
  | MkRef of unit * ('Aa,'Arel) FStar_Monotonic_Heap.mref 
let uu___is_MkRef : 'Aa 'Arel . ('Aa,'Arel) mreference' -> Prims.bool =
  fun projectee  -> true 
let __proj__MkRef__item__frame :
  'Aa 'Arel . ('Aa,'Arel) mreference' -> FStar_Monotonic_HyperHeap.rid =
  fun projectee  -> match projectee with | MkRef (frame,ref) -> frame 
let __proj__MkRef__item__ref :
  'Aa 'Arel .
    ('Aa,'Arel) mreference' -> ('Aa,'Arel) FStar_Monotonic_Heap.mref
  = fun projectee  -> match projectee with | MkRef (frame,ref) -> ref 
type ('Aa,'Arel) mreference = ('Aa,'Arel) mreference'
let frameOf :
  'Aa 'Arel . ('Aa,'Arel) mreference -> FStar_Monotonic_HyperHeap.rid =
  fun r  -> __proj__MkRef__item__frame r 
let mk_mreference :
  'Aa 'Arel .
    FStar_Monotonic_HyperHeap.rid ->
      ('Aa,'Arel) FStar_Monotonic_Heap.mref -> ('Aa,'Arel) mreference
  = fun id1  -> fun r  -> MkRef ((), r) 
let as_ref :
  'Aa 'Arel . ('Aa,'Arel) mreference -> ('Aa,'Arel) FStar_Monotonic_Heap.mref
  = fun x  -> __proj__MkRef__item__ref x 



type ('Aa,'Arel) mstackref = ('Aa,'Arel) mreference
type ('Aa,'Arel) mref = ('Aa,'Arel) mreference
type ('Aa,'Arel) mmmstackref = ('Aa,'Arel) mreference
type ('Aa,'Arel) mmmref = ('Aa,'Arel) mreference
type ('Ai,'Aa,'Arel) s_mref = ('Aa,'Arel) mreference
let (live_region : mem -> FStar_Monotonic_HyperHeap.rid -> Prims.bool) =
  fun m  -> fun i  -> FStar_Map.contains (__proj__HS__item__h m) i 



type ('Aa,'Arel,'Ar,'Am0,'Am1) fresh_ref = unit
type ('Ai,'Am0,'Am1) fresh_region = unit



let alloc :
  'Aa 'Arel .
    FStar_Monotonic_HyperHeap.rid ->
      'Aa ->
        Prims.bool ->
          mem -> (('Aa,'Arel) mreference,mem) FStar_Pervasives_Native.tuple2
  =
  fun id1  ->
    fun init1  ->
      fun mm  ->
        fun m  ->
          let uu____2165 =
            FStar_Monotonic_Heap.alloc
              (FStar_Map.sel (__proj__HS__item__h m) id1) init1 mm
             in
          match uu____2165 with
          | (r,h) ->
              let h1 = FStar_Map.upd (__proj__HS__item__h m) id1 h  in
              ((mk_mreference id1 r),
                (HS ((__proj__HS__item__rid_ctr m), h1, ())))
  
let free : 'Aa 'Arel . ('Aa,'Arel) mreference -> mem -> mem =
  fun r  ->
    fun m  ->
      let i = frameOf r  in
      let h = FStar_Map.sel (__proj__HS__item__h m) i  in
      let new_h = FStar_Monotonic_Heap.free_mm h (as_ref r)  in
      let new_h1 = FStar_Map.upd (__proj__HS__item__h m) i new_h  in
      HS ((__proj__HS__item__rid_ctr m), new_h1, ())
  
let upd_tot : 'Aa 'Arel . mem -> ('Aa,'Arel) mreference -> 'Aa -> mem =
  fun m  ->
    fun r  ->
      fun v  ->
        let i = frameOf r  in
        let h = FStar_Map.sel (__proj__HS__item__h m) i  in
        let new_h = FStar_Monotonic_Heap.upd_tot h (as_ref r) v  in
        let new_h1 = FStar_Map.upd (__proj__HS__item__h m) i new_h  in
        HS ((__proj__HS__item__rid_ctr m), new_h1, ())
  
let sel_tot : 'Aa 'Arel . mem -> ('Aa,'Arel) mreference -> 'Aa =
  fun m  ->
    fun r  ->
      FStar_Monotonic_Heap.sel_tot
        (FStar_Map.sel (__proj__HS__item__h m) (frameOf r)) (as_ref r)
  
type ('Am0,'Am1) fresh_frame = unit
let (hs_push_frame : mem -> mem) =
  fun m  ->
    let new_tip_rid = ()  in
    let h =
      FStar_Map.upd (__proj__HS__item__h m) new_tip_rid
        FStar_Monotonic_Heap.emp
       in
    HS (((__proj__HS__item__rid_ctr m) + (Prims.parse_int "1")), h, ())
  
let (new_eternal_region :
  mem ->
    FStar_Monotonic_HyperHeap.rid ->
      Prims.int FStar_Pervasives_Native.option ->
        (FStar_Monotonic_HyperHeap.rid,mem) FStar_Pervasives_Native.tuple2)
  =
  fun m  ->
    fun parent  ->
      fun c  ->
        let new_rid = ()  in
        let h1 =
          FStar_Map.upd (__proj__HS__item__h m) new_rid
            FStar_Monotonic_Heap.emp
           in
        (new_rid,
          (HS
             (((__proj__HS__item__rid_ctr m) + (Prims.parse_int "1")), h1,
               ())))
  



type ('As,'Am0,'Am1) modifies = unit
type ('As,'Am0,'Am1) modifies_transitively = unit
let (heap_only : mem -> Prims.bool) =
  fun m0  -> (__proj__HS__item__tip m0) = () 
let (top_frame : mem -> FStar_Monotonic_Heap.heap) =
  fun m  -> FStar_Map.sel (__proj__HS__item__h m) (__proj__HS__item__tip m) 


type ('Aid,'Ah0,'Ah1) modifies_one = unit
type ('Aid,'As,'Ah0,'Ah1) modifies_ref = unit




type some_ref =
  | Ref of unit * unit * (Obj.t,Obj.t) mreference 
let (uu___is_Ref : some_ref -> Prims.bool) = fun projectee  -> true 
type 'Aprojectee __proj__Ref__item__a = Obj.t
type ('Aprojectee,'Auu____3537,'Auu____3538) __proj__Ref__item__rel = Obj.t
let (__proj__Ref__item___2 : some_ref -> (Obj.t,Obj.t) mreference) =
  fun projectee  -> match projectee with | Ref (a,rel,_2) -> _2 
type some_refs = some_ref Prims.list
let rec (regions_of_some_refs :
  some_refs -> FStar_Monotonic_HyperHeap.rid FStar_Set.set) =
  fun rs  ->
    match rs with
    | [] -> FStar_Set.empty
    | (Ref (uu____3884,uu____3885,r))::tl1 ->
        FStar_Set.union (FStar_Set.singleton (frameOf r))
          (regions_of_some_refs tl1)
  


let (norm_steps : FStar_Pervasives_Native.norm_step Prims.list) =
  [FStar_Pervasives_Native.iota;
  FStar_Pervasives_Native.zeta;
  FStar_Pervasives_Native.delta;
  FStar_Pervasives_Native.delta_only
    ["FStar.Monotonic.HyperStack.regions_of_some_refs";
    "FStar.Monotonic.HyperStack.refs_in_region";
    "FStar.Monotonic.HyperStack.modifies_some_refs"];
  FStar_Pervasives_Native.primops] 
type ('Ars,'Ah0,'Ah1) mods = unit




type aref =
  | ARef of unit * FStar_Monotonic_Heap.aref 
let (uu___is_ARef : aref -> Prims.bool) = fun projectee  -> true 
let (__proj__ARef__item__aref_region : aref -> FStar_Monotonic_HyperHeap.rid)
  =
  fun projectee  ->
    match projectee with | ARef (aref_region,aref_aref) -> aref_region
  
let (__proj__ARef__item__aref_aref : aref -> FStar_Monotonic_Heap.aref) =
  fun projectee  ->
    match projectee with | ARef (aref_region,aref_aref) -> aref_aref
  
let (dummy_aref : aref) = ARef ((), FStar_Monotonic_Heap.dummy_aref) 

let aref_of : 'At 'Arel . ('At,'Arel) mreference -> aref =
  fun r  -> ARef ((), (FStar_Monotonic_Heap.aref_of (as_ref r))) 






type ('Aa,'Ah) aref_unused_in = unit


type ('Ah,'Aa,'Av,'Arel) aref_live_at = unit

let (reference_of : mem -> aref -> unit -> unit -> (Obj.t,Obj.t) mreference)
  =
  fun h  ->
    fun a  ->
      fun v  ->
        fun rel  ->
          MkRef
            ((),
              (FStar_Monotonic_Heap.ref_of
                 (FStar_Map.sel (__proj__HS__item__h h)
                    (__proj__ARef__item__aref_region a))
                 (__proj__ARef__item__aref_aref a) () ()))
  








