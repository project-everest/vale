open Prims
type ('Aa,'Ab,'Ax) opt = 'Ab FStar_Pervasives_Native.option
type ('Aa,'Ab) partial_dependent_map =
  ('Aa,('Aa,'Ab,unit) opt) FStar_DependentMap.t
let empty_partial_dependent_map :
  'Aa 'Ab . unit -> ('Aa,'Ab) partial_dependent_map =
  fun uu____68  ->
    FStar_DependentMap.create (fun x  -> FStar_Pervasives_Native.None)
  
type ('Aa,'Ab) map = ('Aa,'Ab) Prims.dtuple2 Prims.list

let empty : 'Aa 'Ab . unit -> ('Aa,'Ab) map = fun uu____157  -> [] 
let rec sel :
  'Aa 'Ab . ('Aa,'Ab) map -> 'Aa -> 'Ab FStar_Pervasives_Native.option =
  fun r  ->
    fun x  ->
      match r with
      | [] -> FStar_Pervasives_Native.None
      | (Prims.Mkdtuple2 (x',y))::tl1 ->
          if x = x' then FStar_Pervasives_Native.Some y else sel tl1 x
  
let upd : 'Aa 'Ab . ('Aa,'Ab) map -> 'Aa -> 'Ab -> ('Aa,'Ab) map =
  fun r  -> fun x  -> fun v  -> (Prims.Mkdtuple2 (x, v)) :: r 
type ('Aa,'Ab,'Ainv) imap = ('Aa,'Ab) map
type ('Aa,'Ab,'Ainv,'Am1,'Am2) grows' = unit
type ('Aa,'Ab,'Ainv,'Auu____594,'Auu____595) grows = unit
type ('Ar,'Aa,'Ab,'Ainv) t =
  (unit,('Aa,'Ab,'Ainv) imap,unit) FStar_HyperStack_ST.m_rref
type ('Aa,'Ab,'Ainv,'Ar,'At,'Ax,'Ah) defined = unit
type ('Aa,'Ab,'Ainv,'Ar,'At,'Ax,'Ah) fresh = unit

type ('Aa,'Ab,'Ainv,'Ar,'At,'Ax,'Ay,'Ah) contains = unit


let alloc :
  'Aa 'Ab 'Ainv . FStar_HyperStack_ST.erid -> unit -> (unit,'Aa,'Ab,'Ainv) t
  = fun r  -> fun uu____3873  -> FStar_HyperStack_ST.ralloc r [] 
let extend :
  'Aa 'Ab 'Ainv .
    FStar_HyperStack_ST.erid -> (unit,'Aa,'Ab,'Ainv) t -> 'Aa -> 'Ab -> unit
  =
  fun r  ->
    fun t  ->
      fun x  ->
        fun y  ->
          FStar_HyperStack_ST.recall t;
          (let cur = FStar_HyperStack_ST.op_Bang t  in
           FStar_HyperStack_ST.op_Colon_Equals t (upd cur x y);
           FStar_HyperStack_ST.mr_witness r () () (Obj.magic t) ())
  
let lookup :
  'Aa 'Ab 'Ainv .
    FStar_HyperStack_ST.erid ->
      (unit,'Aa,'Ab,'Ainv) t -> 'Aa -> 'Ab FStar_Pervasives_Native.option
  =
  fun r  ->
    fun t  ->
      fun x  ->
        let m = FStar_HyperStack_ST.op_Bang t  in
        let y = sel m x  in
        match y with
        | FStar_Pervasives_Native.None  -> y
        | FStar_Pervasives_Native.Some b ->
            (FStar_HyperStack_ST.mr_witness r () () (Obj.magic t) (); y)
  
type ('Aa,'Ab,'Ainv,'Ar,'At,'Ah,'Apred) forall_t = unit
let f_opt :
  'Aa 'Ab 'Ac .
    ('Aa -> 'Ab -> 'Ac) ->
      'Aa ->
        'Ab FStar_Pervasives_Native.option ->
          'Ac FStar_Pervasives_Native.option
  =
  fun f  ->
    fun x  ->
      fun y  ->
        match y with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some y1 ->
            FStar_Pervasives_Native.Some (f x y1)
  
let rec mmap_f :
  'Aa 'Ab 'Ac . ('Aa,'Ab) map -> ('Aa -> 'Ab -> 'Ac) -> ('Aa,'Ac) map =
  fun m  ->
    fun f  ->
      match m with
      | [] -> []
      | (Prims.Mkdtuple2 (x,y))::tl1 -> (Prims.Mkdtuple2 (x, (f x y))) ::
          (mmap_f tl1 f)
  
let map_f :
  'Aa 'Ab 'Ac 'Ainv 'Ainv' .
    FStar_HyperStack_ST.erid ->
      FStar_HyperStack_ST.erid ->
        (unit,'Aa,'Ab,'Ainv) t ->
          ('Aa -> 'Ab -> 'Ac) -> (unit,'Aa,'Ac,'Ainv') t
  =
  fun r  ->
    fun r'  ->
      fun t  ->
        fun f  ->
          let m = FStar_HyperStack_ST.op_Bang t  in
          FStar_HyperStack_ST.ralloc r' (mmap_f m f)
  