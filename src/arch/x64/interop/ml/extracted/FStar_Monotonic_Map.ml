open Prims
type ('Aa,'Ab) map' = 'Aa -> 'Ab FStar_Pervasives_Native.option
type ('Aa,'Ab,'Ainv) map = ('Aa,'Ab) map'
let upd : 'Aa 'Ab . ('Aa,'Ab) map' -> 'Aa -> 'Ab -> ('Aa,'Ab) map' =
  fun m  ->
    fun x  ->
      fun y  ->
        fun z  -> if x = z then FStar_Pervasives_Native.Some y else m z
  
let sel :
  'Aa 'Ab . ('Aa,'Ab) map' -> 'Aa -> 'Ab FStar_Pervasives_Native.option =
  fun m  -> fun x  -> m x 
type ('Aa,'Ab,'Ainv,'Am1,'Am2) grows = unit
type ('Ar,'Aa,'Ab,'Ainv) t =
  (unit,('Aa,'Ab,'Ainv) map,unit) FStar_HyperStack_ST.m_rref
let empty_map : 'Aa 'Ab . ('Aa,'Ab) map' =
  fun x  -> FStar_Pervasives_Native.None 
type rid = unit
let (alloc : rid -> unit -> unit -> unit -> (unit,Obj.t,Obj.t,Obj.t) t) =
  fun r  ->
    fun a  -> fun b  -> fun inv  -> FStar_HyperStack_ST.ralloc r empty_map
  
type ('Ar,'Aa,'Ab,'Ainv,'Am,'Ax,'Ah) defined = unit
type ('Ar,'Aa,'Ab,'Ainv,'Am,'Ax,'Ay,'Ah) contains = unit

type ('Ar,'Aa,'Ab,'Ainv,'Am,'Ax,'Ah) fresh = unit

let (extend :
  rid ->
    unit ->
      unit -> unit -> (unit,Obj.t,Obj.t,Obj.t) t -> Obj.t -> Obj.t -> unit)
  =
  fun r  ->
    fun a  ->
      fun b  ->
        fun inv  ->
          fun m  ->
            fun x  ->
              fun y  ->
                FStar_HyperStack_ST.recall m;
                (let cur = FStar_HyperStack_ST.op_Bang m  in
                 FStar_HyperStack_ST.op_Colon_Equals m (upd cur x y);
                 FStar_HyperStack_ST.mr_witness r () () (Obj.magic m) ();
                 FStar_HyperStack_ST.mr_witness r () () (Obj.magic m) ())
  
let (lookup :
  FStar_HyperStack_ST.erid ->
    unit ->
      unit ->
        unit ->
          (unit,Obj.t,Obj.t,Obj.t) t ->
            Obj.t -> Obj.t FStar_Pervasives_Native.option)
  =
  fun r  ->
    fun a  ->
      fun b  ->
        fun inv  ->
          fun m  ->
            fun x  ->
              let y =
                let uu____3924 = FStar_HyperStack_ST.op_Bang m  in
                sel uu____3924 x  in
              match y with
              | FStar_Pervasives_Native.None  -> y
              | FStar_Pervasives_Native.Some b ->
                  (FStar_HyperStack_ST.mr_witness r () () (Obj.magic m) ();
                   FStar_HyperStack_ST.mr_witness r () () (Obj.magic m) ();
                   y)
  