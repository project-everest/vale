open Prims
type ('Aa,'Ar,'Alen,'Ab,'Ah0,'Ah1) rcreate_post_common = unit
let rfree : 'Aa . 'Aa LowStar_Buffer.buffer -> unit =
  fun b  -> LowStar_Buffer.free b 
let rcreate :
  'Aa .
    FStar_Monotonic_HyperHeap.rid ->
      'Aa -> FStar_UInt32.t -> 'Aa LowStar_Buffer.buffer
  = fun r  -> fun init1  -> fun len  -> LowStar_Buffer.gcmalloc r init1 len 
let rcreate_mm :
  'Aa .
    FStar_Monotonic_HyperHeap.rid ->
      'Aa -> FStar_UInt32.t -> 'Aa LowStar_Buffer.buffer
  = fun r  -> fun init1  -> fun len  -> LowStar_Buffer.malloc r init1 len 
let create : 'Aa . 'Aa -> FStar_UInt32.t -> 'Aa LowStar_Buffer.buffer =
  fun init1  -> fun len  -> LowStar_Buffer.alloca init1 len 
type ('Aa,'Ainit) createL_pre = unit
type ('Aa,'Alen,'Abuf) createL_post = unit
let createL : 'Aa . 'Aa Prims.list -> 'Aa LowStar_Buffer.buffer =
  fun init1  -> LowStar_Buffer.alloca_of_list init1 