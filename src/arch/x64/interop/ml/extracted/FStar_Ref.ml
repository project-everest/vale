open Prims



type ('Aa,'Ah,'Ar) contains =
  ('Aa,unit,unit,unit) FStar_Monotonic_Heap.contains
type ('Aa,'Ar,'Ah) unused_in =
  ('Aa,unit,unit,unit) FStar_Monotonic_Heap.unused_in
type ('Aa,'Ar,'Ah0,'Ah1) fresh = unit

let recall : 'Aa . 'Aa FStar_ST.ref -> unit = fun r  -> FStar_ST.recall r 
let alloc : 'Aa . 'Aa -> 'Aa FStar_ST.ref = fun init  -> FStar_ST.alloc init 
let read : 'Aa . 'Aa FStar_ST.ref -> 'Aa = fun r  -> FStar_ST.read r 
let write : 'Aa . 'Aa FStar_ST.ref -> 'Aa -> unit =
  fun r  -> fun v  -> FStar_ST.write r v 
let op_Bang : 'Aa . 'Aa FStar_ST.ref -> 'Aa = fun r  -> read r 
let op_Colon_Equals : 'Aa . 'Aa FStar_ST.ref -> 'Aa -> unit =
  fun r  -> fun v  -> write r v 