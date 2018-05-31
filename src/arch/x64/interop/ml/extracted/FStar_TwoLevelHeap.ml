open Prims
type rid = Prims.int
type t = (rid,FStar_Monotonic_Heap.heap) FStar_Map.t
type st_pre = unit
type ('Aa,'Apre) st_post' = unit
type 'Aa st_post = unit
type 'Aa st_wp = unit
type ('Aid,'Aa) rref = 'Aa FStar_Heap.ref
let as_ref : 'Aa . rid -> (unit,'Aa) rref -> 'Aa FStar_Heap.ref =
  fun id1  -> fun r  -> r 
let ref_as_rref : 'Aa . rid -> 'Aa FStar_Heap.ref -> (unit,'Aa) rref =
  fun i  -> fun r  -> r 

let (new_region : unit -> rid) =
  fun uu____150  -> failwith "Not yet implemented:new_region" 


let ralloc : 'Aa . rid -> 'Aa -> (unit,'Aa) rref =
  fun i  -> fun init  -> failwith "Not yet implemented:ralloc" 
let op_Colon_Equals : 'Aa . rid -> (unit,'Aa) rref -> 'Aa -> unit =
  fun i  ->
    fun r  -> fun v  -> failwith "Not yet implemented:op_Colon_Equals"
  
let op_Bang : 'Aa . rid -> (unit,'Aa) rref -> 'Aa =
  fun i  -> fun r  -> failwith "Not yet implemented:op_Bang" 
let (get : unit -> t) = fun uu____332  -> failwith "Not yet implemented:get" 
type ('As,'Am0,'Am1) modifies = unit
type ('Ai,'Am0,'Am1) fresh_region = unit
type ('Aa,'Ai,'Ar,'Am) contains_ref = unit
type ('Aa,'Ai,'Ar,'Am0,'Am1) fresh_rref = unit