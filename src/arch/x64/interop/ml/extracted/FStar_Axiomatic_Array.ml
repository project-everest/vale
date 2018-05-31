open Prims
type 'Auu____2 seq = unit
let index : 'Aa . 'Aa seq -> Prims.int -> 'Aa =
  fun a98  ->
    fun a99  ->
      (Obj.magic
         (fun uu____29  ->
            fun uu____30  -> failwith "Not yet implemented:index")) a98 a99
  
let update : 'Aa . 'Aa seq -> Prims.int -> 'Aa -> 'Aa seq =
  fun a100  ->
    fun a101  ->
      fun a102  ->
        (Obj.magic
           (fun uu____70  ->
              fun uu____71  ->
                fun uu____72  -> failwith "Not yet implemented:update")) a100
          a101 a102
  
let emp : 'Aa . unit -> 'Aa seq =
  fun a103  ->
    (Obj.magic (fun uu____85  -> failwith "Not yet implemented:emp")) a103
  
let create : 'Aa . Prims.int -> 'Aa -> 'Aa seq =
  fun a104  ->
    fun a105  ->
      (Obj.magic
         (fun uu____114  ->
            fun uu____115  -> failwith "Not yet implemented:create")) a104
        a105
  
let length : 'Aa . 'Aa seq -> Prims.nat =
  fun a106  ->
    (Obj.magic (fun uu____139  -> failwith "Not yet implemented:length"))
      a106
  
let slice : 'Aa . 'Aa seq -> Prims.int -> Prims.int -> 'Aa seq =
  fun a107  ->
    fun a108  ->
      fun a109  ->
        (Obj.magic
           (fun uu____179  ->
              fun uu____180  ->
                fun uu____181  -> failwith "Not yet implemented:slice")) a107
          a108 a109
  
let append : 'Aa . 'Aa seq -> 'Aa seq -> 'Aa seq =
  fun a110  ->
    fun a111  ->
      (Obj.magic
         (fun uu____216  ->
            fun uu____217  -> failwith "Not yet implemented:append")) a110
        a111
  
let proj_some : 'Aa . 'Aa FStar_Pervasives_Native.option seq -> 'Aa seq =
  fun a112  ->
    (Obj.magic (fun uu____245  -> failwith "Not yet implemented:proj_some"))
      a112
  
type ('Aa,'Auu____256,'Auu____257) equal = unit
type 'Aa array = 'Aa seq FStar_Heap.ref
type ('Aa,'As) is_Some_All = unit