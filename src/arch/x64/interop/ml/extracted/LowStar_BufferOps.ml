open Prims
let op_Array_Access :
  'Auu____15 .
    unit -> 'Auu____15 LowStar_Buffer.buffer -> FStar_UInt32.t -> 'Auu____15
  = fun uu____29  -> LowStar_Buffer.index 
let op_Array_Assignment :
  'Auu____47 .
    unit ->
      'Auu____47 LowStar_Buffer.buffer ->
        FStar_UInt32.t -> 'Auu____47 -> unit
  = fun uu____64  -> LowStar_Buffer.upd 
let op_Bang_Star : 'Aa . 'Aa LowStar_Buffer.buffer -> 'Aa =
  fun p  ->
    LowStar_Buffer.index p (FStar_UInt32.uint_to_t (Prims.parse_int "0"))
  
let op_Star_Equals : 'Aa . 'Aa LowStar_Buffer.buffer -> 'Aa -> unit =
  fun p  ->
    fun v1  ->
      LowStar_Buffer.upd p (FStar_UInt32.uint_to_t (Prims.parse_int "0")) v1
  