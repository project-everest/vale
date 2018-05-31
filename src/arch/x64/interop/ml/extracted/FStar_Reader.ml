open Prims
type 'Aheap reader_pre_h = unit
type 'Aa reader_post_h = unit
type ('Aheap,'Aa) reader_wp_h = unit
type ('Aheap,'Aa,'Ax,'Ap,'Ah0) reader_return = 'Ap
type ('Aheap,'Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap,'Ah0) reader_bind_wp = unit
type ('Aheap,'Aa,'Ap,'Awp_then,'Awp_else,'Apost,'Ah0) reader_if_then_else =
  unit
type ('Aheap,'Aa,'Awp,'Apost,'Ah0) reader_ite_wp = unit
type ('Aheap,'Aa,'Awp1,'Awp2) reader_stronger = unit
type ('Aheap,'Aa,'Ab,'Awp,'Ap,'Ah) reader_close_wp = unit
type ('Aheap,'Aa,'Ap,'Awp,'Aq,'Ah) reader_assert_p = unit
type ('Aheap,'Aa,'Ap,'Awp,'Aq,'Ah) reader_assume_p = unit
type ('Aheap,'Aa,'Ap,'Ah) reader_null_wp = unit
type ('Aheap,'Aa,'Awp) reader_trivial = unit
let read : 'Aa . 'Aa FStar_ST.ref -> 'Aa =
  fun r  -> failwith "Not yet implemented:read" 
type ('Aa,'Awp,'Ap,'Ah) lift_reader_state = 'Awp
type ('Aa,'Awp,'Ap,'Ah) lift_div_reader = 'Awp
let (f : Prims.int FStar_ST.ref -> Prims.int) =
  fun r  -> let uu____441 = read r  in uu____441 + (Prims.parse_int "1") 
let (g : Prims.int FStar_ST.ref -> Prims.int FStar_ST.ref -> unit) =
  fun r  ->
    fun s  ->
      let x = f r  in let y = f s  in FStar_ST.op_Colon_Equals r (x + y)
  