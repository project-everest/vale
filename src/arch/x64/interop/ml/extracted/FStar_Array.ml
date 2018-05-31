open Prims
type 'At array = 'At FStar_Seq_Base.seq FStar_ST.ref






let op_At_Bar : 'Aa . 'Aa array -> 'Aa array -> 'Aa array =
  fun s1  ->
    fun s2  ->
      let s1' = FStar_Ref.op_Bang s1  in
      let s2' = FStar_Ref.op_Bang s2  in
      FStar_ST.alloc (FStar_Seq_Base.append s1' s2')
  
let of_seq : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa array =
  fun s  -> FStar_ST.alloc s 
let to_seq : 'Aa . 'Aa array -> 'Aa FStar_Seq_Base.seq =
  fun s  -> FStar_Ref.op_Bang s 
let create : 'Aa . Prims.nat -> 'Aa -> 'Aa array =
  fun n  -> fun init1  -> FStar_ST.alloc (FStar_Seq_Base.create n init1) 
let index : 'Aa . 'Aa array -> Prims.nat -> 'Aa =
  fun x  -> fun n  -> let s = to_seq x  in FStar_Seq_Base.index s n 
let upd : 'Aa . 'Aa array -> Prims.nat -> 'Aa -> unit =
  fun x  ->
    fun n  ->
      fun v  ->
        let s = FStar_Ref.op_Bang x  in
        let s' = FStar_Seq_Base.upd s n v  in FStar_Ref.op_Colon_Equals x s'
  
let length : 'Aa . 'Aa array -> Prims.nat =
  fun x  -> let s = FStar_Ref.op_Bang x  in FStar_Seq_Base.length s 
let op :
  'Aa .
    ('Aa FStar_Seq_Base.seq -> 'Aa FStar_Seq_Base.seq) -> 'Aa array -> unit
  =
  fun f  ->
    fun x  ->
      let s = FStar_Ref.op_Bang x  in
      let s' = f s  in FStar_Ref.op_Colon_Equals x s'
  
let swap : 'Aa . 'Aa array -> Prims.nat -> Prims.nat -> unit =
  fun x  ->
    fun i  ->
      fun j  ->
        let tmpi = index x i  in
        let tmpj = index x j  in upd x j tmpi; upd x i tmpj
  
let rec copy_aux : 'Aa . 'Aa array -> 'Aa array -> Prims.nat -> unit =
  fun s  ->
    fun cpy  ->
      fun ctr  ->
        let uu____1212 = let uu____1213 = length cpy  in uu____1213 - ctr  in
        match uu____1212 with
        | _0_3 when _0_3 = (Prims.parse_int "0") -> ()
        | uu____1240 ->
            ((let uu____1242 = index s ctr  in upd cpy ctr uu____1242);
             copy_aux s cpy (ctr + (Prims.parse_int "1")))
  
let copy : 'Aa . 'Aa array -> 'Aa array =
  fun s  ->
    let cpy =
      let uu____1430 = length s  in
      let uu____1453 = index s (Prims.parse_int "0")  in
      create uu____1430 uu____1453  in
    copy_aux s cpy (Prims.parse_int "0"); cpy
  
let rec blit_aux :
  'Aa .
    'Aa array ->
      Prims.nat -> 'Aa array -> Prims.nat -> Prims.nat -> Prims.nat -> unit
  =
  fun s  ->
    fun s_idx  ->
      fun t  ->
        fun t_idx  ->
          fun len  ->
            fun ctr  ->
              match len - ctr with
              | _0_4 when _0_4 = (Prims.parse_int "0") -> ()
              | uu____1689 ->
                  ((let uu____1691 = index s (s_idx + ctr)  in
                    upd t (t_idx + ctr) uu____1691);
                   blit_aux s s_idx t t_idx len (ctr + (Prims.parse_int "1")))
  
let rec blit :
  'Aa . 'Aa array -> Prims.nat -> 'Aa array -> Prims.nat -> Prims.nat -> unit
  =
  fun s  ->
    fun s_idx  ->
      fun t  ->
        fun t_idx  ->
          fun len  -> blit_aux s s_idx t t_idx len (Prims.parse_int "0")
  
let sub : 'Aa . 'Aa array -> Prims.nat -> Prims.nat -> 'Aa array =
  fun s  ->
    fun idx  ->
      fun len  ->
        let t =
          let uu____2108 = index s (Prims.parse_int "0")  in
          create len uu____2108  in
        blit s idx t (Prims.parse_int "0") len; t
  