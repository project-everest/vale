open Prims
type 'An bv_t = Prims.bool FStar_Seq_Base.seq
let (zero_vec : Prims.pos -> unit bv_t) =
  fun n  -> FStar_Seq_Base.create n false 
let (elem_vec : Prims.pos -> Prims.nat -> unit bv_t) =
  fun n  ->
    fun i  -> FStar_Seq_Base.upd (FStar_Seq_Base.create n false) i true
  
let (ones_vec : Prims.pos -> unit bv_t) =
  fun n  -> FStar_Seq_Base.create n true 
let rec (logand_vec : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n  ->
    fun a  ->
      fun b  ->
        if n = (Prims.parse_int "1")
        then
          FStar_Seq_Base.create (Prims.parse_int "1")
            ((FStar_Seq_Base.index a (Prims.parse_int "0")) &&
               (FStar_Seq_Base.index b (Prims.parse_int "0")))
        else
          FStar_Seq_Base.append
            (FStar_Seq_Base.create (Prims.parse_int "1")
               ((FStar_Seq_Base.index a (Prims.parse_int "0")) &&
                  (FStar_Seq_Base.index b (Prims.parse_int "0"))))
            (logand_vec (n - (Prims.parse_int "1"))
               (FStar_Seq_Base.slice a (Prims.parse_int "1") n)
               (FStar_Seq_Base.slice b (Prims.parse_int "1") n))
  
let rec (logxor_vec : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n  ->
    fun a  ->
      fun b  ->
        if n = (Prims.parse_int "1")
        then
          FStar_Seq_Base.create (Prims.parse_int "1")
            ((FStar_Seq_Base.index a (Prims.parse_int "0")) <>
               (FStar_Seq_Base.index b (Prims.parse_int "0")))
        else
          FStar_Seq_Base.append
            (FStar_Seq_Base.create (Prims.parse_int "1")
               ((FStar_Seq_Base.index a (Prims.parse_int "0")) <>
                  (FStar_Seq_Base.index b (Prims.parse_int "0"))))
            (logxor_vec (n - (Prims.parse_int "1"))
               (FStar_Seq_Base.slice a (Prims.parse_int "1") n)
               (FStar_Seq_Base.slice b (Prims.parse_int "1") n))
  
let rec (logor_vec : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n  ->
    fun a  ->
      fun b  ->
        if n = (Prims.parse_int "1")
        then
          FStar_Seq_Base.create (Prims.parse_int "1")
            ((FStar_Seq_Base.index a (Prims.parse_int "0")) ||
               (FStar_Seq_Base.index b (Prims.parse_int "0")))
        else
          FStar_Seq_Base.append
            (FStar_Seq_Base.create (Prims.parse_int "1")
               ((FStar_Seq_Base.index a (Prims.parse_int "0")) ||
                  (FStar_Seq_Base.index b (Prims.parse_int "0"))))
            (logor_vec (n - (Prims.parse_int "1"))
               (FStar_Seq_Base.slice a (Prims.parse_int "1") n)
               (FStar_Seq_Base.slice b (Prims.parse_int "1") n))
  
let rec (lognot_vec : Prims.pos -> unit bv_t -> unit bv_t) =
  fun n  ->
    fun a  ->
      if n = (Prims.parse_int "1")
      then
        FStar_Seq_Base.create (Prims.parse_int "1")
          (Prims.op_Negation (FStar_Seq_Base.index a (Prims.parse_int "0")))
      else
        FStar_Seq_Base.append
          (FStar_Seq_Base.create (Prims.parse_int "1")
             (Prims.op_Negation
                (FStar_Seq_Base.index a (Prims.parse_int "0"))))
          (lognot_vec (n - (Prims.parse_int "1"))
             (FStar_Seq_Base.slice a (Prims.parse_int "1") n))
  





type ('An,'Aa,'Ab) is_subset_vec = unit
type ('An,'Aa,'Ab) is_superset_vec = unit


let (shift_left_vec : Prims.pos -> unit bv_t -> Prims.nat -> unit bv_t) =
  fun n  ->
    fun a  ->
      fun s  ->
        if s >= n
        then zero_vec n
        else
          if s = (Prims.parse_int "0")
          then a
          else
            FStar_Seq_Base.append (FStar_Seq_Base.slice a s n) (zero_vec s)
  
let (shift_right_vec : Prims.pos -> unit bv_t -> Prims.nat -> unit bv_t) =
  fun n  ->
    fun a  ->
      fun s  ->
        if s >= n
        then zero_vec n
        else
          if s = (Prims.parse_int "0")
          then a
          else
            FStar_Seq_Base.append (zero_vec s)
              (FStar_Seq_Base.slice a (Prims.parse_int "0") (n - s))
  



