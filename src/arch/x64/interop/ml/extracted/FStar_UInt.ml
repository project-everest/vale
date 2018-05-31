open Prims

let (max_int : Prims.nat -> Prims.int) =
  fun n  -> (Prims.pow2 n) - (Prims.parse_int "1") 
let (min_int : Prims.nat -> Prims.int) = fun n  -> (Prims.parse_int "0") 
let (fits : Prims.int -> Prims.nat -> Prims.bool) =
  fun x  -> fun n  -> ((min_int n) <= x) && (x <= (max_int n)) 
type ('Ax,'An) size = unit
type 'An uint_t = Prims.int
let (zero : Prims.nat -> unit uint_t) = fun n  -> (Prims.parse_int "0") 
let (pow2_n : Prims.pos -> Prims.nat -> unit uint_t) =
  fun n  -> fun p  -> Prims.pow2 p 
let (one : Prims.pos -> unit uint_t) = fun n  -> (Prims.parse_int "1") 
let (ones : Prims.nat -> unit uint_t) = fun n  -> max_int n 
let (incr : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> a + (Prims.parse_int "1") 
let (decr : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> a - (Prims.parse_int "1") 
let (incr_underspec : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n  ->
    fun a  ->
      if a < (max_int n)
      then a + (Prims.parse_int "1")
      else (Prims.parse_int "0")
  
let (decr_underspec : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n  ->
    fun a  ->
      if a > (min_int n)
      then a - (Prims.parse_int "1")
      else (Prims.parse_int "0")
  
let (incr_mod : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> (a + (Prims.parse_int "1")) mod (Prims.pow2 n) 
let (decr_mod : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> (a - (Prims.parse_int "1")) mod (Prims.pow2 n) 
let (add : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> a + b 
let (add_underspec : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t)
  =
  fun n  ->
    fun a  ->
      fun b  -> if fits (a + b) n then a + b else (Prims.parse_int "0")
  
let (add_mod : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> (a + b) mod (Prims.pow2 n) 
let (sub : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> a - b 
let (sub_underspec : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t)
  =
  fun n  ->
    fun a  ->
      fun b  -> if fits (a - b) n then a - b else (Prims.parse_int "0")
  
let (sub_mod : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> (a - b) mod (Prims.pow2 n) 
let (mul : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> a * b 
let (mul_underspec : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t)
  =
  fun n  ->
    fun a  ->
      fun b  -> if fits (a * b) n then a * b else (Prims.parse_int "0")
  
let (mul_mod : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> (a * b) mod (Prims.pow2 n) 

let (mul_div : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> (a * b) / (Prims.pow2 n) 
let (div : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> a / b 
let (div_underspec : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t)
  =
  fun n  ->
    fun a  ->
      fun b  -> if fits (a / b) n then a / b else (Prims.parse_int "0")
  

let (udiv : Prims.pos -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> a / b 
let (mod_ : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> fun b  -> a - ((a / b) * b) 
let (eq : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a = b 
let (gt : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a > b 
let (gte : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a >= b 
let (lt : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a < b 
let (lte : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a <= b 
let (to_uint_t : Prims.nat -> Prims.int -> unit uint_t) =
  fun m  -> fun a  -> a mod (Prims.pow2 m) 
let rec (to_vec : Prims.nat -> unit uint_t -> unit FStar_BitVector.bv_t) =
  fun n  ->
    fun num  ->
      if n = (Prims.parse_int "0")
      then FStar_Seq_Base.createEmpty ()
      else
        FStar_Seq_Base.append
          (to_vec (n - (Prims.parse_int "1")) (num / (Prims.parse_int "2")))
          (FStar_Seq_Base.create (Prims.parse_int "1")
             ((num mod (Prims.parse_int "2")) = (Prims.parse_int "1")))
  
let rec (from_vec : Prims.nat -> unit FStar_BitVector.bv_t -> unit uint_t) =
  fun n  ->
    fun vec  ->
      if n = (Prims.parse_int "0")
      then (Prims.parse_int "0")
      else
        ((Prims.parse_int "2") *
           (from_vec (n - (Prims.parse_int "1"))
              (FStar_Seq_Base.slice vec (Prims.parse_int "0")
                 (n - (Prims.parse_int "1")))))
          +
          (if FStar_Seq_Base.index vec (n - (Prims.parse_int "1"))
           then (Prims.parse_int "1")
           else (Prims.parse_int "0"))
  




















let (nth : Prims.pos -> unit uint_t -> Prims.nat -> Prims.bool) =
  fun n  -> fun a  -> fun i  -> FStar_Seq_Base.index (to_vec n a) i 





let (logand : Prims.pos -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  ->
    fun a  ->
      fun b  ->
        from_vec n (FStar_BitVector.logand_vec n (to_vec n a) (to_vec n b))
  
let (logxor : Prims.pos -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  ->
    fun a  ->
      fun b  ->
        from_vec n (FStar_BitVector.logxor_vec n (to_vec n a) (to_vec n b))
  
let (logor : Prims.pos -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n  ->
    fun a  ->
      fun b  ->
        from_vec n (FStar_BitVector.logor_vec n (to_vec n a) (to_vec n b))
  
let (lognot : Prims.pos -> unit uint_t -> unit uint_t) =
  fun n  -> fun a  -> from_vec n (FStar_BitVector.lognot_vec n (to_vec n a)) 
















let (xor : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b  -> fun b'  -> b <> b' 
















let (shift_left : Prims.pos -> unit uint_t -> Prims.nat -> unit uint_t) =
  fun n  ->
    fun a  ->
      fun s  -> from_vec n (FStar_BitVector.shift_left_vec n (to_vec n a) s)
  
let (shift_right : Prims.pos -> unit uint_t -> Prims.nat -> unit uint_t) =
  fun n  ->
    fun a  ->
      fun s  -> from_vec n (FStar_BitVector.shift_right_vec n (to_vec n a) s)
  

















