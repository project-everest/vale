open Prims

let (op_Slash : Prims.int -> Prims.int -> Prims.int) =
  fun a  ->
    fun b  ->
      if
        ((a >= (Prims.parse_int "0")) && (b < (Prims.parse_int "0"))) ||
          ((a < (Prims.parse_int "0")) && (b >= (Prims.parse_int "0")))
      then - ((Prims.abs a) / (Prims.abs b))
      else (Prims.abs a) / (Prims.abs b)
  
let (div_eucl : Prims.int -> Prims.nonzero -> Prims.int) =
  fun a  ->
    fun b  ->
      if a < (Prims.parse_int "0")
      then
        (if (a mod b) = (Prims.parse_int "0")
         then - (- (op_Slash a b))
         else (- (- (op_Slash a b))) - (Prims.parse_int "1"))
      else op_Slash a b
  
let (op_Slash_Percent : Prims.int -> Prims.nonzero -> Prims.int) = div_eucl 
let (op_At_Percent : Prims.int -> Prims.int -> Prims.int) =
  fun v  ->
    fun p  ->
      let m = v mod p  in
      if m >= (op_Slash p (Prims.parse_int "2")) then m - p else m
  
let (max_int : Prims.pos -> Prims.int) =
  fun n  -> (Prims.pow2 (n - (Prims.parse_int "1"))) - (Prims.parse_int "1") 
let (min_int : Prims.pos -> Prims.int) =
  fun n  -> - (Prims.pow2 (n - (Prims.parse_int "1"))) 
let (fits : Prims.int -> Prims.pos -> Prims.bool) =
  fun x  -> fun n  -> ((min_int n) <= x) && (x <= (max_int n)) 
type ('Ax,'An) size = unit
type 'An int_t = Prims.int
let (add : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n  -> fun a  -> fun b  -> a + b 
let (add_mod : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n  -> fun a  -> fun b  -> op_At_Percent (a + b) (Prims.pow2 n) 
let (sub : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n  -> fun a  -> fun b  -> a - b 
let (sub_mod : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n  -> fun a  -> fun b  -> op_At_Percent (a - b) (Prims.pow2 n) 
let (mul : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n  -> fun a  -> fun b  -> a * b 
let (mul_mod : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n  -> fun a  -> fun b  -> op_At_Percent (a * b) (Prims.pow2 n) 
let (div : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n  -> fun a  -> fun b  -> op_Slash a b 
let (mod_ : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n  -> fun a  -> fun b  -> a - ((op_Slash a b) * b) 
let (logand : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun a81  ->
    fun a82  ->
      fun a83  ->
        (Obj.magic
           (fun n  ->
              fun uu____1350  ->
                fun uu____1351  -> failwith "Not yet implemented:logand"))
          a81 a82 a83
  
let (logxor : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun a84  ->
    fun a85  ->
      fun a86  ->
        (Obj.magic
           (fun n  ->
              fun uu____1458  ->
                fun uu____1459  -> failwith "Not yet implemented:logxor"))
          a84 a85 a86
  
let (logor : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun a87  ->
    fun a88  ->
      fun a89  ->
        (Obj.magic
           (fun n  ->
              fun uu____1566  ->
                fun uu____1567  -> failwith "Not yet implemented:logor")) a87
          a88 a89
  
let (lognot : Prims.pos -> unit int_t -> unit int_t) =
  fun a90  ->
    fun a91  ->
      (Obj.magic
         (fun n  -> fun uu____1654  -> failwith "Not yet implemented:lognot"))
        a90 a91
  
let (eq : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a = b 
let (gt : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a > b 
let (gte : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a >= b 
let (lt : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a < b 
let (lte : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n  -> fun a  -> fun b  -> a <= b 
let (to_int_t : Prims.pos -> Prims.int -> unit int_t) =
  fun m  -> fun a  -> op_At_Percent a (Prims.pow2 m) 
let (shift_right : Prims.pos -> unit int_t -> Prims.nat -> unit int_t) =
  fun a92  ->
    fun a93  ->
      fun a94  ->
        (Obj.magic
           (fun n  ->
              fun a  -> fun s  -> failwith "Not yet implemented:shift_right"))
          a92 a93 a94
  
let (shift_left : Prims.pos -> unit int_t -> Prims.nat -> unit int_t) =
  fun n  ->
    fun a  -> fun s  -> op_At_Percent (a * (Prims.pow2 s)) (Prims.pow2 n)
  