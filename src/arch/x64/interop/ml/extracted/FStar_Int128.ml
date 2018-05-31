open Prims
let (n : Prims.int) = (Prims.parse_int "128") 
type t =
  | Mk of unit FStar_Int.int_t 
let (uu___is_Mk : t -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk__item__v : t -> unit FStar_Int.int_t) =
  fun projectee  -> match projectee with | Mk v1 -> v1 
let (v : t -> unit FStar_Int.int_t) = fun x  -> __proj__Mk__item__v x 
let (int_to_t : unit FStar_Int.int_t -> t) = fun x  -> Mk x 



let (add : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_Int.add (Prims.parse_int "128") (v a) (v b)) 
let (sub : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_Int.sub (Prims.parse_int "128") (v a) (v b)) 
let (mul : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_Int.mul (Prims.parse_int "128") (v a) (v b)) 
let (div : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_Int.div (Prims.parse_int "128") (v a) (v b)) 
let (rem : t -> t -> t) =
  fun a  -> fun b  -> Mk (FStar_Int.mod_ (Prims.parse_int "128") (v a) (v b)) 
let (logand : t -> t -> t) =
  fun x  ->
    fun y  -> Mk (FStar_Int.logand (Prims.parse_int "128") (v x) (v y))
  
let (logxor : t -> t -> t) =
  fun x  ->
    fun y  -> Mk (FStar_Int.logxor (Prims.parse_int "128") (v x) (v y))
  
let (logor : t -> t -> t) =
  fun x  ->
    fun y  -> Mk (FStar_Int.logor (Prims.parse_int "128") (v x) (v y))
  
let (lognot : t -> t) =
  fun x  -> Mk (FStar_Int.lognot (Prims.parse_int "128") (v x)) 
let (shift_right : t -> FStar_UInt32.t -> t) =
  fun a  ->
    fun s  ->
      Mk
        (FStar_Int.shift_right (Prims.parse_int "128") (v a)
           (FStar_UInt32.v s))
  
let (shift_left : t -> FStar_UInt32.t -> t) =
  fun a  ->
    fun s  ->
      Mk
        (FStar_Int.shift_left (Prims.parse_int "128") (v a)
           (FStar_UInt32.v s))
  
let (eq : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_Int.eq (Prims.parse_int "128") (v a) (v b) 
let (gt : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_Int.gt (Prims.parse_int "128") (v a) (v b) 
let (gte : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_Int.gte (Prims.parse_int "128") (v a) (v b) 
let (lt : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_Int.lt (Prims.parse_int "128") (v a) (v b) 
let (lte : t -> t -> Prims.bool) =
  fun a  -> fun b  -> FStar_Int.lte (Prims.parse_int "128") (v a) (v b) 
let (op_Plus_Hat : t -> t -> t) = add 
let (op_Subtraction_Hat : t -> t -> t) = sub 
let (op_Star_Hat : t -> t -> t) = mul 
let (op_Slash_Hat : t -> t -> t) = div 
let (op_Percent_Hat : t -> t -> t) = rem 
let (op_Hat_Hat : t -> t -> t) = logxor 
let (op_Amp_Hat : t -> t -> t) = logand 
let (op_Bar_Hat : t -> t -> t) = logor 
let (op_Less_Less_Hat : t -> FStar_UInt32.t -> t) = shift_left 
let (op_Greater_Greater_Hat : t -> FStar_UInt32.t -> t) = shift_right 
let (op_Equals_Hat : t -> t -> Prims.bool) = eq 
let (op_Greater_Hat : t -> t -> Prims.bool) = gt 
let (op_Greater_Equals_Hat : t -> t -> Prims.bool) = gte 
let (op_Less_Hat : t -> t -> Prims.bool) = lt 
let (op_Less_Equals_Hat : t -> t -> Prims.bool) = lte 
let (to_string : t -> Prims.string) =
  fun a100  ->
    (Obj.magic (fun uu____541  -> failwith "Not yet implemented:to_string"))
      a100
  
let (of_string : Prims.string -> t) =
  fun a101  ->
    (Obj.magic (fun uu____549  -> failwith "Not yet implemented:of_string"))
      a101
  
let (__int_to_t : Prims.int -> t) = fun x  -> int_to_t x 
let (mul_wide : FStar_Int64.t -> FStar_Int64.t -> t) =
  fun a  -> fun b  -> Mk ((FStar_Int64.v a) * (FStar_Int64.v b)) 