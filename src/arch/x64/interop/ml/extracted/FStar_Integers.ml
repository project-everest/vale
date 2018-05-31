open Prims
type signedness =
  | Signed 
  | Unsigned 
let (uu___is_Signed : signedness -> Prims.bool) =
  fun projectee  -> match projectee with | Signed  -> true | uu____8 -> false 
let (uu___is_Unsigned : signedness -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unsigned  -> true | uu____16 -> false
  
type width =
  | W8 
  | W16 
  | W31 
  | W32 
  | W63 
  | W64 
  | W128 
  | Winfinite 
let (uu___is_W8 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W8  -> true | uu____24 -> false 
let (uu___is_W16 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W16  -> true | uu____32 -> false 
let (uu___is_W31 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W31  -> true | uu____40 -> false 
let (uu___is_W32 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W32  -> true | uu____48 -> false 
let (uu___is_W63 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W63  -> true | uu____56 -> false 
let (uu___is_W64 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W64  -> true | uu____64 -> false 
let (uu___is_W128 : width -> Prims.bool) =
  fun projectee  -> match projectee with | W128  -> true | uu____72 -> false 
let (uu___is_Winfinite : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Winfinite  -> true | uu____80 -> false
  
type fixed_width = width
let (nat_of_width : width -> Prims.int FStar_Pervasives_Native.option) =
  fun uu___53_89  ->
    match uu___53_89 with
    | W8  -> FStar_Pervasives_Native.Some (Prims.parse_int "8")
    | W16  -> FStar_Pervasives_Native.Some (Prims.parse_int "16")
    | W31  -> FStar_Pervasives_Native.Some (Prims.parse_int "31")
    | W32  -> FStar_Pervasives_Native.Some (Prims.parse_int "32")
    | W63  -> FStar_Pervasives_Native.Some (Prims.parse_int "63")
    | W64  -> FStar_Pervasives_Native.Some (Prims.parse_int "64")
    | W128  -> FStar_Pervasives_Native.Some (Prims.parse_int "128")
    | Winfinite  -> FStar_Pervasives_Native.None
  
let (nat_of_fixed_width : fixed_width -> Prims.int) =
  fun w  -> match nat_of_width w with | FStar_Pervasives_Native.Some v1 -> v1 
type ('As,'Aw) int_t = Obj.t
type 'Ax nat_size = unit

type ('Ax,'An) uint_size = unit

type ('Ax,'An) int_size = unit

type ('As,'Aw,'Ax) within_bounds = Obj.t
let (v : signedness -> width -> Obj.t -> Prims.int) =
  fun s  ->
    fun w  ->
      fun x  ->
        match s with
        | Unsigned  ->
            (match w with
             | Winfinite  -> Obj.magic x
             | W8  -> FStar_UInt8.v (Obj.magic x)
             | W16  -> FStar_UInt16.v (Obj.magic x)
             | W31  -> FStar_UInt31.v (Obj.magic x)
             | W32  -> FStar_UInt32.v (Obj.magic x)
             | W63  -> FStar_UInt63.v (Obj.magic x)
             | W64  -> FStar_UInt64.v (Obj.magic x)
             | W128  -> FStar_UInt128.v (Obj.magic x))
        | Signed  ->
            Obj.magic
              (match w with
               | Winfinite  -> Obj.repr x
               | W8  -> Obj.repr (FStar_Int8.v (Obj.magic x))
               | W16  -> Obj.repr (FStar_Int16.v (Obj.magic x))
               | W31  -> Obj.repr (FStar_Int31.v (Obj.magic x))
               | W32  -> Obj.repr (FStar_Int32.v (Obj.magic x))
               | W63  -> Obj.repr (FStar_Int63.v (Obj.magic x))
               | W64  -> Obj.repr (FStar_Int64.v (Obj.magic x))
               | W128  -> Obj.repr (FStar_Int128.v (Obj.magic x)))
  
let (u : signedness -> width -> Prims.int -> Obj.t) =
  fun s  ->
    fun w  ->
      fun x  ->
        match s with
        | Unsigned  ->
            (match w with
             | Winfinite  -> Obj.repr x
             | W8  -> Obj.repr (FStar_UInt8.uint_to_t x)
             | W16  -> Obj.repr (FStar_UInt16.uint_to_t x)
             | W31  -> Obj.repr (FStar_UInt31.uint_to_t x)
             | W32  -> Obj.repr (FStar_UInt32.uint_to_t x)
             | W63  -> Obj.repr (FStar_UInt63.uint_to_t x)
             | W64  -> Obj.repr (FStar_UInt64.uint_to_t x)
             | W128  -> Obj.repr (FStar_UInt128.uint_to_t x))
        | Signed  ->
            (match w with
             | Winfinite  -> Obj.repr x
             | W8  -> Obj.repr (FStar_Int8.int_to_t x)
             | W16  -> Obj.repr (FStar_Int16.int_to_t x)
             | W31  -> Obj.repr (FStar_Int31.int_to_t x)
             | W32  -> Obj.repr (FStar_Int32.int_to_t x)
             | W63  -> Obj.repr (FStar_Int63.int_to_t x)
             | W64  -> Obj.repr (FStar_Int64.int_to_t x)
             | W128  -> Obj.repr (FStar_Int128.int_to_t x))
  
let (cast : signedness -> signedness -> width -> width -> Obj.t -> Obj.t) =
  fun s  -> fun s'  -> fun w  -> fun w'  -> fun from  -> u s' w' (v s w from) 
let (op_Plus : signedness -> width -> Obj.t -> Obj.t -> Obj.t) =
  fun s  ->
    fun w  ->
      fun x  ->
        fun y  ->
          match (s, w) with
          | (uu____1308,Winfinite ) ->
              Obj.repr ((Obj.magic x) + (Obj.magic y))
          | (Unsigned ,W8 ) ->
              Obj.repr (FStar_UInt8.add (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W16 ) ->
              Obj.repr (FStar_UInt16.add (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W31 ) ->
              Obj.repr (FStar_UInt31.add (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W32 ) ->
              Obj.repr (FStar_UInt32.add (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W63 ) ->
              Obj.repr (FStar_UInt63.add (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W64 ) ->
              Obj.repr (FStar_UInt64.add (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W128 ) ->
              Obj.repr (FStar_UInt128.add (Obj.magic x) (Obj.magic y))
          | (Signed ,W8 ) ->
              Obj.repr (FStar_Int8.add (Obj.magic x) (Obj.magic y))
          | (Signed ,W16 ) ->
              Obj.repr (FStar_Int16.add (Obj.magic x) (Obj.magic y))
          | (Signed ,W31 ) ->
              Obj.repr (FStar_Int31.add (Obj.magic x) (Obj.magic y))
          | (Signed ,W32 ) ->
              Obj.repr (FStar_Int32.add (Obj.magic x) (Obj.magic y))
          | (Signed ,W63 ) ->
              Obj.repr (FStar_Int63.add (Obj.magic x) (Obj.magic y))
          | (Signed ,W64 ) ->
              Obj.repr (FStar_Int64.add (Obj.magic x) (Obj.magic y))
          | (Signed ,W128 ) ->
              Obj.repr (FStar_Int128.add (Obj.magic x) (Obj.magic y))
  
let (op_Plus_Question : width -> Obj.t -> Obj.t -> Obj.t) =
  fun w  ->
    fun x  ->
      fun y  ->
        match w with
        | Winfinite  ->
            Obj.repr
              (match (Unsigned, w) with
               | (uu____1757,Winfinite ) ->
                   Obj.repr ((Obj.magic x) + (Obj.magic y))
               | (Unsigned ,W8 ) ->
                   Obj.repr (FStar_UInt8.add (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W16 ) ->
                   Obj.repr (FStar_UInt16.add (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W31 ) ->
                   Obj.repr (FStar_UInt31.add (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W32 ) ->
                   Obj.repr (FStar_UInt32.add (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W63 ) ->
                   Obj.repr (FStar_UInt63.add (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W64 ) ->
                   Obj.repr (FStar_UInt64.add (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W128 ) ->
                   Obj.repr (FStar_UInt128.add (Obj.magic x) (Obj.magic y))
               | (Signed ,W8 ) ->
                   Obj.repr (FStar_Int8.add (Obj.magic x) (Obj.magic y))
               | (Signed ,W16 ) ->
                   Obj.repr (FStar_Int16.add (Obj.magic x) (Obj.magic y))
               | (Signed ,W31 ) ->
                   Obj.repr (FStar_Int31.add (Obj.magic x) (Obj.magic y))
               | (Signed ,W32 ) ->
                   Obj.repr (FStar_Int32.add (Obj.magic x) (Obj.magic y))
               | (Signed ,W63 ) ->
                   Obj.repr (FStar_Int63.add (Obj.magic x) (Obj.magic y))
               | (Signed ,W64 ) ->
                   Obj.repr (FStar_Int64.add (Obj.magic x) (Obj.magic y))
               | (Signed ,W128 ) ->
                   Obj.repr (FStar_Int128.add (Obj.magic x) (Obj.magic y)))
        | W8  ->
            Obj.repr (FStar_UInt8.add_underspec (Obj.magic x) (Obj.magic y))
        | W16  ->
            Obj.repr (FStar_UInt16.add_underspec (Obj.magic x) (Obj.magic y))
        | W31  ->
            Obj.repr (FStar_UInt31.add_underspec (Obj.magic x) (Obj.magic y))
        | W32  ->
            Obj.repr (FStar_UInt32.add_underspec (Obj.magic x) (Obj.magic y))
        | W63  ->
            Obj.repr (FStar_UInt63.add_underspec (Obj.magic x) (Obj.magic y))
        | W64  ->
            Obj.repr (FStar_UInt64.add_underspec (Obj.magic x) (Obj.magic y))
        | W128  ->
            Obj.repr
              (FStar_UInt128.add_underspec (Obj.magic x) (Obj.magic y))
  
let (modulo : signedness -> Prims.int -> Prims.pos -> Prims.int) =
  fun s  ->
    fun x  ->
      fun y  ->
        match s with
        | Unsigned  -> x mod y
        | uu____2227 -> FStar_Int.op_At_Percent x y
  
let (op_Plus_Percent : fixed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun w  ->
    fun x  ->
      fun y  ->
        match w with
        | W8  -> Obj.repr (FStar_UInt8.add_mod (Obj.magic x) (Obj.magic y))
        | W16  -> Obj.repr (FStar_UInt16.add_mod (Obj.magic x) (Obj.magic y))
        | W31  -> Obj.repr (FStar_UInt31.add_mod (Obj.magic x) (Obj.magic y))
        | W32  -> Obj.repr (FStar_UInt32.add_mod (Obj.magic x) (Obj.magic y))
        | W63  -> Obj.repr (FStar_UInt63.add_mod (Obj.magic x) (Obj.magic y))
        | W64  -> Obj.repr (FStar_UInt64.add_mod (Obj.magic x) (Obj.magic y))
        | W128  ->
            Obj.repr (FStar_UInt128.add_mod (Obj.magic x) (Obj.magic y))
  
let (op_Subtraction : signedness -> width -> Obj.t -> Obj.t -> Obj.t) =
  fun s  ->
    fun w  ->
      fun x  ->
        fun y  ->
          match (s, w) with
          | (uu____2651,Winfinite ) ->
              Obj.repr ((Obj.magic x) - (Obj.magic y))
          | (Unsigned ,W8 ) ->
              Obj.repr (FStar_UInt8.sub (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W16 ) ->
              Obj.repr (FStar_UInt16.sub (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W31 ) ->
              Obj.repr (FStar_UInt31.sub (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W32 ) ->
              Obj.repr (FStar_UInt32.sub (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W63 ) ->
              Obj.repr (FStar_UInt63.sub (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W64 ) ->
              Obj.repr (FStar_UInt64.sub (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W128 ) ->
              Obj.repr (FStar_UInt128.sub (Obj.magic x) (Obj.magic y))
          | (Signed ,W8 ) ->
              Obj.repr (FStar_Int8.sub (Obj.magic x) (Obj.magic y))
          | (Signed ,W16 ) ->
              Obj.repr (FStar_Int16.sub (Obj.magic x) (Obj.magic y))
          | (Signed ,W31 ) ->
              Obj.repr (FStar_Int31.sub (Obj.magic x) (Obj.magic y))
          | (Signed ,W32 ) ->
              Obj.repr (FStar_Int32.sub (Obj.magic x) (Obj.magic y))
          | (Signed ,W63 ) ->
              Obj.repr (FStar_Int63.sub (Obj.magic x) (Obj.magic y))
          | (Signed ,W64 ) ->
              Obj.repr (FStar_Int64.sub (Obj.magic x) (Obj.magic y))
          | (Signed ,W128 ) ->
              Obj.repr (FStar_Int128.sub (Obj.magic x) (Obj.magic y))
  
let (op_Subtraction_Question : width -> Obj.t -> Obj.t -> Obj.t) =
  fun w  ->
    fun x  ->
      fun y  ->
        match w with
        | Winfinite  ->
            Obj.repr
              (if
                 ((v Unsigned w x) - (v Unsigned w y)) >=
                   (Prims.parse_int "0")
               then
                 Obj.repr
                   (match (Unsigned, w) with
                    | (uu____3116,Winfinite ) ->
                        Obj.repr ((Obj.magic x) - (Obj.magic y))
                    | (Unsigned ,W8 ) ->
                        Obj.repr
                          (FStar_UInt8.sub (Obj.magic x) (Obj.magic y))
                    | (Unsigned ,W16 ) ->
                        Obj.repr
                          (FStar_UInt16.sub (Obj.magic x) (Obj.magic y))
                    | (Unsigned ,W31 ) ->
                        Obj.repr
                          (FStar_UInt31.sub (Obj.magic x) (Obj.magic y))
                    | (Unsigned ,W32 ) ->
                        Obj.repr
                          (FStar_UInt32.sub (Obj.magic x) (Obj.magic y))
                    | (Unsigned ,W63 ) ->
                        Obj.repr
                          (FStar_UInt63.sub (Obj.magic x) (Obj.magic y))
                    | (Unsigned ,W64 ) ->
                        Obj.repr
                          (FStar_UInt64.sub (Obj.magic x) (Obj.magic y))
                    | (Unsigned ,W128 ) ->
                        Obj.repr
                          (FStar_UInt128.sub (Obj.magic x) (Obj.magic y))
                    | (Signed ,W8 ) ->
                        Obj.repr (FStar_Int8.sub (Obj.magic x) (Obj.magic y))
                    | (Signed ,W16 ) ->
                        Obj.repr
                          (FStar_Int16.sub (Obj.magic x) (Obj.magic y))
                    | (Signed ,W31 ) ->
                        Obj.repr
                          (FStar_Int31.sub (Obj.magic x) (Obj.magic y))
                    | (Signed ,W32 ) ->
                        Obj.repr
                          (FStar_Int32.sub (Obj.magic x) (Obj.magic y))
                    | (Signed ,W63 ) ->
                        Obj.repr
                          (FStar_Int63.sub (Obj.magic x) (Obj.magic y))
                    | (Signed ,W64 ) ->
                        Obj.repr
                          (FStar_Int64.sub (Obj.magic x) (Obj.magic y))
                    | (Signed ,W128 ) ->
                        Obj.repr
                          (FStar_Int128.sub (Obj.magic x) (Obj.magic y)))
               else Obj.repr (Prims.parse_int "0"))
        | W8  ->
            Obj.repr (FStar_UInt8.sub_underspec (Obj.magic x) (Obj.magic y))
        | W16  ->
            Obj.repr (FStar_UInt16.sub_underspec (Obj.magic x) (Obj.magic y))
        | W31  ->
            Obj.repr (FStar_UInt31.sub_underspec (Obj.magic x) (Obj.magic y))
        | W32  ->
            Obj.repr (FStar_UInt32.sub_underspec (Obj.magic x) (Obj.magic y))
        | W63  ->
            Obj.repr (FStar_UInt63.sub_underspec (Obj.magic x) (Obj.magic y))
        | W64  ->
            Obj.repr (FStar_UInt64.sub_underspec (Obj.magic x) (Obj.magic y))
        | W128  ->
            Obj.repr
              (FStar_UInt128.sub_underspec (Obj.magic x) (Obj.magic y))
  
let (op_Subtraction_Percent : fixed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun w  ->
    fun x  ->
      fun y  ->
        match w with
        | W8  -> Obj.repr (FStar_UInt8.sub_mod (Obj.magic x) (Obj.magic y))
        | W16  -> Obj.repr (FStar_UInt16.sub_mod (Obj.magic x) (Obj.magic y))
        | W31  -> Obj.repr (FStar_UInt31.sub_mod (Obj.magic x) (Obj.magic y))
        | W32  -> Obj.repr (FStar_UInt32.sub_mod (Obj.magic x) (Obj.magic y))
        | W63  -> Obj.repr (FStar_UInt63.sub_mod (Obj.magic x) (Obj.magic y))
        | W64  -> Obj.repr (FStar_UInt64.sub_mod (Obj.magic x) (Obj.magic y))
        | W128  ->
            Obj.repr (FStar_UInt128.sub_mod (Obj.magic x) (Obj.magic y))
  
let (op_Star : signedness -> width -> Obj.t -> Obj.t -> Obj.t) =
  fun s  ->
    fun w  ->
      fun x  ->
        fun y  ->
          match (s, w) with
          | (uu____3979,Winfinite ) ->
              Obj.repr ((Obj.magic x) * (Obj.magic y))
          | (Unsigned ,W8 ) ->
              Obj.repr (FStar_UInt8.mul (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W16 ) ->
              Obj.repr (FStar_UInt16.mul (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W31 ) ->
              Obj.repr (FStar_UInt31.mul (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W32 ) ->
              Obj.repr (FStar_UInt32.mul (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W63 ) ->
              Obj.repr (FStar_UInt63.mul (Obj.magic x) (Obj.magic y))
          | (Unsigned ,W64 ) ->
              Obj.repr (FStar_UInt64.mul (Obj.magic x) (Obj.magic y))
          | (Signed ,W8 ) ->
              Obj.repr (FStar_Int8.mul (Obj.magic x) (Obj.magic y))
          | (Signed ,W16 ) ->
              Obj.repr (FStar_Int16.mul (Obj.magic x) (Obj.magic y))
          | (Signed ,W31 ) ->
              Obj.repr (FStar_Int31.mul (Obj.magic x) (Obj.magic y))
          | (Signed ,W32 ) ->
              Obj.repr (FStar_Int32.mul (Obj.magic x) (Obj.magic y))
          | (Signed ,W63 ) ->
              Obj.repr (FStar_Int63.mul (Obj.magic x) (Obj.magic y))
          | (Signed ,W64 ) ->
              Obj.repr (FStar_Int64.mul (Obj.magic x) (Obj.magic y))
          | (Signed ,W128 ) ->
              Obj.repr (FStar_Int128.mul (Obj.magic x) (Obj.magic y))
  
let (op_Star_Question : width -> Obj.t -> Obj.t -> Obj.t) =
  fun w  ->
    fun x  ->
      fun y  ->
        match w with
        | Winfinite  ->
            Obj.repr
              (match (Unsigned, w) with
               | (uu____4384,Winfinite ) ->
                   Obj.repr ((Obj.magic x) * (Obj.magic y))
               | (Unsigned ,W8 ) ->
                   Obj.repr (FStar_UInt8.mul (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W16 ) ->
                   Obj.repr (FStar_UInt16.mul (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W31 ) ->
                   Obj.repr (FStar_UInt31.mul (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W32 ) ->
                   Obj.repr (FStar_UInt32.mul (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W63 ) ->
                   Obj.repr (FStar_UInt63.mul (Obj.magic x) (Obj.magic y))
               | (Unsigned ,W64 ) ->
                   Obj.repr (FStar_UInt64.mul (Obj.magic x) (Obj.magic y))
               | (Signed ,W8 ) ->
                   Obj.repr (FStar_Int8.mul (Obj.magic x) (Obj.magic y))
               | (Signed ,W16 ) ->
                   Obj.repr (FStar_Int16.mul (Obj.magic x) (Obj.magic y))
               | (Signed ,W31 ) ->
                   Obj.repr (FStar_Int31.mul (Obj.magic x) (Obj.magic y))
               | (Signed ,W32 ) ->
                   Obj.repr (FStar_Int32.mul (Obj.magic x) (Obj.magic y))
               | (Signed ,W63 ) ->
                   Obj.repr (FStar_Int63.mul (Obj.magic x) (Obj.magic y))
               | (Signed ,W64 ) ->
                   Obj.repr (FStar_Int64.mul (Obj.magic x) (Obj.magic y))
               | (Signed ,W128 ) ->
                   Obj.repr (FStar_Int128.mul (Obj.magic x) (Obj.magic y)))
        | W8  ->
            Obj.repr (FStar_UInt8.mul_underspec (Obj.magic x) (Obj.magic y))
        | W16  ->
            Obj.repr (FStar_UInt16.mul_underspec (Obj.magic x) (Obj.magic y))
        | W31  ->
            Obj.repr (FStar_UInt31.mul_underspec (Obj.magic x) (Obj.magic y))
        | W32  ->
            Obj.repr (FStar_UInt32.mul_underspec (Obj.magic x) (Obj.magic y))
        | W63  ->
            Obj.repr (FStar_UInt63.mul_underspec (Obj.magic x) (Obj.magic y))
        | W64  ->
            Obj.repr (FStar_UInt64.mul_underspec (Obj.magic x) (Obj.magic y))
  
let (op_Star_Percent : fixed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun w  ->
    fun x  ->
      fun y  ->
        match w with
        | W8  -> Obj.repr (FStar_UInt8.mul_mod (Obj.magic x) (Obj.magic y))
        | W16  -> Obj.repr (FStar_UInt16.mul_mod (Obj.magic x) (Obj.magic y))
        | W31  -> Obj.repr (FStar_UInt31.mul_mod (Obj.magic x) (Obj.magic y))
        | W32  -> Obj.repr (FStar_UInt32.mul_mod (Obj.magic x) (Obj.magic y))
        | W63  -> Obj.repr (FStar_UInt63.mul_mod (Obj.magic x) (Obj.magic y))
        | W64  -> Obj.repr (FStar_UInt64.mul_mod (Obj.magic x) (Obj.magic y))
  
type nat = Prims.int
type uint_8 = FStar_UInt8.t
type uint_16 = FStar_UInt16.t
type uint_31 = FStar_UInt31.t
type uint_32 = FStar_UInt32.t
type uint_63 = FStar_UInt63.t
type uint_64 = FStar_UInt64.t
type int = Prims.int
type int_8 = FStar_Int8.t
type int_16 = FStar_Int16.t
type int_31 = FStar_Int31.t
type int_32 = FStar_Int32.t
type int_63 = FStar_Int63.t
type int_64 = FStar_Int64.t
type int_128 = FStar_Int128.t
type ('As,'Aw,'Aop,'Ax,'Ay) ok = Obj.t
let (f_int : Prims.int -> Prims.int -> Prims.int) = fun x  -> fun y  -> x + y 
let (f_nat : Prims.int -> Prims.int -> Prims.int) = fun x  -> fun y  -> x + y 
let (f_uint_8 : FStar_UInt8.t -> FStar_UInt8.t -> FStar_UInt8.t) =
  fun x  -> fun y  -> FStar_UInt8.add x y 
let (f_int_16 : FStar_Int16.t -> FStar_Int16.t -> FStar_Int16.t) =
  fun x  -> fun y  -> FStar_Int16.add x y 
let (g : FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x  -> fun y  -> FStar_UInt32.add x (FStar_UInt32.mul y y) 
let (h : Prims.nat -> Prims.nat -> Prims.int) =
  fun x  ->
    fun y  ->
      (Obj.magic (u Unsigned Winfinite x)) +
        (Obj.magic (u Unsigned Winfinite y))
  