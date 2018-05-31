open Prims
type 'An fin = Prims.int
type ('An,'Aa) vect = 'Aa Prims.list
type ('An,'Aa) seqn = 'Aa FStar_Seq_Base.seq
type ('Aa,'As) in_ = Prims.nat
let rec find :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      ('Aa -> Prims.bool) ->
        Prims.nat -> Prims.nat FStar_Pervasives_Native.option
  =
  fun s  ->
    fun p  ->
      fun i  ->
        if p (FStar_Seq_Base.index s i)
        then FStar_Pervasives_Native.Some i
        else
          if (i + (Prims.parse_int "1")) < (FStar_Seq_Base.length s)
          then find s p (i + (Prims.parse_int "1"))
          else FStar_Pervasives_Native.None
  
let rec (pigeonhole :
  Prims.nat ->
    unit fin FStar_Seq_Base.seq ->
      ((unit fin,unit) in_,(unit fin,unit) in_)
        FStar_Pervasives_Native.tuple2)
  =
  fun n  ->
    fun s  ->
      if n = (Prims.parse_int "0")
      then Obj.magic (failwith "unreachable")
      else
        if n = (Prims.parse_int "1")
        then ((Prims.parse_int "0"), (Prims.parse_int "1"))
        else
          (let k0 = FStar_Seq_Base.index s (Prims.parse_int "0")  in
           match find s (fun k  -> k = k0) (Prims.parse_int "1") with
           | FStar_Pervasives_Native.Some i -> ((Prims.parse_int "0"), i)
           | FStar_Pervasives_Native.None  ->
               let reduced_s =
                 FStar_Seq_Base.init n
                   (fun i  ->
                      let k =
                        FStar_Seq_Base.index s (i + (Prims.parse_int "1"))
                         in
                      if k < k0 then k else k - (Prims.parse_int "1"))
                  in
               let uu____538 =
                 pigeonhole (n - (Prims.parse_int "1")) reduced_s  in
               (match uu____538 with
                | (i1,i2) ->
                    ((i1 + (Prims.parse_int "1")),
                      (i2 + (Prims.parse_int "1")))))
  