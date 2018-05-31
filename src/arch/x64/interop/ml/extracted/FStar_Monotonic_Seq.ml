open Prims
type ('Aa,'As1,'As2) grows = unit
type rid = unit
let snoc : 'a . 'a FStar_Seq_Base.seq -> 'a -> 'a FStar_Seq_Base.seq =
  fun s  ->
    fun x  ->
      FStar_Seq_Base.append s (FStar_Seq_Base.create (Prims.parse_int "1") x)
  

let alloc_mref_seq :
  'Aa .
    rid ->
      'Aa FStar_Seq_Base.seq ->
        (unit,'Aa FStar_Seq_Base.seq,('Aa,unit,unit) grows)
          FStar_HyperStack_ST.m_rref
  = fun r  -> fun init1  -> FStar_HyperStack_ST.ralloc r init1 
type ('Aa,'Ai,'An,'Ax,'Ar,'Ah) at_least = unit

let write_at_end :
  'Aa .
    rid ->
      (unit,'Aa FStar_Seq_Base.seq,('Aa,unit,unit) grows)
        FStar_HyperStack_ST.m_rref -> 'Aa -> unit
  =
  fun i  ->
    fun r  ->
      fun x  ->
        FStar_HyperStack_ST.recall r;
        (let s0 = FStar_HyperStack_ST.op_Bang r  in
         let n = FStar_Seq_Base.length s0  in
         FStar_HyperStack_ST.op_Colon_Equals r
           (FStar_Seq_Properties.snoc s0 x);
         FStar_HyperStack_ST.mr_witness i () () (Obj.magic r) ())
  
type ('Aa,'Ap,'As1,'As2) grows_p = unit
type ('Ar,'Aa,'Ap) i_seq =
  (unit,'Aa FStar_Seq_Base.seq,unit) FStar_HyperStack_ST.m_rref
let alloc_mref_iseq :
  'Aa 'Ap . rid -> 'Aa FStar_Seq_Base.seq -> (unit,'Aa,'Ap) i_seq =
  fun r  -> fun init1  -> FStar_HyperStack_ST.ralloc r init1 
type ('Ar,'Aa,'Ap,'An,'Ax,'Am,'Ah) i_at_least = unit

type ('Ar,'Aa,'Ap,'Ax,'Ais,'Ah) int_at_most = unit


let i_read : 'Aa 'Ap . rid -> (unit,'Aa,'Ap) i_seq -> 'Aa FStar_Seq_Base.seq
  = fun r  -> fun m  -> FStar_HyperStack_ST.op_Bang m 
type ('Ar,'Aa,'Ap,'Am,'Ah) i_contains = unit
let i_write_at_end : 'Aa 'Ap . rid -> (unit,'Aa,'Ap) i_seq -> 'Aa -> unit =
  fun rgn  ->
    fun r  ->
      fun x  ->
        FStar_HyperStack_ST.recall r;
        (let s0 = FStar_HyperStack_ST.op_Bang r  in
         let n = FStar_Seq_Base.length s0  in
         FStar_HyperStack_ST.op_Colon_Equals r
           (FStar_Seq_Properties.snoc s0 x);
         FStar_HyperStack_ST.mr_witness rgn () () (Obj.magic r) ())
  
type 'As invariant = unit
let (test0 :
  rid ->
    (unit,Prims.nat FStar_Seq_Base.seq,(Prims.nat,unit,unit) grows)
      FStar_HyperStack_ST.m_rref -> Prims.nat -> unit)
  =
  fun r  ->
    fun a  ->
      fun k  ->
        let h0 = FStar_HyperStack_ST.get ()  in
        FStar_HyperStack_ST.mr_witness r () () (Obj.magic a) ()
  
let (itest :
  rid -> (unit,Prims.nat,unit invariant) i_seq -> Prims.nat -> unit) =
  fun r  ->
    fun a  ->
      fun k  ->
        let h0 = FStar_HyperStack_ST.get ()  in
        FStar_HyperStack_ST.mr_witness r () () (Obj.magic a) ()
  
let test_alloc : 'Aa 'Ap . rid -> 'Aa FStar_Seq_Base.seq -> unit =
  fun r  ->
    fun init1  ->
      let is = alloc_mref_iseq r init1  in
      let h = FStar_HyperStack_ST.get ()  in ()
  
let un_snoc :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      ('Aa FStar_Seq_Base.seq,'Aa) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    let last1 = (FStar_Seq_Base.length s) - (Prims.parse_int "1")  in
    ((FStar_Seq_Base.slice s (Prims.parse_int "0") last1),
      (FStar_Seq_Base.index s last1))
  
let rec map :
  'a 'b . ('a -> 'b) -> 'a FStar_Seq_Base.seq -> 'b FStar_Seq_Base.seq =
  fun f  ->
    fun s  ->
      if (FStar_Seq_Base.length s) = (Prims.parse_int "0")
      then FStar_Seq_Base.createEmpty ()
      else
        (let uu____4404 = un_snoc s  in
         match uu____4404 with
         | (prefix,last1) ->
             FStar_Seq_Properties.snoc (map f prefix) (f last1))
  

let op_At :
  'Auu____4444 .
    'Auu____4444 FStar_Seq_Base.seq ->
      'Auu____4444 FStar_Seq_Base.seq -> 'Auu____4444 FStar_Seq_Base.seq
  = fun s1  -> fun s2  -> FStar_Seq_Base.append s1 s2 




type ('Aa,'Ab,'Ai,'Ar,'Af,'Abs,'Ah) map_prefix = unit

type ('Aa,'Ab,'Ai,'Ar,'Af,'An,'Av,'Ah) map_has_at_index = unit

let rec collect :
  'a 'b .
    ('a -> 'b FStar_Seq_Base.seq) ->
      'a FStar_Seq_Base.seq -> 'b FStar_Seq_Base.seq
  =
  fun f  ->
    fun s  ->
      if (FStar_Seq_Base.length s) = (Prims.parse_int "0")
      then FStar_Seq_Base.createEmpty ()
      else
        (let uu____4846 = un_snoc s  in
         match uu____4846 with
         | (prefix,last1) ->
             FStar_Seq_Base.append (collect f prefix) (f last1))
  


type ('Aa,'Ab,'Ai,'Ar,'Af,'Abs,'Ah) collect_prefix = unit

type ('Aa,'Ab,'Ai,'Ar,'Af,'An,'Av,'Ah) collect_has_at_index = unit

type ('Ai,'Aa) log_t =
  (unit,'Aa FStar_Seq_Base.seq,unit) FStar_HyperStack_ST.m_rref
type ('Ax,'Ay) increases = unit
type ('Al,'Aa,'Ax,'Alog,'Ah) at_most_log_len = unit
type ('Al,'Aa,'Ai,'Alog,'Amax) seqn_val = Prims.nat
type ('Al,'Aa,'Ai,'Alog,'Amax) seqn =
  (unit,(unit,'Aa,unit,unit,unit) seqn_val,unit) FStar_HyperStack_ST.m_rref

let new_seqn :
  'Aa .
    rid ->
      Prims.nat ->
        rid ->
          Prims.nat -> (unit,'Aa) log_t -> (unit,'Aa,unit,unit,unit) seqn
  =
  fun l  ->
    fun max  ->
      fun i  ->
        fun init1  ->
          fun log  ->
            FStar_HyperStack_ST.recall log;
            FStar_HyperStack_ST.recall_region i;
            FStar_HyperStack_ST.mr_witness l () () (Obj.magic log) ();
            FStar_HyperStack_ST.ralloc i init1
  
let increment_seqn :
  'Aa .
    rid ->
      Prims.nat ->
        rid -> (unit,'Aa) log_t -> (unit,'Aa,unit,unit,unit) seqn -> unit
  =
  fun l  ->
    fun max  ->
      fun i  ->
        fun log  ->
          fun c  ->
            FStar_HyperStack_ST.recall c;
            FStar_HyperStack_ST.recall log;
            (let n =
               let uu____11464 = FStar_HyperStack_ST.op_Bang c  in
               uu____11464 + (Prims.parse_int "1")  in
             FStar_HyperStack_ST.mr_witness l () () (Obj.magic log) ();
             FStar_HyperStack_ST.op_Colon_Equals c n)
  
let testify_seqn :
  'Aa .
    rid ->
      rid ->
        (unit,'Aa) log_t ->
          Prims.nat -> (unit,'Aa,unit,unit,unit) seqn -> unit
  =
  fun i  ->
    fun l  ->
      fun log  ->
        fun max  ->
          fun ctr  -> let n = FStar_HyperStack_ST.op_Bang ctr  in ()
  
