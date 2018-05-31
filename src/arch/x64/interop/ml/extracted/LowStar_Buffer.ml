open Prims
type ('Aa,'dummyV0) vec =
  | VNil 
  | VCons of Prims.nat * 'Aa * ('Aa,unit) vec 
let uu___is_VNil : 'Aa . Prims.nat -> ('Aa,unit) vec -> Prims.bool =
  fun uu____78  ->
    fun projectee  ->
      match projectee with | VNil  -> true | uu____90 -> false
  
let uu___is_VCons : 'Aa . Prims.nat -> ('Aa,unit) vec -> Prims.bool =
  fun uu____134  ->
    fun projectee  ->
      match projectee with
      | VCons (n1,vec_hd,vec_tl) -> true
      | uu____156 -> false
  
let __proj__VCons__item__n : 'Aa . Prims.nat -> ('Aa,unit) vec -> Prims.nat =
  fun uu____208  ->
    fun projectee  -> match projectee with | VCons (n1,vec_hd,vec_tl) -> n1
  
let __proj__VCons__item__vec_hd : 'Aa . Prims.nat -> ('Aa,unit) vec -> 'Aa =
  fun uu____268  ->
    fun projectee  ->
      match projectee with | VCons (n1,vec_hd,vec_tl) -> vec_hd
  
let __proj__VCons__item__vec_tl :
  'Aa . Prims.nat -> ('Aa,unit) vec -> ('Aa,unit) vec =
  fun uu____332  ->
    fun projectee  ->
      match projectee with | VCons (n1,vec_hd,vec_tl) -> vec_tl
  
type 'Aa buffer' =
  | Null 
  | Buffer of FStar_UInt32.t * ('Aa,unit) vec FStar_HyperStack_ST.reference *
  FStar_UInt32.t * FStar_UInt32.t 
let uu___is_Null : 'Aa . 'Aa buffer' -> Prims.bool =
  fun projectee  -> match projectee with | Null  -> true | uu____437 -> false 
let uu___is_Buffer : 'Aa . 'Aa buffer' -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Buffer (max_length,content,idx,length1) -> true
    | uu____477 -> false
  
let __proj__Buffer__item__max_length : 'Aa . 'Aa buffer' -> FStar_UInt32.t =
  fun projectee  ->
    match projectee with
    | Buffer (max_length,content,idx,length1) -> max_length
  
let __proj__Buffer__item__content :
  'Aa . 'Aa buffer' -> ('Aa,unit) vec FStar_HyperStack_ST.reference =
  fun projectee  ->
    match projectee with | Buffer (max_length,content,idx,length1) -> content
  
let __proj__Buffer__item__idx : 'Aa . 'Aa buffer' -> FStar_UInt32.t =
  fun projectee  ->
    match projectee with | Buffer (max_length,content,idx,length1) -> idx
  
let __proj__Buffer__item__length : 'Aa . 'Aa buffer' -> FStar_UInt32.t =
  fun projectee  ->
    match projectee with | Buffer (max_length,content,idx,length1) -> length1
  
type 'Aa buffer = 'Aa buffer'

let null : 'Aa . unit -> 'Aa buffer = fun uu____702  -> Null 

type ('Aa,'Ab,'Ah) unused_in = Obj.t
type ('Aa,'Ah,'Ab) live = Obj.t













type ('Aa,'Al) lseq = 'Aa FStar_Seq_Base.seq
let rec lseq_of_vec : 'Aa . Prims.nat -> ('Aa,unit) vec -> ('Aa,unit) lseq =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then FStar_Seq_Base.createEmpty ()
      else
        FStar_Seq_Properties.cons (__proj__VCons__item__vec_hd n1 l)
          (lseq_of_vec
             ((__proj__VCons__item__n n1 l) - (Prims.parse_int "1"))
             (__proj__VCons__item__vec_tl n1 l))
  
let rec vec_of_lseq : 'Aa . Prims.nat -> ('Aa,unit) lseq -> ('Aa,unit) vec =
  fun n1  ->
    fun l  ->
      if n1 = (Prims.parse_int "0")
      then VNil
      else
        VCons
          (n1, (FStar_Seq_Properties.head l),
            (vec_of_lseq (n1 - (Prims.parse_int "1"))
               (FStar_Seq_Properties.tail l)))
  





type ('Aa,'Alarger,'Asmaller) includes = Obj.t












type ('Aa1,'Aa2,'Ab1,'Ab2) disjoint = Obj.t






type 'At pointer = 'At buffer
type 'At pointer_or_null = 'At buffer

type abuffer_ =
  {
  b_max_length: Prims.nat ;
  b_offset: Prims.nat ;
  b_length: Prims.nat }
let (__proj__Mkabuffer___item__b_max_length : abuffer_ -> Prims.nat) =
  fun projectee  ->
    match projectee with
    | { b_max_length = __fname__b_max_length; b_offset = __fname__b_offset;
        b_length = __fname__b_length;_} -> __fname__b_max_length
  
let (__proj__Mkabuffer___item__b_offset : abuffer_ -> Prims.nat) =
  fun projectee  ->
    match projectee with
    | { b_max_length = __fname__b_max_length; b_offset = __fname__b_offset;
        b_length = __fname__b_length;_} -> __fname__b_offset
  
let (__proj__Mkabuffer___item__b_length : abuffer_ -> Prims.nat) =
  fun projectee  ->
    match projectee with
    | { b_max_length = __fname__b_max_length; b_offset = __fname__b_offset;
        b_length = __fname__b_length;_} -> __fname__b_length
  
type ('Aregion,'Aaddr) abuffer' = abuffer_
type ('Aregion,'Aaddr) abuffer = unit

type ('Ar,'Aa,'Ab,'Ah,'Ah') abuffer_preserved' = unit
type ('Ar,'Aa,'Ab,'Ah,'Ah') abuffer_preserved = unit








type ('Alarger,'Asmaller) abuffer_includes' = unit
type ('Ar,'Aa,'Alarger,'Asmaller) abuffer_includes = unit




type ('Ax1,'Ax2) abuffer_disjoint' = unit
type ('Ar,'Aa,'Ab1,'Ab2) abuffer_disjoint = unit




type ('Ah1,'Ah2) modifies_0_preserves_mreferences = unit
type ('Ah1,'Ah2) modifies_0_preserves_regions = unit
type ('Ah1,'Ah2) modifies_0' = unit
type ('Ah1,'Ah2) modifies_0 = unit



type ('Aa,'Ab,'Ah1,'Ah2) modifies_1_preserves_mreferences = unit
type ('Aa,'Ab,'Ah1,'Ah2) modifies_1_preserves_abuffers = unit
type ('Aa,'Ab,'Ah1,'Ah2) modifies_1' = unit
type ('Aa,'Ab,'Ah1,'Ah2) modifies_1 = unit




let is_null : 'Aa . 'Aa buffer -> Prims.bool = fun b  -> uu___is_Null b 
let sub : 'Aa . 'Aa buffer -> FStar_UInt32.t -> FStar_UInt32.t -> 'Aa buffer
  =
  fun b  ->
    fun i  ->
      fun len  ->
        match b with
        | Null  -> Null
        | Buffer (max_len,content,i0,len0) ->
            Buffer (max_len, content, (FStar_UInt32.add i0 i), len)
  
let offset : 'Aa . 'Aa buffer -> FStar_UInt32.t -> 'Aa buffer =
  fun b  ->
    fun i  ->
      match b with
      | Null  -> Null
      | Buffer (max_len,content,i0,len) ->
          Buffer
            (max_len, content, (FStar_UInt32.add i0 i),
              (FStar_UInt32.sub len i))
  
let index : 'Aa . 'Aa buffer -> FStar_UInt32.t -> 'Aa =
  fun b  ->
    fun i  ->
      let s = FStar_HyperStack_ST.op_Bang (__proj__Buffer__item__content b)
         in
      FStar_Seq_Base.index
        (lseq_of_vec (FStar_UInt32.v (__proj__Buffer__item__max_length b)) s)
        ((FStar_UInt32.v (__proj__Buffer__item__idx b)) + (FStar_UInt32.v i))
  
let upd : 'Aa . 'Aa buffer -> FStar_UInt32.t -> 'Aa -> unit =
  fun b  ->
    fun i  ->
      fun v1  ->
        let s0 =
          let uu____2360 =
            FStar_HyperStack_ST.op_Bang (__proj__Buffer__item__content b)  in
          lseq_of_vec (FStar_UInt32.v (__proj__Buffer__item__max_length b))
            uu____2360
           in
        let s =
          FStar_Seq_Base.upd s0
            ((FStar_UInt32.v (__proj__Buffer__item__idx b)) +
               (FStar_UInt32.v i)) v1
           in
        FStar_HyperStack_ST.op_Colon_Equals (__proj__Buffer__item__content b)
          (vec_of_lseq (FStar_UInt32.v (__proj__Buffer__item__max_length b))
             s)
  
type ('Aa,'Ab) recallable' = unit
type ('Aa,'Ab) recallable = unit

let recall : 'Aa . 'Aa buffer -> unit =
  fun b  ->
    if uu___is_Null b
    then ()
    else FStar_HyperStack_ST.recall (__proj__Buffer__item__content b)
  
type ('Aa,'Ab) freeable' = unit
type ('Aa,'Ab) freeable = unit
let free : 'Aa . 'Aa buffer -> unit =
  fun b  -> FStar_HyperStack_ST.rfree (__proj__Buffer__item__content b) 
type ('Aa,'Ar,'Alen,'Ab,'Ah0,'Ah1) alloc_post_common = unit
let alloc_common :
  'Aa .
    FStar_Monotonic_HyperHeap.rid ->
      'Aa -> FStar_UInt32.t -> Prims.bool -> 'Aa buffer
  =
  fun r  ->
    fun init1  ->
      fun len  ->
        fun mm  ->
          let s =
            vec_of_lseq (FStar_UInt32.v len)
              (FStar_Seq_Base.create (FStar_UInt32.v len) init1)
             in
          let content =
            if mm
            then FStar_HyperStack_ST.ralloc_mm r s
            else FStar_HyperStack_ST.ralloc r s  in
          let b =
            Buffer
              (len, content, (FStar_UInt32.uint_to_t (Prims.parse_int "0")),
                len)
             in
          b
  
let gcmalloc :
  'Aa . FStar_Monotonic_HyperHeap.rid -> 'Aa -> FStar_UInt32.t -> 'Aa buffer
  = fun r  -> fun init1  -> fun len  -> alloc_common r init1 len false 
let malloc :
  'Aa . FStar_Monotonic_HyperHeap.rid -> 'Aa -> FStar_UInt32.t -> 'Aa buffer
  = fun r  -> fun init1  -> fun len  -> alloc_common r init1 len true 
let alloca : 'Aa . 'Aa -> FStar_UInt32.t -> 'Aa buffer =
  fun init1  ->
    fun len  ->
      let content =
        FStar_HyperStack_ST.salloc
          (vec_of_lseq (FStar_UInt32.v len)
             (FStar_Seq_Base.create (FStar_UInt32.v len) init1))
         in
      let b =
        Buffer
          (len, content, (FStar_UInt32.uint_to_t (Prims.parse_int "0")), len)
         in
      b
  
type ('Aa,'Ainit) alloca_of_list_pre = unit
type ('Aa,'Alen,'Abuf) alloca_of_list_post = unit
let alloca_of_list : 'Aa . 'Aa Prims.list -> 'Aa buffer =
  fun init1  ->
    let len = FStar_UInt32.uint_to_t (FStar_List_Tot_Base.length init1)  in
    let s = FStar_Seq_Base.of_list init1  in
    let content =
      FStar_HyperStack_ST.salloc (vec_of_lseq (FStar_UInt32.v len) s)  in
    let b =
      Buffer
        (len, content, (FStar_UInt32.uint_to_t (Prims.parse_int "0")), len)
       in
    b
  