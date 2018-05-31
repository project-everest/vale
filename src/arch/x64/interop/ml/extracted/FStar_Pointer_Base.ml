open Prims
type base_typ =
  | TUInt 
  | TUInt8 
  | TUInt16 
  | TUInt32 
  | TUInt64 
  | TInt 
  | TInt8 
  | TInt16 
  | TInt32 
  | TInt64 
  | TChar 
  | TBool 
  | TUnit 
let (uu___is_TUInt : base_typ -> Prims.bool) =
  fun projectee  -> match projectee with | TUInt  -> true | uu____8 -> false 
let (uu___is_TUInt8 : base_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUInt8  -> true | uu____16 -> false
  
let (uu___is_TUInt16 : base_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUInt16  -> true | uu____24 -> false
  
let (uu___is_TUInt32 : base_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUInt32  -> true | uu____32 -> false
  
let (uu___is_TUInt64 : base_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUInt64  -> true | uu____40 -> false
  
let (uu___is_TInt : base_typ -> Prims.bool) =
  fun projectee  -> match projectee with | TInt  -> true | uu____48 -> false 
let (uu___is_TInt8 : base_typ -> Prims.bool) =
  fun projectee  -> match projectee with | TInt8  -> true | uu____56 -> false 
let (uu___is_TInt16 : base_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt16  -> true | uu____64 -> false
  
let (uu___is_TInt32 : base_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt32  -> true | uu____72 -> false
  
let (uu___is_TInt64 : base_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt64  -> true | uu____80 -> false
  
let (uu___is_TChar : base_typ -> Prims.bool) =
  fun projectee  -> match projectee with | TChar  -> true | uu____88 -> false 
let (uu___is_TBool : base_typ -> Prims.bool) =
  fun projectee  -> match projectee with | TBool  -> true | uu____96 -> false 
let (uu___is_TUnit : base_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____104 -> false
  
type array_length_t = FStar_UInt32.t
type typ =
  | TBase of base_typ 
  | TStruct of struct_typ 
  | TUnion of struct_typ 
  | TArray of array_length_t * typ 
  | TPointer of typ 
  | TNPointer of typ 
  | TBuffer of typ 
and struct_typ =
  {
  name: Prims.string ;
  fields: (Prims.string,typ) FStar_Pervasives_Native.tuple2 Prims.list }
let (uu___is_TBase : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBase b -> true | uu____189 -> false
  
let (__proj__TBase__item__b : typ -> base_typ) =
  fun projectee  -> match projectee with | TBase b -> b 
let (uu___is_TStruct : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TStruct l -> true | uu____209 -> false
  
let (__proj__TStruct__item__l : typ -> struct_typ) =
  fun projectee  -> match projectee with | TStruct l -> l 
let (uu___is_TUnion : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnion l -> true | uu____229 -> false
  
let (__proj__TUnion__item__l : typ -> struct_typ) =
  fun projectee  -> match projectee with | TUnion l -> l 
let (uu___is_TArray : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArray (length1,t) -> true | uu____251 -> false
  
let (__proj__TArray__item__length : typ -> array_length_t) =
  fun projectee  -> match projectee with | TArray (length1,t) -> length1 
let (__proj__TArray__item__t : typ -> typ) =
  fun projectee  -> match projectee with | TArray (length1,t) -> t 
let (uu___is_TPointer : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TPointer t -> true | uu____291 -> false
  
let (__proj__TPointer__item__t : typ -> typ) =
  fun projectee  -> match projectee with | TPointer t -> t 
let (uu___is_TNPointer : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TNPointer t -> true | uu____311 -> false
  
let (__proj__TNPointer__item__t : typ -> typ) =
  fun projectee  -> match projectee with | TNPointer t -> t 
let (uu___is_TBuffer : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuffer t -> true | uu____331 -> false
  
let (__proj__TBuffer__item__t : typ -> typ) =
  fun projectee  -> match projectee with | TBuffer t -> t 
let (__proj__Mkstruct_typ__item__name : struct_typ -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; fields = __fname__fields;_} -> __fname__name
  
let (__proj__Mkstruct_typ__item__fields :
  struct_typ -> (Prims.string,typ) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; fields = __fname__fields;_} -> __fname__fields
  
type struct_typ' =
  (Prims.string,typ) FStar_Pervasives_Native.tuple2 Prims.list
type union_typ = struct_typ
type 'Al struct_field' = Prims.string
type 'Al struct_field = unit struct_field'
type 'Al union_field = unit struct_field
let (typ_of_struct_field' : struct_typ' -> unit struct_field' -> typ) =
  fun l  ->
    fun f  ->
      let y =
        FStar_Pervasives_Native.__proj__Some__item__v
          (FStar_List_Tot_Base.assoc f l)
         in
      y
  
let (typ_of_struct_field : struct_typ -> unit struct_field -> typ) =
  fun l  -> fun f  -> typ_of_struct_field' l.fields f 
let (typ_of_union_field : union_typ -> unit union_field -> typ) =
  fun l  -> fun f  -> typ_of_struct_field l f 


type ('dummyV0,'dummyV1) step =
  | StepField of struct_typ * unit struct_field 
  | StepUField of union_typ * unit struct_field 
  | StepCell of FStar_UInt32.t * typ * FStar_UInt32.t 
let (uu___is_StepField : typ -> typ -> (unit,unit) step -> Prims.bool) =
  fun from  ->
    fun to_1089  ->
      fun projectee  ->
        match projectee with | StepField (l,fd) -> true | uu____1100 -> false
  
let (__proj__StepField__item__l :
  typ -> typ -> (unit,unit) step -> struct_typ) =
  fun from  ->
    fun to_1129  ->
      fun projectee  -> match projectee with | StepField (l,fd) -> l
  
let (__proj__StepField__item__fd :
  typ -> typ -> (unit,unit) step -> unit struct_field) =
  fun from  ->
    fun to_1203  ->
      fun projectee  -> match projectee with | StepField (l,fd) -> fd
  
let (uu___is_StepUField : typ -> typ -> (unit,unit) step -> Prims.bool) =
  fun from  ->
    fun to_1258  ->
      fun projectee  ->
        match projectee with
        | StepUField (l,fd) -> true
        | uu____1269 -> false
  
let (__proj__StepUField__item__l :
  typ -> typ -> (unit,unit) step -> union_typ) =
  fun from  ->
    fun to_1298  ->
      fun projectee  -> match projectee with | StepUField (l,fd) -> l
  
let (__proj__StepUField__item__fd :
  typ -> typ -> (unit,unit) step -> unit struct_field) =
  fun from  ->
    fun to_1372  ->
      fun projectee  -> match projectee with | StepUField (l,fd) -> fd
  
let (uu___is_StepCell : typ -> typ -> (unit,unit) step -> Prims.bool) =
  fun from  ->
    fun to_1429  ->
      fun projectee  ->
        match projectee with
        | StepCell (length1,value,index1) -> true
        | uu____1439 -> false
  
let (__proj__StepCell__item__length :
  typ -> typ -> (unit,unit) step -> FStar_UInt32.t) =
  fun from  ->
    fun to_1470  ->
      fun projectee  ->
        match projectee with | StepCell (length1,value,index1) -> length1
  
let (__proj__StepCell__item__value : typ -> typ -> (unit,unit) step -> typ) =
  fun from  ->
    fun to_1506  ->
      fun projectee  ->
        match projectee with | StepCell (length1,value,index1) -> value
  
let (__proj__StepCell__item__index :
  typ -> typ -> (unit,unit) step -> FStar_UInt32.t) =
  fun from  ->
    fun to_1545  ->
      fun projectee  ->
        match projectee with | StepCell (length1,value,index1) -> index1
  
type ('Afrom,'dummyV0) path =
  | PathBase 
  | PathStep of typ * typ * (unit,unit) path * (unit,unit) step 
let (uu___is_PathBase : typ -> typ -> (unit,unit) path -> Prims.bool) =
  fun from  ->
    fun to_1617  ->
      fun projectee  ->
        match projectee with | PathBase  -> true | uu____1623 -> false
  
let (uu___is_PathStep : typ -> typ -> (unit,unit) path -> Prims.bool) =
  fun from  ->
    fun to_1653  ->
      fun projectee  ->
        match projectee with
        | PathStep (through,to_1660,p,s) -> true
        | uu____1671 -> false
  
let (__proj__PathStep__item__through : typ -> typ -> (unit,unit) path -> typ)
  =
  fun from  ->
    fun to_1702  ->
      fun projectee  ->
        match projectee with | PathStep (through,to_1709,p,s) -> through
  
let (__proj__PathStep__item__to : typ -> typ -> (unit,unit) path -> typ) =
  fun from  ->
    fun to_1746  ->
      fun projectee  ->
        match projectee with | PathStep (through,to_1753,p,s) -> to_1753
  
let (__proj__PathStep__item__p :
  typ -> typ -> (unit,unit) path -> (unit,unit) path) =
  fun from  ->
    fun to_1794  ->
      fun projectee  ->
        match projectee with | PathStep (through,to_1805,p,s) -> p
  
let (__proj__PathStep__item__s :
  typ -> typ -> (unit,unit) path -> (unit,unit) step) =
  fun from  ->
    fun to_1846  ->
      fun projectee  ->
        match projectee with | PathStep (through,to_1857,p,s) -> s
  


type 'Ato_1892 _npointer =
  | Pointer of typ * FStar_Monotonic_HyperStack.aref * (unit,unit) path 
  | NullPtr 
let (uu___is_Pointer : typ -> unit _npointer -> Prims.bool) =
  fun to_1934  ->
    fun projectee  ->
      match projectee with
      | Pointer (from,contents,p) -> true
      | uu____1945 -> false
  
let (__proj__Pointer__item__from : typ -> unit _npointer -> typ) =
  fun to_1965  ->
    fun projectee  ->
      match projectee with | Pointer (from,contents,p) -> from
  
let (__proj__Pointer__item__contents :
  typ -> unit _npointer -> FStar_Monotonic_HyperStack.aref) =
  fun to_1993  ->
    fun projectee  ->
      match projectee with | Pointer (from,contents,p) -> contents
  
let (__proj__Pointer__item__p : typ -> unit _npointer -> (unit,unit) path) =
  fun to_2025  ->
    fun projectee  -> match projectee with | Pointer (from,contents,p) -> p
  
let (uu___is_NullPtr : typ -> unit _npointer -> Prims.bool) =
  fun to_2053  ->
    fun projectee  ->
      match projectee with | NullPtr  -> true | uu____2057 -> false
  
type 'At npointer = unit _npointer
let (nullptr : typ -> unit npointer) = fun t  -> NullPtr 


type 'At pointer = unit npointer

type 'At buffer_root =
  | BufferRootSingleton of unit pointer 
  | BufferRootArray of array_length_t * unit pointer 
let (uu___is_BufferRootSingleton : typ -> unit buffer_root -> Prims.bool) =
  fun t  ->
    fun projectee  ->
      match projectee with
      | BufferRootSingleton p -> true
      | uu____2195 -> false
  
let (__proj__BufferRootSingleton__item__p :
  typ -> unit buffer_root -> unit pointer) =
  fun t  ->
    fun projectee  -> match projectee with | BufferRootSingleton p -> p
  
let (uu___is_BufferRootArray : typ -> unit buffer_root -> Prims.bool) =
  fun t  ->
    fun projectee  ->
      match projectee with
      | BufferRootArray (max_length,p) -> true
      | uu____2265 -> false
  
let (__proj__BufferRootArray__item__max_length :
  typ -> unit buffer_root -> array_length_t) =
  fun t  ->
    fun projectee  ->
      match projectee with | BufferRootArray (max_length,p) -> max_length
  
let (__proj__BufferRootArray__item__p :
  typ -> unit buffer_root -> unit pointer) =
  fun t  ->
    fun projectee  ->
      match projectee with | BufferRootArray (max_length,p) -> p
  
let (buffer_root_length : typ -> unit buffer_root -> FStar_UInt32.t) =
  fun t  ->
    fun b  ->
      match Obj.magic b with
      | BufferRootSingleton uu____2359 ->
          FStar_UInt32.uint_to_t (Prims.parse_int "1")
      | BufferRootArray (len,uu____2365) -> len
  
type 'At _buffer =
  | Buffer of unit buffer_root * FStar_UInt32.t * FStar_UInt32.t 
let (uu___is_Buffer : typ -> unit _buffer -> Prims.bool) =
  fun t  -> fun projectee  -> true 
let (__proj__Buffer__item__broot : typ -> unit _buffer -> unit buffer_root) =
  fun t  ->
    fun projectee  ->
      match projectee with | Buffer (broot,bidx,blength) -> broot
  
let (__proj__Buffer__item__bidx : typ -> unit _buffer -> FStar_UInt32.t) =
  fun t  ->
    fun projectee  ->
      match projectee with | Buffer (broot,bidx,blength) -> bidx
  
let (__proj__Buffer__item__blength : typ -> unit _buffer -> FStar_UInt32.t) =
  fun t  ->
    fun projectee  ->
      match projectee with | Buffer (broot,bidx,blength) -> blength
  
type 'At buffer = unit _buffer
type 'At type_of_base_typ = Obj.t
type ('Alength,'At) array = 'At FStar_Seq_Base.seq
type ('Al,'Atype_of_typ,'Af) type_of_struct_field'' = 'Atype_of_typ
type ('Al,'Atype_of_typ,'Af) type_of_struct_field' =
  (unit,'Atype_of_typ,unit) type_of_struct_field''
type ('Akey,'Avalue) gtdata = ('Akey,'Avalue) Prims.dtuple2
let _gtdata_get_key : 'Akey 'Avalue . ('Akey,'Avalue) gtdata -> 'Akey =
  fun u  -> FStar_Pervasives.dfst u 

let gtdata_get_value :
  'Akey 'Avalue . ('Akey,'Avalue) gtdata -> 'Akey -> 'Avalue =
  fun u  ->
    fun k  ->
      let uu____2822 = u  in
      match uu____2822 with | Prims.Mkdtuple2 (uu____2840,v1) -> v1
  
let gtdata_create :
  'Akey 'Avalue . 'Akey -> 'Avalue -> ('Akey,'Avalue) gtdata =
  fun k  -> fun v1  -> Prims.Mkdtuple2 (k, v1) 




type ('Al,'Auu____2960) type_of_struct_field = unit



let (_union_get_key :
  union_typ -> (Prims.string,Obj.t) Prims.dtuple2 -> unit struct_field) =
  fun l  -> fun v1  -> _gtdata_get_key (Obj.magic v1) 
let (struct_sel :
  struct_typ ->
    (Prims.string,Obj.t) FStar_DependentMap.t ->
      unit struct_field -> (unit,unit) type_of_struct_field)
  = fun l  -> fun s  -> fun f  -> FStar_DependentMap.sel (Obj.magic s) f 
let (dfst_struct_field :
  struct_typ ->
    (unit struct_field,(unit,unit) type_of_struct_field) Prims.dtuple2 ->
      Prims.string)
  =
  fun s  ->
    fun p  ->
      let uu____6501 = p  in
      match uu____6501 with | Prims.Mkdtuple2 (f,uu____6588) -> f
  
type 'As struct_literal = (unit struct_field,unit) Prims.dtuple2 Prims.list
let (struct_literal_wf : struct_typ -> unit struct_literal -> Prims.bool) =
  fun s  ->
    fun l  ->
      (FStar_List_Tot_Base.sortWith FStar_String.compare
         (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst s.fields))
        =
        (FStar_List_Tot_Base.sortWith FStar_String.compare
           (FStar_List_Tot_Base.map (dfst_struct_field s) l))
  
let (fun_of_list :
  struct_typ ->
    unit struct_literal ->
      unit struct_field -> (unit,unit) type_of_struct_field)
  =
  fun s  ->
    fun l  ->
      fun f  ->
        let f' = f  in
        let phi p = (dfst_struct_field s p) = f'  in
        match FStar_List_Tot_Base.find phi l with
        | FStar_Pervasives_Native.Some p ->
            let uu____8417 = p  in
            (match uu____8417 with | Prims.Mkdtuple2 (uu____8556,v1) -> v1)
        | uu____8769 -> FStar_Pervasives.false_elim ()
  
let (struct_upd :
  struct_typ ->
    (Prims.string,Obj.t) FStar_DependentMap.t ->
      unit struct_field ->
        (unit,unit) type_of_struct_field ->
          (Prims.string,Obj.t) FStar_DependentMap.t)
  =
  fun l  ->
    fun s  ->
      fun f  ->
        fun v1  -> Obj.magic (FStar_DependentMap.upd (Obj.magic s) f v1)
  
let (struct_create_fun :
  struct_typ ->
    (unit struct_field -> (unit,unit) type_of_struct_field) ->
      (Prims.string,Obj.t) FStar_DependentMap.t)
  = fun l  -> fun f  -> Obj.magic (FStar_DependentMap.create f) 
let (struct_create :
  struct_typ ->
    unit struct_literal -> (Prims.string,Obj.t) FStar_DependentMap.t)
  = fun s  -> fun l  -> struct_create_fun s (fun_of_list s l) 



let (union_get_value :
  union_typ ->
    (Prims.string,Obj.t) Prims.dtuple2 ->
      unit struct_field -> (unit,unit) type_of_struct_field)
  = fun l  -> fun v1  -> fun fd  -> gtdata_get_value (Obj.magic v1) fd 
let (union_create :
  union_typ ->
    unit struct_field ->
      (unit,unit) type_of_struct_field -> (Prims.string,Obj.t) Prims.dtuple2)
  =
  fun a167  ->
    fun a168  ->
      fun a169  ->
        (Obj.magic (fun l  -> fun fd  -> fun v1  -> gtdata_create fd v1))
          a167 a168 a169
  
let rec (dummy_val : typ -> Obj.t) =
  fun t  ->
    match t with
    | TBase b ->
        Obj.repr
          (match b with
           | TUInt  -> Obj.repr (Prims.parse_int "0")
           | TUInt8  ->
               Obj.repr (FStar_UInt8.uint_to_t (Prims.parse_int "0"))
           | TUInt16  ->
               Obj.repr (FStar_UInt16.uint_to_t (Prims.parse_int "0"))
           | TUInt32  ->
               Obj.repr (FStar_UInt32.uint_to_t (Prims.parse_int "0"))
           | TUInt64  ->
               Obj.repr (FStar_UInt64.uint_to_t (Prims.parse_int "0"))
           | TInt  -> Obj.repr (Prims.parse_int "0")
           | TInt8  -> Obj.repr (FStar_Int8.int_to_t (Prims.parse_int "0"))
           | TInt16  -> Obj.repr (FStar_Int16.int_to_t (Prims.parse_int "0"))
           | TInt32  -> Obj.repr (FStar_Int32.int_to_t (Prims.parse_int "0"))
           | TInt64  -> Obj.repr (FStar_Int64.int_to_t (Prims.parse_int "0"))
           | TChar  -> Obj.repr 99
           | TBool  -> Obj.repr false
           | TUnit  -> Obj.repr ())
    | TStruct l ->
        Obj.repr
          (struct_create_fun l
             (fun a170  ->
                (Obj.magic (fun f  -> dummy_val (typ_of_struct_field l f)))
                  a170))
    | TUnion l ->
        Obj.repr
          (let dummy_field =
             FStar_List_Tot_Base.hd
               (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l.fields)
              in
           union_create l dummy_field
             (Obj.magic (dummy_val (typ_of_struct_field l dummy_field))))
    | TArray (length1,t1) ->
        Obj.repr
          (FStar_Seq_Base.create (FStar_UInt32.v length1) (dummy_val t1))
    | TPointer t1 ->
        Obj.repr
          (Pointer (t1, FStar_Monotonic_HyperStack.dummy_aref, PathBase))
    | TNPointer t1 -> Obj.repr NullPtr
    | TBuffer t1 ->
        Obj.repr
          (Buffer
             ((BufferRootSingleton
                 (Pointer
                    (t1, FStar_Monotonic_HyperStack.dummy_aref, PathBase))),
               (FStar_UInt32.uint_to_t (Prims.parse_int "0")),
               (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
  

type ('Al,'Auu____18957) otype_of_struct_field = unit



type 'Al ostruct =
  (unit struct_field,unit) FStar_DependentMap.t
    FStar_Pervasives_Native.option
let (ostruct_sel :
  struct_typ ->
    unit ostruct -> unit struct_field -> (unit,unit) otype_of_struct_field)
  =
  fun l  ->
    fun s  ->
      fun f  ->
        FStar_DependentMap.sel
          (FStar_Pervasives_Native.__proj__Some__item__v s) f
  
let (ostruct_upd :
  struct_typ ->
    unit ostruct ->
      unit struct_field -> (unit,unit) otype_of_struct_field -> unit ostruct)
  =
  fun l  ->
    fun s  ->
      fun f  ->
        fun v1  ->
          FStar_Pervasives_Native.Some
            (FStar_DependentMap.upd
               (FStar_Pervasives_Native.__proj__Some__item__v s) f v1)
  
let (ostruct_create :
  struct_typ ->
    (unit struct_field -> (unit,unit) otype_of_struct_field) -> unit ostruct)
  =
  fun l  ->
    fun f  -> FStar_Pervasives_Native.Some (FStar_DependentMap.create f)
  

type 'Al ounion =
  (unit struct_field,unit) gtdata FStar_Pervasives_Native.option
let (ounion_get_key : union_typ -> unit ounion -> unit struct_field) =
  fun l  ->
    fun v1  ->
      _gtdata_get_key (FStar_Pervasives_Native.__proj__Some__item__v v1)
  
let (ounion_get_value :
  union_typ ->
    unit ounion -> unit struct_field -> (unit,unit) otype_of_struct_field)
  =
  fun l  ->
    fun v1  ->
      fun fd  ->
        gtdata_get_value (FStar_Pervasives_Native.__proj__Some__item__v v1)
          fd
  
let (ounion_create :
  union_typ ->
    unit struct_field -> (unit,unit) otype_of_struct_field -> unit ounion)
  =
  fun l  ->
    fun fd  -> fun v1  -> FStar_Pervasives_Native.Some (gtdata_create fd v1)
  

let (struct_field_is_readable :
  struct_typ ->
    (typ -> Obj.t -> Prims.bool) ->
      unit ostruct -> Prims.string -> Prims.bool)
  =
  fun l  ->
    fun ovalue_is_readable  ->
      fun v1  ->
        fun s  ->
          if
            FStar_List_Tot_Base.mem s
              (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l.fields)
          then ovalue_is_readable (typ_of_struct_field l s) (Obj.repr ())
          else true
  
let rec (ovalue_is_readable : typ -> Obj.t -> Prims.bool) =
  fun t  ->
    fun v1  ->
      match t with
      | TStruct l ->
          let v2 = Obj.magic v1  in
          (FStar_Pervasives_Native.uu___is_Some v2) &&
            (let keys =
               FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l.fields
                in
             let pred t' v3 = ovalue_is_readable t' v3  in
             FStar_List_Tot_Base.for_all (struct_field_is_readable l pred v2)
               keys)
      | TUnion l ->
          let v2 = Obj.magic v1  in
          (FStar_Pervasives_Native.uu___is_Some v2) &&
            (let k = ounion_get_key l v2  in
             ovalue_is_readable (typ_of_struct_field l k) (Obj.repr ()))
      | TArray (len,t1) ->
          let v2 = Obj.magic v1  in
          (FStar_Pervasives_Native.uu___is_Some v2) &&
            (FStar_Seq_Properties.for_all (ovalue_is_readable t1)
               (Obj.magic (FStar_Pervasives_Native.__proj__Some__item__v v2)))
      | TBase t1 ->
          let v2 = Obj.magic v1  in FStar_Pervasives_Native.uu___is_Some v2
      | TPointer t1 ->
          let v2 = Obj.magic v1  in FStar_Pervasives_Native.uu___is_Some v2
      | TNPointer t1 ->
          let v2 = Obj.magic v1  in FStar_Pervasives_Native.uu___is_Some v2
      | TBuffer t1 ->
          let v2 = Obj.magic v1  in FStar_Pervasives_Native.uu___is_Some v2
  





let (ostruct_field_of_struct_field :
  struct_typ ->
    (typ -> Obj.t -> Obj.t) ->
      (Prims.string,Obj.t) FStar_DependentMap.t ->
        unit struct_field -> (unit,unit) otype_of_struct_field)
  =
  fun l  ->
    fun ovalue_of_value  ->
      fun v1  ->
        fun f  ->
          Obj.magic (ovalue_of_value (typ_of_struct_field l f) (Obj.repr ()))
  

let rec (ovalue_of_value : typ -> Obj.t -> Obj.t) =
  fun t  ->
    fun v1  ->
      match t with
      | TStruct l ->
          Obj.repr
            (let oval t' v' = ovalue_of_value t' v'  in
             ostruct_create l
               (ostruct_field_of_struct_field l oval (Obj.magic v1)))
      | TArray (len,t1) ->
          Obj.repr
            (let v2 = Obj.magic v1  in
             let f i =
               ovalue_of_value t1 (FStar_Seq_Base.index (Obj.magic v2) i)  in
             let v' = Obj.magic (FStar_Seq_Base.init (FStar_UInt32.v len) f)
                in
             FStar_Pervasives_Native.Some v')
      | TUnion l ->
          Obj.repr
            (let v2 = Obj.magic v1  in
             let k = _union_get_key l v2  in
             ounion_create l k
               (Obj.magic
                  (ovalue_of_value (typ_of_struct_field l k) (Obj.repr ()))))
      | uu____27573 -> Obj.repr (FStar_Pervasives_Native.Some v1)
  


let rec (value_of_ovalue : typ -> Obj.t -> Obj.t) =
  fun t  ->
    fun v1  ->
      match t with
      | TStruct l ->
          let v2 = Obj.magic v1  in
          if FStar_Pervasives_Native.uu___is_Some v2
          then
            Obj.repr
              (let phi f =
                 Obj.magic
                   (value_of_ovalue (typ_of_struct_field l f) (Obj.repr ()))
                  in
               struct_create_fun l phi)
          else Obj.repr (dummy_val t)
      | TArray (len,t') ->
          let v2 = Obj.magic v1  in
          (match v2 with
           | FStar_Pervasives_Native.None  -> Obj.repr (dummy_val t)
           | FStar_Pervasives_Native.Some v3 ->
               Obj.repr
                 (let phi i =
                    value_of_ovalue t'
                      (FStar_Seq_Base.index (Obj.magic v3) i)
                     in
                  FStar_Seq_Base.init (FStar_UInt32.v len) phi))
      | TUnion l ->
          let v2 = Obj.magic v1  in
          (match v2 with
           | FStar_Pervasives_Native.None  -> Obj.repr (dummy_val t)
           | uu____28922 ->
               Obj.repr
                 (let k = ounion_get_key l v2  in
                  union_create l k
                    (Obj.magic
                       (value_of_ovalue (typ_of_struct_field l k)
                          (Obj.repr ())))))
      | TBase b ->
          let v2 = Obj.magic v1  in
          (match v2 with
           | FStar_Pervasives_Native.None  -> dummy_val t
           | FStar_Pervasives_Native.Some v3 -> v3)
      | TPointer t' ->
          let v2 = Obj.magic v1  in
          (match v2 with
           | FStar_Pervasives_Native.None  -> Obj.repr (dummy_val t)
           | FStar_Pervasives_Native.Some v3 -> Obj.repr v3)
      | TNPointer t' ->
          let v2 = Obj.magic v1  in
          (match v2 with
           | FStar_Pervasives_Native.None  -> Obj.repr (dummy_val t)
           | FStar_Pervasives_Native.Some v3 -> Obj.repr v3)
      | TBuffer t' ->
          let v2 = Obj.magic v1  in
          (match v2 with
           | FStar_Pervasives_Native.None  -> Obj.repr (dummy_val t)
           | FStar_Pervasives_Native.Some v3 -> Obj.repr v3)
  



let (none_ovalue : typ -> Obj.t) =
  fun t  ->
    match t with
    | TStruct l -> Obj.repr FStar_Pervasives_Native.None
    | TArray (len,t') -> Obj.repr FStar_Pervasives_Native.None
    | TUnion l -> Obj.repr FStar_Pervasives_Native.None
    | TBase b -> Obj.repr FStar_Pervasives_Native.None
    | TPointer t' -> Obj.repr FStar_Pervasives_Native.None
    | TNPointer t' -> Obj.repr FStar_Pervasives_Native.None
    | TBuffer t' -> Obj.repr FStar_Pervasives_Native.None
  

let (step_sel : typ -> typ -> Obj.t -> (unit,unit) step -> Obj.t) =
  fun from  ->
    fun to_29830  ->
      fun m'  ->
        fun s  ->
          match s with
          | StepField (l,fd) ->
              let m'1 = Obj.magic m'  in
              (match m'1 with
               | FStar_Pervasives_Native.None  ->
                   Obj.repr (none_ovalue to_29830)
               | uu____30020 -> Obj.repr (ostruct_sel l m'1 fd))
          | StepUField (l,fd) ->
              let m'1 = Obj.magic m'  in
              (match m'1 with
               | FStar_Pervasives_Native.None  -> none_ovalue to_29830
               | uu____30291 ->
                   if fd = (ounion_get_key l m'1)
                   then Obj.repr (ounion_get_value l m'1 fd)
                   else Obj.repr (none_ovalue to_29830))
          | StepCell (length1,value,i) ->
              let m'1 = Obj.magic m'  in
              (match m'1 with
               | FStar_Pervasives_Native.None  -> none_ovalue to_29830
               | FStar_Pervasives_Native.Some m'2 ->
                   FStar_Seq_Base.index (Obj.magic m'2) (FStar_UInt32.v i))
  




let rec (path_sel : typ -> typ -> Obj.t -> (unit,unit) path -> Obj.t) =
  fun from  ->
    fun to_30845  ->
      fun m  ->
        fun p  ->
          match p with
          | PathBase  -> m
          | PathStep (through',to',p',s) ->
              let m' = path_sel from through' m p'  in
              step_sel through' to' m' s
  

let (step_upd : typ -> typ -> Obj.t -> (unit,unit) step -> Obj.t -> Obj.t) =
  fun from  ->
    fun to_31180  ->
      fun m  ->
        fun s  ->
          fun v1  ->
            match s with
            | StepField (l,fd) ->
                Obj.repr
                  (let m1 = Obj.magic m  in
                   Obj.magic
                     (match m1 with
                      | FStar_Pervasives_Native.None  ->
                          let phi fd' =
                            Obj.magic
                              (if fd' = fd
                               then v1
                               else none_ovalue (typ_of_struct_field l fd'))
                             in
                          ostruct_create l phi
                      | FStar_Pervasives_Native.Some uu____31871 ->
                          ostruct_upd l m1 fd (Obj.magic v1)))
            | StepCell (len,uu____32097,i) ->
                Obj.repr
                  (let m1 = Obj.magic m  in
                   Obj.magic
                     (match m1 with
                      | FStar_Pervasives_Native.None  ->
                          let phi j =
                            if j = (FStar_UInt32.v i)
                            then v1
                            else none_ovalue to_31180  in
                          let m' =
                            FStar_Pervasives_Native.Some
                              (Obj.magic
                                 (FStar_Seq_Base.init (FStar_UInt32.v len)
                                    phi))
                             in
                          m'
                      | FStar_Pervasives_Native.Some m2 ->
                          let m' =
                            FStar_Pervasives_Native.Some
                              (Obj.magic
                                 (FStar_Seq_Base.upd (Obj.magic m2)
                                    (FStar_UInt32.v i) v1))
                             in
                          m'))
            | StepUField (l,fd) ->
                Obj.repr (ounion_create l fd (Obj.magic v1))
  

let rec (path_upd :
  typ -> typ -> Obj.t -> (unit,unit) path -> Obj.t -> Obj.t) =
  fun from  ->
    fun to_32598  ->
      fun m  ->
        fun p  ->
          fun v1  ->
            match p with
            | PathBase  -> v1
            | PathStep (through',to',p',st) ->
                let s = path_sel from through' m p'  in
                path_upd from through' m p' (step_upd through' to' s st v1)
  

let rec (path_concat :
  typ ->
    typ -> typ -> (unit,unit) path -> (unit,unit) path -> (unit,unit) path)
  =
  fun from  ->
    fun through  ->
      fun to_32887  ->
        fun p  ->
          fun q  ->
            match q with
            | PathBase  -> p
            | PathStep (through',to',q',st) ->
                PathStep
                  (through', to', (path_concat from through through' p q'),
                    st)
  











let rec (path_length : typ -> typ -> (unit,unit) path -> Prims.nat) =
  fun from  ->
    fun to_33158  ->
      fun p  ->
        match p with
        | PathBase  -> (Prims.parse_int "0")
        | PathStep (uu____33164,uu____33165,p',uu____33167) ->
            (Prims.parse_int "1") + (path_length from uu____33164 p')
  






let (step_eq :
  typ -> typ -> typ -> (unit,unit) step -> (unit,unit) step -> Prims.bool) =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun s1  ->
          fun s2  ->
            match s1 with
            | StepField (l1,fd1) ->
                let uu____33418 = s2  in
                (match uu____33418 with
                 | StepField (uu____33424,fd2) -> fd1 = fd2)
            | StepCell (uu____33504,uu____33505,i1) ->
                let uu____33508 = s2  in
                (match uu____33508 with
                 | StepCell (uu____33514,uu____33515,i2) -> i1 = i2)
            | StepUField (l1,fd1) ->
                let uu____33524 = s2  in
                (match uu____33524 with
                 | StepUField (uu____33530,fd2) -> fd1 = fd2)
  


type ('Afrom,'dummyV0,'dummyV1,'dummyV2,'dummyV3) path_disjoint_t =
  | PathDisjointStep of typ * typ * typ * (unit,unit) path * (unit,unit) step
  * (unit,unit) step 
  | PathDisjointIncludes of typ * typ * (unit,unit) path * (unit,unit) path *
  typ * typ * (unit,unit) path * (unit,unit) path *
  (unit,unit,unit,unit,unit) path_disjoint_t 
let (uu___is_PathDisjointStep :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> Prims.bool)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointStep (through,to11,to21,p,s1,s2) -> true
              | uu____33902 -> false
  
let (__proj__PathDisjointStep__item__through :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> typ)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointStep (through,to11,to21,p,s1,s2) -> through
  
let (__proj__PathDisjointStep__item__to1 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> typ)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointStep (through,to11,to21,p,s1,s2) -> to11
  
let (__proj__PathDisjointStep__item__to2 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> typ)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointStep (through,to11,to21,p,s1,s2) -> to21
  
let (__proj__PathDisjointStep__item__p :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> (unit,unit) path)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointStep (through,to11,to21,p,s1,s2) -> p
  
let (__proj__PathDisjointStep__item__s1 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> (unit,unit) step)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointStep (through,to11,to21,p,s1,s2) -> s1
  
let (__proj__PathDisjointStep__item__s2 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> (unit,unit) step)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointStep (through,to11,to21,p,s1,s2) -> s2
  
let (uu___is_PathDisjointIncludes :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> Prims.bool)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> true
              | uu____34662 -> false
  
let (__proj__PathDisjointIncludes__item__to1 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> typ)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> to11
  
let (__proj__PathDisjointIncludes__item__to2 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> typ)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> to21
  
let (__proj__PathDisjointIncludes__item__p1 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> (unit,unit) path)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> p11
  
let (__proj__PathDisjointIncludes__item__p2 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> (unit,unit) path)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> p21
  
let (__proj__PathDisjointIncludes__item__to1' :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> typ)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> to1'
  
let (__proj__PathDisjointIncludes__item__to2' :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> typ)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> to2'
  
let (__proj__PathDisjointIncludes__item__p1' :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> (unit,unit) path)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> p1'
  
let (__proj__PathDisjointIncludes__item__p2' :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t -> (unit,unit) path)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> p2'
  
let (__proj__PathDisjointIncludes__item___8 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_t ->
              (unit,unit,unit,unit,unit) path_disjoint_t)
  =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointIncludes (to11,to21,p11,p21,to1',to2',p1',p2',_8)
                  -> _8
  

type ('Afrom,'Avalue1,'Avalue2,'Ap1,'Ap2) path_disjoint = unit





let rec (path_equal :
  typ -> typ -> typ -> (unit,unit) path -> (unit,unit) path -> Prims.bool) =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            match p1 with
            | PathBase  -> uu___is_PathBase from value2 p2
            | PathStep (uu____36138,uu____36139,p1',s1) ->
                (uu___is_PathStep from value2 p2) &&
                  (let uu____36155 = p2  in
                   (match uu____36155 with
                    | PathStep (uu____36160,uu____36161,p2',s2) ->
                        (path_equal from uu____36138 uu____36160 p1' p2') &&
                          (step_eq uu____36138 uu____36139 uu____36161 s1 s2)))
  


type ('Afrom,'Avalue1,'Avalue2,'Ap1,'Ap2) path_disjoint_decomp_t =
  | PathDisjointDecomp of typ * (unit,unit) path * typ * (unit,unit) step *
  (unit,unit) path * typ * (unit,unit) step * (unit,unit) path * unit 
let (uu___is_PathDisjointDecomp :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t -> Prims.bool)
  =
  fun from  ->
    fun value1  ->
      fun value2  -> fun p1  -> fun p2  -> fun projectee  -> true
  
let (__proj__PathDisjointDecomp__item__d_through :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t -> typ)
  =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointDecomp
                  (d_through,d_p,d_v1,d_s1,d_p1',d_v2,d_s2,d_p2',_8) ->
                  d_through
  
let (__proj__PathDisjointDecomp__item__d_p :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t ->
              (unit,unit) path)
  =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointDecomp
                  (d_through,d_p,d_v1,d_s1,d_p1',d_v2,d_s2,d_p2',_8) -> d_p
  
let (__proj__PathDisjointDecomp__item__d_v1 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t -> typ)
  =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointDecomp
                  (d_through,d_p,d_v1,d_s1,d_p1',d_v2,d_s2,d_p2',_8) -> d_v1
  
let (__proj__PathDisjointDecomp__item__d_s1 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t ->
              (unit,unit) step)
  =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointDecomp
                  (d_through,d_p,d_v1,d_s1,d_p1',d_v2,d_s2,d_p2',_8) -> d_s1
  
let (__proj__PathDisjointDecomp__item__d_p1' :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t ->
              (unit,unit) path)
  =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointDecomp
                  (d_through,d_p,d_v1,d_s1,d_p1',d_v2,d_s2,d_p2',_8) -> d_p1'
  
let (__proj__PathDisjointDecomp__item__d_v2 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t -> typ)
  =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointDecomp
                  (d_through,d_p,d_v1,d_s1,d_p1',d_v2,d_s2,d_p2',_8) -> d_v2
  
let (__proj__PathDisjointDecomp__item__d_s2 :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t ->
              (unit,unit) step)
  =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointDecomp
                  (d_through,d_p,d_v1,d_s1,d_p1',d_v2,d_s2,d_p2',_8) -> d_s2
  
let (__proj__PathDisjointDecomp__item__d_p2' :
  typ ->
    typ ->
      typ ->
        (unit,unit) path ->
          (unit,unit) path ->
            (unit,unit,unit,unit,unit) path_disjoint_decomp_t ->
              (unit,unit) path)
  =
  fun from  ->
    fun value1  ->
      fun value2  ->
        fun p1  ->
          fun p2  ->
            fun projectee  ->
              match projectee with
              | PathDisjointDecomp
                  (d_through,d_p,d_v1,d_s1,d_p1',d_v2,d_s2,d_p2',_8) -> d_p2'
  




let rec (path_destruct_l :
  typ ->
    typ ->
      (unit,unit) path ->
        (typ,((unit,unit) step,(unit,unit) path) Prims.dtuple2) Prims.dtuple2
          FStar_Pervasives_Native.option)
  =
  fun t0  ->
    fun t2  ->
      fun p  ->
        match p with
        | PathBase  -> FStar_Pervasives_Native.None
        | PathStep (uu____37683,uu____37684,p',s) ->
            (match path_destruct_l t0 uu____37683 p' with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some
                   (Prims.Mkdtuple2 (t2, (Prims.Mkdtuple2 (s, PathBase))))
             | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
                 (t_,Prims.Mkdtuple2 (s_,p_))) ->
                 FStar_Pervasives_Native.Some
                   (Prims.Mkdtuple2
                      (t_,
                        (Prims.Mkdtuple2
                           (s_, (PathStep (uu____37683, uu____37684, p_, s)))))))
  
let rec (path_equal' :
  typ -> typ -> typ -> (unit,unit) path -> (unit,unit) path -> Prims.bool) =
  fun from  ->
    fun to1  ->
      fun to2  ->
        fun p1  ->
          fun p2  ->
            match path_destruct_l from to1 p1 with
            | FStar_Pervasives_Native.None  -> uu___is_PathBase from to2 p2
            | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
                (t1,Prims.Mkdtuple2 (s1,p1'))) ->
                (match path_destruct_l from to2 p2 with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
                     (t2,Prims.Mkdtuple2 (s2,p2'))) ->
                     (step_eq from t1 t2 s1 s2) &&
                       (path_equal' t1 to1 to2 p1' p2'))
  







let (_field :
  struct_typ -> unit pointer -> unit struct_field -> unit pointer) =
  fun l  ->
    fun p  ->
      fun fd  ->
        let uu____38622 = p  in
        match uu____38622 with
        | Pointer (from,contents,p') ->
            let p'1 = p'  in
            let p'' =
              PathStep
                ((TStruct l), (typ_of_struct_field l fd), p'1,
                  (StepField (l, fd)))
               in
            Pointer (from, contents, p'')
  
let (_cell :
  array_length_t -> typ -> unit pointer -> FStar_UInt32.t -> unit pointer) =
  fun length1  ->
    fun value  ->
      fun p  ->
        fun i  ->
          let uu____38843 = p  in
          match uu____38843 with
          | Pointer (from,contents,p') ->
              let p'1 = p'  in
              let p'' =
                PathStep
                  ((TArray (length1, value)), value, p'1,
                    (StepCell (length1, value, i)))
                 in
              Pointer (from, contents, p'')
  
let (_ufield :
  union_typ -> unit pointer -> unit struct_field -> unit pointer) =
  fun l  ->
    fun p  ->
      fun fd  ->
        let uu____38971 = p  in
        match uu____38971 with
        | Pointer (from,contents,p') ->
            let p'1 = p'  in
            let p'' =
              PathStep
                ((TUnion l), (typ_of_struct_field l fd), p'1,
                  (StepUField (l, fd)))
               in
            Pointer (from, contents, p'')
  
type ('Avalue,'Ap,'Ah) unused_in = Obj.t
type pointer_ref_contents = (typ,unit) Prims.dtuple2
type ('Avalue,'Ah,'Ap) live = Obj.t
type ('Avalue,'Ah,'Ap) nlive = Obj.t








































type ('Aa,'Ah,'Ab) readable = unit





type ('Al,'Ah,'Ap,'As) readable_struct_fields = Obj.t







type ('Al,'Ah,'Ap,'Afd) is_active_union_field = unit






type ('Aa,'Ah,'Ab,'Ah','Ab') equal_values = unit
let (_singleton_buffer_of_pointer : typ -> unit pointer -> unit buffer) =
  fun t  ->
    fun p  ->
      let uu____40048 = p  in
      match uu____40048 with
      | Pointer (from,contents,pth) ->
          (match pth with
           | PathStep (uu____40070,uu____40071,pth',StepCell (ln,ty,i)) ->
               Buffer
                 ((BufferRootArray (ln, (Pointer (from, contents, pth')))),
                   i, (FStar_UInt32.uint_to_t (Prims.parse_int "1")))
           | uu____40081 ->
               Buffer
                 ((BufferRootSingleton p),
                   (FStar_UInt32.uint_to_t (Prims.parse_int "0")),
                   (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
  

let (singleton_buffer_of_pointer : typ -> unit pointer -> unit buffer) =
  fun t  -> fun p  -> _singleton_buffer_of_pointer t p 

let (buffer_of_array_pointer :
  typ -> array_length_t -> unit pointer -> unit buffer) =
  fun t  ->
    fun length1  ->
      fun p  ->
        Buffer
          ((BufferRootArray (length1, p)),
            (FStar_UInt32.uint_to_t (Prims.parse_int "0")), length1)
  



type ('At,'Ah,'Ab) buffer_live = Obj.t


type ('At,'Ab,'Ah) buffer_unused_in = Obj.t













let (sub_buffer :
  typ -> unit buffer -> FStar_UInt32.t -> FStar_UInt32.t -> unit buffer) =
  fun t  ->
    fun b  ->
      fun i  ->
        fun len  ->
          Buffer
            ((__proj__Buffer__item__broot t b),
              (FStar_UInt32.add (__proj__Buffer__item__bidx t b) i), len)
  
let (offset_buffer : typ -> unit buffer -> FStar_UInt32.t -> unit buffer) =
  fun t  ->
    fun b  ->
      fun i  ->
        sub_buffer t b i
          (FStar_UInt32.sub (__proj__Buffer__item__blength t b) i)
  














let (pointer_of_buffer_cell :
  typ -> unit buffer -> FStar_UInt32.t -> unit pointer) =
  fun t  ->
    fun b  ->
      fun i  ->
        match __proj__Buffer__item__broot t b with
        | BufferRootSingleton p -> p
        | BufferRootArray (uu____40731,p) ->
            _cell uu____40731 t p
              (FStar_UInt32.add (__proj__Buffer__item__bidx t b) i)
  












type ('At,'Ah,'Ab) buffer_readable' = unit
type ('At,'Ah,'Ab) buffer_readable = unit







type ('Avalue1,'Avalue2,'Ap1,'Ap2) disjoint = Obj.t











type loc_aux =
  | LocBuffer of typ * unit buffer 
  | LocPointer of typ * unit pointer 
  | LocUnion of loc_aux * loc_aux 
let (uu___is_LocBuffer : loc_aux -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocBuffer (t,b) -> true | uu____41314 -> false
  
let (__proj__LocBuffer__item__t : loc_aux -> typ) =
  fun projectee  -> match projectee with | LocBuffer (t,b) -> t 
let (__proj__LocBuffer__item__b : loc_aux -> unit buffer) =
  fun projectee  -> match projectee with | LocBuffer (t,b) -> b 
let (uu___is_LocPointer : loc_aux -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocPointer (t,p) -> true | uu____41363 -> false
  
let (__proj__LocPointer__item__t : loc_aux -> typ) =
  fun projectee  -> match projectee with | LocPointer (t,p) -> t 
let (__proj__LocPointer__item__p : loc_aux -> unit pointer) =
  fun projectee  -> match projectee with | LocPointer (t,p) -> p 
let (uu___is_LocUnion : loc_aux -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocUnion (l1,l2) -> true | uu____41419 -> false
  
let (__proj__LocUnion__item__l1 : loc_aux -> loc_aux) =
  fun projectee  -> match projectee with | LocUnion (l1,l2) -> l1 
let (__proj__LocUnion__item__l2 : loc_aux -> loc_aux) =
  fun projectee  -> match projectee with | LocUnion (l1,l2) -> l2 

type ('At,'As) set_nonempty = unit
type loc' =
  | Loc of unit * unit * unit * unit * unit * unit 
let (uu___is_Loc : loc' -> Prims.bool) = fun projectee  -> true 






type loc = loc'

let (loc_none : loc) = Loc ((), (), (), (), (), ()) 










type ('At1,'At2,'Ab,'Ap) buffer_includes_pointer = unit




type ('As,'At,'Ab) loc_aux_includes_buffer = unit













type ('As1,'As2) loc_includes = unit


















type ('At1,'At2,'Ab,'Ap) disjoint_buffer_vs_pointer = unit

type ('Al,'At,'Ab) loc_aux_disjoint_buffer = unit











type ('Al1,'Al2) loc_disjoint' = unit
type ('As1,'As2) loc_disjoint = unit






















type ('As,'Ah1,'Ah2) modifies' = unit
type ('As,'Ah1,'Ah2) modifies = unit













type ('Ah0,'Ah1) modifies_0 = unit
type ('At,'Ap,'Ah0,'Ah1) modifies_1 = unit
let (screate : typ -> unit FStar_Pervasives_Native.option -> unit pointer) =
  fun value  ->
    fun s  ->
      let h0 = FStar_HyperStack_ST.get ()  in
      let s1 =
        match Obj.magic s with
        | FStar_Pervasives_Native.Some s1 -> ovalue_of_value value s1
        | uu____43153 -> none_ovalue value  in
      let content =
        FStar_HyperStack_ST.salloc (Obj.magic (Prims.Mkdtuple2 (value, s1)))
         in
      let aref = FStar_Monotonic_HyperStack.aref_of content  in
      let p = Pointer (value, aref, PathBase)  in
      let h1 = FStar_HyperStack_ST.get ()  in p
  

let (ecreate :
  typ ->
    FStar_Monotonic_HyperHeap.rid ->
      unit FStar_Pervasives_Native.option -> unit pointer)
  =
  fun t  ->
    fun r  ->
      fun s  ->
        let h0 = FStar_HyperStack_ST.get ()  in
        let s0 = s  in
        let s1 =
          match Obj.magic s with
          | FStar_Pervasives_Native.Some s1 -> ovalue_of_value t s1
          | uu____43511 -> none_ovalue t  in
        let content =
          FStar_HyperStack_ST.ralloc r (Obj.magic (Prims.Mkdtuple2 (t, s1)))
           in
        let aref = FStar_Monotonic_HyperStack.aref_of content  in
        let p = Pointer (t, aref, PathBase)  in
        let h1 = FStar_HyperStack_ST.get ()  in p
  
let (field : struct_typ -> unit pointer -> unit struct_field -> unit pointer)
  = fun l  -> fun p  -> fun fd  -> _field l p fd 
let (ufield : union_typ -> unit pointer -> unit struct_field -> unit pointer)
  = fun l  -> fun p  -> fun fd  -> _ufield l p fd 
let (cell :
  array_length_t -> typ -> unit pointer -> FStar_UInt32.t -> unit pointer) =
  fun length1  -> fun value  -> fun p  -> fun i  -> _cell length1 value p i 
let (reference_of :
  typ ->
    FStar_Monotonic_HyperStack.mem ->
      unit pointer -> pointer_ref_contents FStar_HyperStack.reference)
  =
  fun value  ->
    fun h  ->
      fun p  ->
        let x =
          Obj.magic
            (FStar_Monotonic_HyperStack.reference_of h
               (__proj__Pointer__item__contents value p) () ())
           in
        x
  
let (read : typ -> unit pointer -> Obj.t) =
  fun value  ->
    fun p  ->
      let h = FStar_HyperStack_ST.get ()  in
      let r = reference_of value h p  in
      FStar_HyperStack_ST.witness_region
        (FStar_Monotonic_HyperStack.frameOf r);
      FStar_HyperStack_ST.witness_hsref r;
      (let uu____44340 = FStar_HyperStack_ST.op_Bang r  in
       match Obj.magic uu____44340 with
       | Prims.Mkdtuple2 (uu____44403,c) ->
           value_of_ovalue value
             (path_sel uu____44403 value c (__proj__Pointer__item__p value p)))
  
let (is_null : typ -> unit npointer -> Prims.bool) =
  fun t  -> fun p  -> match p with | NullPtr  -> true | uu____44541 -> false 
let (owrite : typ -> unit pointer -> Obj.t -> unit) =
  fun a  ->
    fun b  ->
      fun z  ->
        let h0 = FStar_HyperStack_ST.get ()  in
        let r = reference_of a h0 b  in
        FStar_HyperStack_ST.witness_region
          (FStar_Monotonic_HyperStack.frameOf r);
        FStar_HyperStack_ST.witness_hsref r;
        (let v0 = FStar_HyperStack_ST.op_Bang r  in
         let uu____44823 = v0  in
         match Obj.magic uu____44823 with
         | Prims.Mkdtuple2 (t,c0) ->
             let c1 = path_upd t a c0 (__proj__Pointer__item__p a b) z  in
             let v1 = Obj.magic (Prims.Mkdtuple2 (t, c1))  in
             (FStar_HyperStack_ST.op_Colon_Equals r v1;
              (let h1 = FStar_HyperStack_ST.get ()  in ())))
  
let (write : typ -> unit pointer -> Obj.t -> unit) =
  fun a  -> fun b  -> fun z  -> owrite a b (ovalue_of_value a z) 
let (write_union_field :
  union_typ -> unit pointer -> unit struct_field -> unit) =
  fun l  ->
    fun p  ->
      fun fd  ->
        let field_t = typ_of_struct_field l fd  in
        let vu =
          FStar_Pervasives_Native.Some
            (gtdata_create fd (Obj.magic (none_ovalue field_t)))
           in
        let vu1 = Obj.magic vu  in owrite (TUnion l) p (Obj.magic vu1)
  


















let (read_buffer : typ -> unit buffer -> FStar_UInt32.t -> Obj.t) =
  fun t  ->
    fun b  ->
      fun i  ->
        let uu____46510 = pointer_of_buffer_cell t b i  in read t uu____46510
  
let (write_buffer : typ -> unit buffer -> FStar_UInt32.t -> Obj.t -> unit) =
  fun t  ->
    fun b  ->
      fun i  ->
        fun v1  ->
          let uu____46631 = pointer_of_buffer_cell t b i  in
          write t uu____46631 v1
  










type ('At,'Ablarge,'Absmall) buffer_includes = unit





