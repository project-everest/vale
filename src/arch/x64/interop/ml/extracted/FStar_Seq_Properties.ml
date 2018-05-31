open Prims
type ('Aa,'As,'Aj) indexable = unit




let head : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa =
  fun s  -> FStar_Seq_Base.index s (Prims.parse_int "0") 
let tail : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa FStar_Seq_Base.seq =
  fun s  ->
    FStar_Seq_Base.slice s (Prims.parse_int "1") (FStar_Seq_Base.length s)
  


let last : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa =
  fun s  ->
    FStar_Seq_Base.index s
      ((FStar_Seq_Base.length s) - (Prims.parse_int "1"))
  
let cons : 'Aa . 'Aa -> 'Aa FStar_Seq_Base.seq -> 'Aa FStar_Seq_Base.seq =
  fun x  ->
    fun s  ->
      FStar_Seq_Base.append (FStar_Seq_Base.create (Prims.parse_int "1") x) s
  

let split :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat ->
        ('Aa FStar_Seq_Base.seq,'Aa FStar_Seq_Base.seq)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun i  ->
      ((FStar_Seq_Base.slice s (Prims.parse_int "0") i),
        (FStar_Seq_Base.slice s i (FStar_Seq_Base.length s)))
  

let split_eq :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat ->
        ('Aa FStar_Seq_Base.seq,'Aa FStar_Seq_Base.seq)
          FStar_Pervasives_Native.tuple2
  = fun s  -> fun i  -> let x = split s i  in x 
let rec count : 'Aa . 'Aa -> 'Aa FStar_Seq_Base.seq -> Prims.nat =
  fun x  ->
    fun s  ->
      if (FStar_Seq_Base.length s) = (Prims.parse_int "0")
      then (Prims.parse_int "0")
      else
        if (head s) = x
        then (Prims.parse_int "1") + (count x (tail s))
        else count x (tail s)
  
let mem : 'Aa . 'Aa -> 'Aa FStar_Seq_Base.seq -> Prims.bool =
  fun x  -> fun l  -> (count x l) > (Prims.parse_int "0") 

let swap :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat -> Prims.nat -> 'Aa FStar_Seq_Base.seq
  =
  fun s  ->
    fun i  ->
      fun j  ->
        FStar_Seq_Base.upd
          (FStar_Seq_Base.upd s j (FStar_Seq_Base.index s i)) i
          (FStar_Seq_Base.index s j)
  






let rec sorted :
  'Aa . ('Aa -> 'Aa -> Prims.bool) -> 'Aa FStar_Seq_Base.seq -> Prims.bool =
  fun f  ->
    fun s  ->
      if (FStar_Seq_Base.length s) <= (Prims.parse_int "1")
      then true
      else
        (let hd1 = head s  in
         (f hd1 (FStar_Seq_Base.index s (Prims.parse_int "1"))) &&
           (sorted f (tail s)))
  





type ('Aa,'Af) total_order = unit
type 'Aa tot_ord = 'Aa -> 'Aa -> Prims.bool

let split_5 :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat -> Prims.nat -> 'Aa FStar_Seq_Base.seq FStar_Seq_Base.seq
  =
  fun s  ->
    fun i  ->
      fun j  ->
        let uu____700 = split_eq s i  in
        match uu____700 with
        | (frag_lo,rest) ->
            let uu____727 = split_eq rest (Prims.parse_int "1")  in
            (match uu____727 with
             | (frag_i,rest1) ->
                 let uu____750 =
                   split_eq rest1 (j - (i + (Prims.parse_int "1")))  in
                 (match uu____750 with
                  | (frag_mid,rest2) ->
                      let uu____785 = split_eq rest2 (Prims.parse_int "1")
                         in
                      (match uu____785 with
                       | (frag_j,frag_hi) ->
                           FStar_Seq_Base.upd
                             (FStar_Seq_Base.upd
                                (FStar_Seq_Base.upd
                                   (FStar_Seq_Base.upd
                                      (FStar_Seq_Base.create
                                         (Prims.parse_int "5") frag_lo)
                                      (Prims.parse_int "1") frag_i)
                                   (Prims.parse_int "2") frag_mid)
                                (Prims.parse_int "3") frag_j)
                             (Prims.parse_int "4") frag_hi)))
  


type ('Aa,'As1,'As2) permutation = unit












let splice :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat ->
        'Aa FStar_Seq_Base.seq -> Prims.nat -> 'Aa FStar_Seq_Base.seq
  =
  fun s1  ->
    fun i  ->
      fun s2  ->
        fun j  ->
          FStar_Seq_Base.append
            (FStar_Seq_Base.slice s1 (Prims.parse_int "0") i)
            (FStar_Seq_Base.append (FStar_Seq_Base.slice s2 i j)
               (FStar_Seq_Base.slice s1 j (FStar_Seq_Base.length s1)))
  











let snoc : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa -> 'Aa FStar_Seq_Base.seq =
  fun s  ->
    fun x  ->
      FStar_Seq_Base.append s (FStar_Seq_Base.create (Prims.parse_int "1") x)
  




let rec find_l :
  'Aa .
    ('Aa -> Prims.bool) ->
      'Aa FStar_Seq_Base.seq -> 'Aa FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      if (FStar_Seq_Base.length l) = (Prims.parse_int "0")
      then FStar_Pervasives_Native.None
      else
        if f (head l)
        then FStar_Pervasives_Native.Some (head l)
        else find_l f (tail l)
  





let un_snoc :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      ('Aa FStar_Seq_Base.seq,'Aa) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    let uu____1463 =
      split s ((FStar_Seq_Base.length s) - (Prims.parse_int "1"))  in
    match uu____1463 with
    | (s',a) -> (s', (FStar_Seq_Base.index a (Prims.parse_int "0")))
  

let rec find_r :
  'Aa .
    ('Aa -> Prims.bool) ->
      'Aa FStar_Seq_Base.seq -> 'Aa FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      if (FStar_Seq_Base.length l) = (Prims.parse_int "0")
      then FStar_Pervasives_Native.None
      else
        (let uu____1548 = un_snoc l  in
         match uu____1548 with
         | (prefix,last1) ->
             if f last1
             then FStar_Pervasives_Native.Some last1
             else find_r f prefix)
  
type 'Ai found = unit
let rec seq_find_aux :
  'Aa .
    ('Aa -> Prims.bool) ->
      'Aa FStar_Seq_Base.seq ->
        Prims.nat -> 'Aa FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      fun ctr  ->
        match ctr with
        | _0_2 when _0_2 = (Prims.parse_int "0") ->
            FStar_Pervasives_Native.None
        | uu____1643 ->
            let i = ctr - (Prims.parse_int "1")  in
            if f (FStar_Seq_Base.index l i)
            then FStar_Pervasives_Native.Some (FStar_Seq_Base.index l i)
            else seq_find_aux f l i
  
let seq_find :
  'Aa .
    ('Aa -> Prims.bool) ->
      'Aa FStar_Seq_Base.seq -> 'Aa FStar_Pervasives_Native.option
  = fun f  -> fun l  -> seq_find_aux f l (FStar_Seq_Base.length l) 

let for_all :
  'Aa . ('Aa -> Prims.bool) -> 'Aa FStar_Seq_Base.seq -> Prims.bool =
  fun f  ->
    fun l  ->
      FStar_Pervasives_Native.uu___is_None
        (seq_find (fun i  -> Prims.op_Negation (f i)) l)
  

let rec seq_to_list : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa Prims.list =
  fun s  ->
    if (FStar_Seq_Base.length s) = (Prims.parse_int "0")
    then []
    else (FStar_Seq_Base.index s (Prims.parse_int "0")) ::
      (seq_to_list
         (FStar_Seq_Base.slice s (Prims.parse_int "1")
            (FStar_Seq_Base.length s)))
  
let rec seq_of_list : 'Aa . 'Aa Prims.list -> 'Aa FStar_Seq_Base.seq =
  fun l  ->
    match l with
    | [] -> FStar_Seq_Base.createEmpty ()
    | hd1::tl1 ->
        FStar_Seq_Base.op_At_Bar
          (FStar_Seq_Base.create (Prims.parse_int "1") hd1) (seq_of_list tl1)
  


type ('Aa,'Al,'As) createL_post = unit
let createL : 'Aa . 'Aa Prims.list -> 'Aa FStar_Seq_Base.seq =
  fun l  -> let s = seq_of_list l  in s 

type ('Aa,'As,'Ax) contains = unit












type ('Aa,'As_suff,'As) suffix_of = unit














