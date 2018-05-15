module X64.Memory_i_s

module I = Interop64
module HS = FStar.HyperStack
module B = FStar.Buffer
module M = FStar.Modifies
module S = X64.Bytes_Semantics_s
module H = FStar.Heap

let heap = H.heap
noeq type mem' = {
  addrs : I.addr_map;
  ptrs : list (B.buffer UInt64.t);
  hs : HS.mem;
  }

type mem = (m:mem'{I.list_disjoint_or_eq #UInt64.t m.ptrs /\
  I.list_live m.hs m.ptrs})

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

let coerce (#a:Type0) (b:Type0{a == b}) (x:a) : b = x

// TODO: Handle UInt128

let tuint8 = UInt8.t
let tuint16 = UInt16.t
let tuint32 = UInt32.t
let tuint64 = UInt64.t
// let tuint128 = magic()

let m_of_typ (t:typ) : Type0 =
  match t with
  | TBase TUInt8 -> tuint8
  | TBase TUInt16 -> tuint16
  | TBase TUInt32 -> tuint32
  | TBase TUInt64 -> tuint64
  | TBase TUInt128 -> admit () // M.tuint128

let v_of_typ (t:typ) (v:type_of_typ t) :  (m_of_typ t) =
  match t with
  | TBase TUInt8 -> coerce ((m_of_typ t)) (UInt8.uint_to_t v)
  | TBase TUInt16 -> coerce ((m_of_typ t)) (UInt16.uint_to_t v)
  | TBase TUInt32 -> coerce ((m_of_typ t)) (UInt32.uint_to_t v)
  | TBase TUInt64 -> coerce ((m_of_typ t)) (UInt64.uint_to_t v)
  | TBase TUInt128 -> magic() //coerce (M.type_of_typ (m_of_typ t)) (UInt128.uint_to_t v)

let v_to_typ (t:typ) (v:(m_of_typ t)) : type_of_typ t =
  match t with
  | TBase TUInt8 -> UInt8.v (coerce UInt8.t v)
  | TBase TUInt16 -> UInt16.v (coerce UInt16.t v)
  | TBase TUInt32 -> UInt32.v (coerce UInt32.t v)
  | TBase TUInt64 -> UInt64.v (coerce UInt64.t v)
  | TBase TUInt128 -> magic()
  
let lemma_v_to_of_typ (t:typ) (v:type_of_typ t) : Lemma
  (ensures v_to_typ t (v_of_typ t v) == v)
  [SMTPat (v_to_typ t (v_of_typ t v))]
  =
  match t with
  | TBase TUInt8 -> assert (UInt8.v (UInt8.uint_to_t v) == v)
  | TBase TUInt16 -> assert (UInt16.v (UInt16.uint_to_t v) == v)
  | TBase TUInt32 -> assert (UInt32.v (UInt32.uint_to_t v) == v)
  | TBase TUInt64 -> assert (UInt64.v (UInt64.uint_to_t v) == v)
  | TBase TUInt128 -> admit()

let buffer t = B.buffer (m_of_typ t)

let buffer_as_seq #t h b =
  let s = B.as_seq h.hs b in
  let len = Seq.length s in
  let contents (i:nat{i < len}) : type_of_typ t = v_to_typ t (Seq.index s i) in
  Seq.init len contents

// TODO: Fix this
let buffer_readable #t h b = if (t = TBase TUInt64) then List.memP b h.ptrs else false
let buffer_length #t b = B.length b
let loc = M.loc
let loc_none = M.loc_none
let loc_union = M.loc_union
let loc_buffer #t b = M.loc_buffer b
let loc_disjoint = M.loc_disjoint
let loc_includes = M.loc_includes
let modifies s h h' = 
  let _ = () in
  M.modifies s h.hs h'.hs /\ h.ptrs == h'.ptrs /\ h.addrs == h'.addrs

let valid_state s = s.state.S.mem == I.down_mem64 s.mem.hs s.mem.addrs s.mem.ptrs

let loc_readable h s = unit // admit()
let loc_readable_none = admit()
let loc_readable_union = admit()
let loc_readable_buffer #t h b = admit()

let modifies_goal_directed s h1 h2 = modifies s h1 h2
let lemma_modifies_goal_directed s h1 h2 = ()

let buffer_length_buffer_as_seq #t h b = ()

val modifies_loc_readable (#t:typ) (b:buffer t) (p:loc) (h h':mem) : Lemma
  (requires
    loc_readable h' p /\
    buffer_readable h b /\
    modifies p h h'
  )
  (ensures
    buffer_readable h' b
  )

let modifies_loc_readable #t b p h h' =
  // TODO
  admit ()

let modifies_buffer_elim #t1 b p h h' =
  if buffer_length b > 0 then
  (
    M.modifies_buffer_elim b p h.hs h'.hs;
    assert (Seq.equal (buffer_as_seq h b) (buffer_as_seq h' b));
    ()
  )
  else
  (
    modifies_loc_readable b p h h';
    assert (Seq.equal (buffer_as_seq h b) (buffer_as_seq h' b));
    ()
  )

let loc_disjoint_none_r s = M.loc_disjoint_none_r s
let loc_disjoint_union_r s s1 s2 = M.loc_disjoint_union_r s s1 s2
let loc_includes_refl s = M.loc_includes_refl s
let loc_includes_trans s1 s2 s3 = M.loc_includes_trans s1 s2 s3
let loc_includes_union_r s s1 s2 = M.loc_includes_union_r s s1 s2
let loc_includes_union_l s1 s2 s = M.loc_includes_union_l s1 s2 s
let loc_includes_union_l_buffer #t s1 s2 b = M.loc_includes_union_l s1 s2 (loc_buffer b)
let loc_includes_none s = M.loc_includes_none s
let modifies_refl s h = M.modifies_refl s h.hs
let modifies_goal_directed_refl s h = M.modifies_refl s h.hs
let modifies_loc_includes s1 h h' s2 = M.modifies_loc_includes s1 h.hs h'.hs s2
let modifies_trans s12 h1 h2 s23 h3 = M.modifies_trans s12 h1.hs h2.hs s23 h3.hs

let modifies_goal_directed_trans s12 h1 h2 s13 h3 =
  modifies_trans s12 h1 h2 s13 h3;
  modifies_loc_includes s13 h1 h3 (loc_union s12 s13);
  ()

let modifies_goal_directed_trans2 s12 h1 h2 s13 h3 = modifies_goal_directed_trans s12 h1 h2 s13 h3

let default_of_typ (t:typ) : type_of_typ t =
  match t with
  | TBase TUInt8 -> 0
  | TBase TUInt16 -> 0
  | TBase TUInt32 -> 0
  | TBase TUInt64 -> 0
  | TBase TUInt128 -> Words_s.Mkfour #nat32 0 0 0 0

let buffer_read #t b i h =
  if i < 0 || i >= buffer_length b then default_of_typ t else
  Seq.index (buffer_as_seq h b) i

// Proven but private in FStar.Buffer
assume private val lemma_aux: (#t:typ) -> b:buffer t -> n:nat{n < B.length b} -> z:m_of_typ t
  -> h0:HS.mem -> Lemma
  (requires True)
  (ensures (B.live h0 b) ==> (B.live h0 b
/\ B.modifies_1 b h0 (HS.upd h0 (B.content b) (Seq.upd (B.sel h0 b) (B.idx b + n) z)) ))

let buffer_write #t b i v h =
 if i < 0 || i >= buffer_length b then h else
 begin
 let vu = v_of_typ t v in
 let s0 = B.sel h.hs b in
 let s = Seq.upd s0 (B.idx b + i) vu in
 let h' = HS.upd h.hs (B.content b) s in
 let h' = {h with hs = h'} in
 lemma_aux b i vu h.hs;
 assert (Seq.equal (buffer_as_seq h' b) (Seq.upd (buffer_as_seq h b) i v));
 h'
 end

let buffer_addr #t b h =
  let addrs = h.addrs in
  addrs.[(B.as_addr b, B.idx b, B.length b)]

val addr_in_ptr: (addr:int) -> (ptr:buffer64) -> (h:mem) ->
  GTot (b:bool{ not b <==> (forall i. 0 <= i /\ i < B.length ptr ==> 
    addr <> (buffer_addr ptr h) + 8 `op_Multiply` i)})
  
// Checks if address addr corresponds to one of the elements of buffer ptr
let addr_in_ptr (addr:int) (ptr:buffer64) (h:mem) =
  let n = B.length ptr in
  let base = buffer_addr ptr h in
  let rec aux (i:nat) : Tot (b:bool{not b <==> (forall j. i <= j /\ j < n ==> 
    addr <> base + 8 `op_Multiply` j)}) 
    (decreases %[n-i]) =
    if i >= n then false
    else if addr = base + 8 `op_Multiply` i then true
    else aux (i+1)
  in aux 0

let rec get_addr_in_ptr (n base addr:nat) (i:nat{exists j. i <= j /\ j < n /\ base + 8 `op_Multiply` j == addr}) : 
    GTot (j:nat{base + 8 `op_Multiply` j == addr})
    (decreases %[n-i]) =
    if base + 8 `op_Multiply` i = addr then i
    else if i >= n then i
    else get_addr_in_ptr n base addr (i+1)


let rec valid_mem_aux addr ps (h:mem) : GTot (b:bool{
  (not b) <==> (forall (x:buffer64). (List.memP x ps ==> not (addr_in_ptr addr x h) ))}) 
  = match ps with
    | [] -> false
    | a::q -> if (addr_in_ptr addr a h) then true else valid_mem_aux addr q h

let valid_mem64 ptr h = valid_mem_aux ptr h.ptrs h

// TODO: Probably a similar approach baser on buffer_read?
let load_mem64 ptr s = admit() //S.get_heap_val64 ptr s.state.S.mem

let rec store_mem_aux addr (ps:list buffer64) (v:nat64) (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs }) : 
  GTot (h1:mem{forall (b:buffer64). B.live h.hs b <==> B.live h1.hs b }) =
  match ps with
  | [] -> h
  | a::q ->
    let base = buffer_addr a h in
    let n = B.length a in
    if addr_in_ptr addr a h then
    begin
      buffer_write a (get_addr_in_ptr n base addr 0) v h
    end
    else store_mem_aux addr q v h

#set-options "--z3rlimit 40"

let rec written_buffer_down_aux1 (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
      (ps:list buffer64{I.list_disjoint_or_eq ps /\ List.memP b ps})
      (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs})
      (base:nat{base == buffer_addr b h})
      (k:nat) (h1:mem{h1 == buffer_write b i v h}) 
      (mem1:S.heap{I.correct_down64 h.hs h.addrs ps mem1}) 
      (mem2:S.heap{
      (I.correct_down64 h1.hs h.addrs ps mem2) /\
      (forall j. base <= j /\ j < base + k `op_Multiply` 8 ==> mem1.[j] == mem2.[j])}) : 
      Lemma (requires True)
      (ensures (forall j. j >= base /\ j < base + 8 `op_Multiply` i ==> mem1.[j] == mem2.[j]))
      (decreases %[i-k]) =
    if k >= i then ()
    else begin
      assert (Seq.index (B.as_seq h.hs b) k == Seq.index (B.as_seq h1.hs b) k);
      Bytes_Semantics_i.same_mem_get_heap_val (base + 8 `op_Multiply` k) mem1 mem2;
      written_buffer_down_aux1 b i v ps h base (k+1) h1 mem1 mem2
    end

let rec written_buffer_down_aux2 (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
      (ps:list buffer64{I.list_disjoint_or_eq ps /\ List.memP b ps})
      (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs})
      (base:nat{base == buffer_addr b h})
      (n:nat{n == B.length b})
      (k:nat{k > i}) (h1:mem{h1 == buffer_write b i v h}) 
      (mem1:S.heap{I.correct_down64 h.hs h.addrs ps mem1}) 
      (mem2:S.heap{
      (I.correct_down64 h1.hs h.addrs ps mem2) /\
      (forall j. base + 8 `op_Multiply` (i+1) <= j /\ j < base + k `op_Multiply` 8 ==>
      mem1.[j] == mem2.[j])}) :
      Lemma 
      (requires True)
      (ensures (forall j. j >= base + 8 `op_Multiply` (i+1) /\ j < base + 8 `op_Multiply` n ==> 
	mem1.[j] == mem2.[j]))
      (decreases %[n-k]) =
    if k >= n then ()
    else begin
      assert (Seq.index (B.as_seq h.hs b) k == Seq.index (B.as_seq h1.hs b) k);
      Bytes_Semantics_i.same_mem_get_heap_val (base + 8 `op_Multiply` k) mem1 mem2;
      written_buffer_down_aux2 b i v ps h base n (k+1) h1 mem1 mem2
    end
    
let written_buffer_down (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{I.list_disjoint_or_eq ps /\ List.memP b ps}) (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs}) :
  Lemma (
    let mem1 = I.down_mem64 h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem64 h1.hs h.addrs ps in
    let base = buffer_addr b h in
    let n = B.length b in
    forall j. (base <= j /\ j < base + 8 `op_Multiply` i) \/ 
	 (base + 8 `op_Multiply` (i+1) <= j /\ j < base + 8 `op_Multiply` n) ==>
	 mem1.[j] == mem2.[j]) = 
    let mem1 = I.down_mem64 h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem64 h1.hs h.addrs ps in	 
    let base = buffer_addr b h in
    let n = B.length b in
    written_buffer_down_aux1 b i v ps h base 0 h1 mem1 mem2;
    written_buffer_down_aux2 b i v ps h base n (i+1) h1 mem1 mem2

let same_mem_get_heap_val_buf (base n:int) (mem1 mem2:S.heap) : Lemma
  (requires (forall i. 0 <= i /\ i < n ==> 
    S.get_heap_val64 (base + 8 `op_Multiply` i) mem1 == S.get_heap_val64 (base + 8 `op_Multiply` i) mem2))
  (ensures (forall i. i >= base /\ i < base + n `op_Multiply` 8 ==> mem1.[i] == mem2.[i])) =
  let rec aux (k:nat) : Lemma
  (requires (forall i. i >= base /\ i < base + k `op_Multiply` 8 ==> mem1.[i] == mem2.[i]) /\
   (forall i. 0 <= i /\ i < n ==> 
    S.get_heap_val64 (base + 8 `op_Multiply` i) mem1 == S.get_heap_val64 (base + 8 `op_Multiply` i) mem2) 
  )
  (ensures (forall i. i >= base /\ i < base + n `op_Multiply` 8 ==> mem1.[i] == mem2.[i]))
  (decreases %[n-k]) =
  if k >= n then ()
  else begin
    Bytes_Semantics_i.same_mem_get_heap_val (base + k `op_Multiply` 8) mem1 mem2;
    aux (k+1)
  end
  in aux 0

let rec unwritten_buffer_down_aux (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{I.list_disjoint_or_eq ps /\ List.memP b ps})
  (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs})
  (a:buffer64{a =!= b /\ List.memP a ps})  : 
  Lemma (let base = buffer_addr a h in
    let mem1 = I.down_mem64 h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem64 h1.hs h.addrs ps in
    forall j. j >= base /\ j < base + (B.length a) `op_Multiply` 8 ==> mem1.[j] == mem2.[j]) =
    let mem1 = I.down_mem64 h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem64 h1.hs h.addrs ps in
    let base = buffer_addr a h in    
    let s0 = B.as_seq h.hs a in
    assert (I.disjoint_or_eq a b);
    // We need this to help z3
    assert (forall j. 0 <= j /\ j < B.length a ==> UInt64.v (Seq.index s0 j) == S.get_heap_val64 (base + (j `op_Multiply` 8)) mem1 );
    same_mem_get_heap_val_buf base (B.length a) mem1 mem2

let unwritten_buffer_down (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{I.list_disjoint_or_eq ps /\ List.memP b ps}) 
  (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs}) : Lemma (
    let mem1 = I.down_mem64 h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem64 h1.hs h.addrs ps in
    forall  (a:buffer64{List.memP a ps /\ a =!= b}) j.
    let base = buffer_addr a h in j >= base /\ j < base + B.length a `op_Multiply` 8 ==> mem1.[j] == mem2.[j]) =
    let mem1 = I.down_mem64 h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem64 h1.hs h.addrs ps in   
    let fintro (a:buffer64{List.memP a ps /\ a =!= b}) 
      : Lemma 
      (forall j. let base = buffer_addr a h in 
      j >= base /\ j < base + (B.length a) `op_Multiply` 8 ==> 
	mem1.[j] == mem2.[j]) =
      let base = buffer_addr a h in
      unwritten_buffer_down_aux b i v ps h a
    in
    Classical.forall_intro fintro

let store_buffer_down_mem (b:buffer64) (i:nat{i < B.length b}) (v:nat64)
  (ps: list buffer64{I.list_disjoint_or_eq ps /\ List.memP b ps})
  (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs}) :
  Lemma (
    let mem1 = I.down_mem64 h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem64 h1.hs h.addrs ps in
    let base = buffer_addr b h in
    forall j. j < base + 8 `op_Multiply` i \/ j >= base + 8 `op_Multiply` (i+1) ==>
      mem1.[j] == mem2.[j]) =
    let mem1 = I.down_mem64 h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem64 h1.hs h.addrs ps in
    let base = buffer_addr b h in
    let n = B.length b in
    I.same_unspecified_down h.hs h1.hs h.addrs ps;
    unwritten_buffer_down b i v ps h;
    assert (forall j. (exists (a:buffer64{List.memP a ps /\ a =!= b}) . let base = buffer_addr a h in
      j >= base /\ j < base + B.length a `op_Multiply` 8) ==> mem1.[j] == mem2.[j]);

    written_buffer_down b i v ps h;
    ()

let rec get_addr_ptr (ptr:int) (h:mem) (ps:list buffer64{valid_mem_aux ptr ps h}) : 
  GTot (b:buffer64{List.memP b ps /\ addr_in_ptr ptr b h}) =
  match ps with
  // The list cannot be empty because of the mem predicate
  | a::q -> if addr_in_ptr ptr a h then a else get_addr_ptr ptr h q

let store_buffer_aux_down_mem (ptr:int) (v:nat64) (h:mem{valid_mem64 ptr h}) : Lemma (
  let mem1 = I.down_mem64 h.hs h.addrs h.ptrs in
  let h1 = store_mem_aux ptr h.ptrs v h in
  let mem2 = I.down_mem64 h1.hs h.addrs h.ptrs in
  forall j. j < ptr \/ j >= ptr + 8 ==> mem1.[j] == mem2.[j]) =
  let h1 = store_mem_aux ptr h.ptrs v h in
  let b = get_addr_ptr ptr h h.ptrs in
  let i = get_addr_in_ptr (B.length b) (buffer_addr b h) ptr 0 in
  let rec aux (ps:list buffer64{I.list_disjoint_or_eq ps /\ valid_mem_aux ptr ps h}) 
  (h0:mem{h0.addrs == h.addrs /\ (forall x. List.memP x ps ==> List.memP x h0.ptrs)}) :
  Lemma (let b = get_addr_ptr ptr h ps in
    let i = get_addr_in_ptr (B.length b) (buffer_addr b h) ptr 0 in
    store_mem_aux ptr ps v h0 == buffer_write b i v h0) =
    match ps with
    | [] -> ()
    | a::q ->
      if addr_in_ptr ptr a h0 then () else aux q h0    
  in aux h.ptrs h;
  store_buffer_down_mem b i v h.ptrs h

let store_buffer_aux_down_mem2 (ptr:int) (v:nat64) (h:mem{valid_mem64 ptr h}) : Lemma (
  let h1 = store_mem_aux ptr h.ptrs v h in
  let mem2 = I.down_mem64 h1.hs h.addrs h.ptrs in
  S.get_heap_val64 ptr mem2 == v) =
  let b = get_addr_ptr ptr h h.ptrs in
  let i = get_addr_in_ptr (B.length b) (buffer_addr b h) ptr 0 in
  let h1 = store_mem_aux ptr h.ptrs v h in
  let mem2 = I.down_mem64 h1.hs h.addrs h.ptrs in
  let rec aux (ps:list buffer64{I.list_disjoint_or_eq ps /\ valid_mem_aux ptr ps h}) 
  (h0:mem{h0.addrs == h.addrs /\ (forall x. List.memP x ps ==> List.memP x h0.ptrs)}) :
  Lemma (let b = get_addr_ptr ptr h ps in
    let i = get_addr_in_ptr (B.length b) (buffer_addr b h) ptr 0 in
    store_mem_aux ptr ps v h0 == buffer_write b i v h0) =
    match ps with
    | [] -> ()
    | a::q ->
      if addr_in_ptr ptr a h0 then () else aux q h0    
  in aux h.ptrs h;
  assert (UInt64.v (Seq.index (B.as_seq h1.hs b) i) == v);
  ()

#set-options "--z3rlimit 60"

let store_mem64 i v h =
  if not (valid_mem64 i h) then h
  else
  let h1 = store_mem_aux i h.ptrs v h in
  h1

let valid_mem128 ptr h = admit()
let load_mem128 ptr h = admit()
let store_mem128 ptr v h = admit()

