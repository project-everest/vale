module X64.Vale.Decls_i
module M = Memory_i_s

// This interface should hide all of Semantics_s.
// (It should not refer to Semantics_s, directly or indirectly.)
// It should not refer to StateLemmas_i, Lemmas_i, or Print_s,
// because they refer to Semantics_s.
// Regs_i and State_i are ok, because they do not refer to Semantics_s.

open X64.Machine_s
open X64.Vale.State_i
open Types_s

unfold let quad32 = quad32

val cf : (flags:int) -> bool
val overflow (flags:int) : bool
val update_cf (flags:int) (new_cf:bool) : (new_flags:int)
val update_of (flags:int) (new_of:bool) : (new_flags:int)

//unfold let va_subscript = Map.sel
unfold let va_subscript (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
unfold let va_update = Map.upd
unfold let va_make_opaque = Opaque_i.make_opaque
unfold let va_reveal_opaque = Opaque_i.reveal_opaque
unfold let va_hd = Cons?.hd
//unfold let va_tl = Cons?.tl // F* inlines "let ... = va_tl ..." more than we'd like; revised definition below suppresses this

// hide 'if' so that x and y get fully normalized
let va_if (#a:Type) (b:bool) (x:(_:unit{b}) -> a) (y:(_:unit{~b}) -> a) : a =
  if b then x () else y ()

(* Type aliases *)
unfold let va_bool = bool
unfold let va_int = int
val ins : Type0
val ocmp : Type0
unfold let va_code = precode ins ocmp
unfold let va_codes = list va_code
let va_tl (cs:va_codes) : Ghost va_codes (requires Cons? cs) (ensures fun tl -> tl == Cons?.tl cs) = Cons?.tl cs
unfold let va_state = state
val va_fuel : Type0
unfold let va_operand = operand
unfold let va_operand_opr64 = operand
let va_reg_operand = o:operand{OReg? o}
let va_operand_reg_opr64 = o:operand{OReg? o}
unfold let va_dst_operand = operand
unfold let va_operand_dst_opr64 = operand
unfold let va_shift_amt = operand
unfold let va_operand_shift_amt64 = operand
unfold let va_cmp = operand
unfold let va_register = reg
unfold let va_operand_xmm = xmm

(* Abbreviations *)
unfold let get_reg (o:va_reg_operand) : reg = OReg?.r o
//unfold let buffer_readable = M.buffer_readable
unfold let buffer_readable (#t:M.typ) (h:mem) (b:M.buffer t) = M.buffer_readable #t h b
//unfold let buffer_length = M.buffer_length
unfold let buffer_length (#t:M.typ) (b:M.buffer t) = M.buffer_length #t b
unfold let buffer64_as_seq (m:mem) (b:buffer64) : GTot (Seq.seq nat64) = M.buffer_as_seq m b
unfold let buffer128_as_seq (m:mem) (b:buffer128) : GTot (Seq.seq quad32) = M.buffer_as_seq m b
unfold let valid_src_addr (#t:M.typ) (m:mem) (b:M.buffer t) (i:int) : Type0 =
  0 <= i /\ i < buffer_length b /\ buffer_readable m b
unfold let valid_dst_addr (#t:M.typ) (m:mem) (b:M.buffer t) (i:int) : Type0 =
  0 <= i /\ i < buffer_length b /\ buffer_readable m b
unfold let buffer64_read (b:buffer64) (i:int) (m:mem) : nat64 = M.buffer_read b i m
unfold let buffer64_write (b:buffer64) (i:int) (v:nat64) (m:mem) : mem = M.buffer_write b i v m
unfold let buffer128_read (b:buffer128) (i:int) (m:mem) : quad32 = M.buffer_read b i m
unfold let buffer128_write (b:buffer128) (i:int) (v:quad32) (m:mem) : mem = M.buffer_write b i v m
unfold let modifies_mem (s:M.loc) (h1 h2:mem) : GTot Type0 = M.modifies s h1 h2
//unfold let loc_buffer = M.loc_buffer
unfold let loc_buffer(#t:M.typ) (b:M.buffer t) = M.loc_buffer #t b
unfold let locs_disjoint = M.locs_disjoint
unfold let loc_union = M.loc_union

(* Constructors *)
val va_fuel_default : unit -> va_fuel
[@va_qattr] unfold let va_op_operand_reg (r:reg) : va_operand = OReg r
[@va_qattr] unfold let va_op_xmm_xmm(x:xmm) : va_operand_xmm = x
[@va_qattr] unfold let va_op_opr_reg (r:reg) : va_operand = OReg r
[@va_qattr] unfold let va_op_opr64_reg (r:reg) : va_operand = OReg r
[@va_qattr] unfold let va_const_operand (n:int) = OConst n
[@va_qattr] unfold let va_const_opr64 (n:int) = OConst n
[@va_qattr] unfold let va_const_shift_amt (n:int) : va_shift_amt = OConst n
[@va_qattr] unfold let va_const_shift_amt64 (n:int) : va_shift_amt = OConst n
[@va_qattr] unfold let va_op_shift_amt_reg(r:reg) : va_shift_amt = OReg r
[@va_qattr] unfold let va_op_shift_amt64_reg (r:reg) : va_shift_amt = OReg r
[@va_qattr] unfold let va_op_cmp_reg (r:reg) : va_cmp = OReg r
[@va_qattr] unfold let va_const_cmp (n:int) : va_cmp = OConst n
[@va_qattr] unfold let va_coerce_register_to_operand (r:va_register) : va_operand = OReg r
[@va_qattr] unfold let va_coerce_operand_to_reg_operand (o:va_operand{OReg? o}) : va_reg_operand = o
[@va_qattr] unfold let va_coerce_dst_operand_to_reg_operand (o:va_dst_operand{OReg? o}) : va_reg_operand = o
[@va_qattr] unfold let va_coerce_operand_to_cmp(o:va_operand) : va_cmp = o
[@va_qattr] unfold let va_coerce_opr64_to_cmp (o:va_operand) : va_cmp = o
[@va_qattr] unfold let va_op_register (r:reg) : va_register = r
[@va_qattr] unfold let va_op_reg_oprerand_reg (r:reg) : va_reg_operand = OReg r
[@va_qattr] unfold let va_op_reg_opr64_reg (r:reg) : va_reg_operand = OReg r
[@va_qattr] unfold let va_op_dst_operand_reg (r:reg) : va_dst_operand = OReg r
[@va_qattr] unfold let va_op_dst_opr64_reg (r:reg) : va_dst_operand = OReg r
[@va_qattr] unfold let va_coerce_operand_to_dst_operand (o:va_operand) : va_dst_operand = o
[@va_qattr] unfold let va_coerce_dst_operand_to_operand (o:va_dst_operand) : va_operand = o
[@va_qattr] unfold let va_coerce_dst_opr64_to_opr64 (o:va_dst_operand) : va_operand = o
[@va_qattr]
unfold let va_opr_code_Mem (o:operand) (offset:int) : operand =
  match o with
  | OConst n -> OConst (n + offset)
  | OReg r -> OMem (MReg r offset)
  | _ -> OConst 42

let va_opr_lemma_Mem (s:va_state) (base:operand{OReg? base}) (offset:int) (b:buffer64) (index:int) : Lemma
  (requires
    valid_src_addr s.mem b index /\
    eval_operand base s + offset == buffer_addr b + 8 `op_Multiply` index
  )
  (ensures valid_operand (va_opr_code_Mem base offset) s)
  =
  lemma_valid_mem64 b index s.mem
  

(* Evaluation *)
[@va_qattr] unfold let va_eval_opr64        (s:va_state) (o:va_operand)     : nat64 = eval_operand o s
[@va_qattr] unfold let va_eval_dst_opr64    (s:va_state) (o:va_dst_operand) : nat64 = eval_operand o s
[@va_qattr] unfold let va_eval_shift_amt64  (s:va_state) (o:va_shift_amt)   : nat64 = eval_operand o s
[@va_qattr] unfold let va_eval_cmp_uint64   (s:va_state) (r:va_cmp)         : nat64 = eval_operand r s
[@va_qattr] unfold let va_eval_reg64        (s:va_state) (r:va_register)    : nat64 = eval_reg r s
[@va_qattr] unfold let va_eval_reg_opr64    (s:va_state) (o:va_operand)     : nat64 = eval_operand o s
[@va_qattr] unfold let va_eval_xmm          (s:va_state) (x:xmm)            : quad32 = eval_xmm x s

(* Predicates *)
[@va_qattr] unfold let va_is_src_opr64 (o:operand) (s:va_state) = valid_operand o s
[@va_qattr] let va_is_dst_opr64 (o:operand) (s:va_state) = match o with OReg Rsp -> false | OReg _ -> true | _ -> false
[@va_qattr] unfold let va_is_dst_dst_opr64 (o:va_dst_operand) (s:va_state) = va_is_dst_opr64 o s
[@va_qattr] unfold let va_is_src_reg (r:reg) (s:va_state) = True
[@va_qattr] unfold let va_is_dst_reg (r:reg) (s:va_state) = True
[@va_qattr] unfold let va_is_src_shift_amt64 (o:operand) (s:va_state) = valid_operand o s /\ (va_eval_shift_amt64 s o) < 64
[@va_qattr] unfold let va_is_src_reg_opr64 (o:operand) (s:va_state) = OReg? o
[@va_qattr] unfold let va_is_src_xmm (x:xmm) (s:va_state) = True
[@va_qattr] unfold let va_is_dst_xmm (x:xmm) (s:va_state) = True

(* Getters *)
[@va_qattr] unfold let va_get_ok (s:va_state) : bool = s.ok
[@va_qattr] unfold let va_get_flags (s:va_state) : int = s.flags
[@va_qattr] unfold let va_get_reg (r:reg) (s:va_state) : nat64 = eval_reg r s
[@va_qattr] unfold let va_get_xmm (x:xmm) (s:va_state) : quad32 = eval_xmm x s
[@va_qattr] unfold let va_get_mem (s:va_state) : mem = s.mem

(* Framing: va_update_foo means the two states are the same except for foo *)
[@va_qattr] let va_update_ok (sM:va_state) (sK:va_state) : va_state = { sK with ok = sM.ok }
[@va_qattr] let va_update_flags (sM:va_state) (sK:va_state) : va_state = { sK with flags = sM.flags }
[@va_qattr] let va_update_reg (r:reg) (sM:va_state) (sK:va_state) : va_state =
  update_reg r (eval_reg r sM) sK
[@va_qattr] let va_update_mem (sM:va_state) (sK:va_state) : va_state = { sK with mem = sM.mem }

[@va_qattr]
let va_update_operand (o:operand) (sM:va_state) (sK:va_state) : va_state =
  match o with
  | OConst n -> sK
  | OReg r -> va_update_reg r sM sK
  | OMem m -> va_update_mem sM sK 

[@va_qattr] unfold
let va_update_dst_operand (o:operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_operand o sM sK   

[@va_qattr] unfold
let va_update_operand_dst_opr64 (o:operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_operand o sM sK

[@va_qattr] unfold
let va_update_operand_opr64 (o:operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_operand o sM sK

[@va_qattr] unfold
let va_update_register (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_update_reg r sM sK

[@va_qattr] unfold
let va_update_operand_xmm (x:xmm) (sM:va_state) (sK:va_state) : va_state =
  update_xmm x (eval_xmm x sM) sK

[@va_qattr] unfold
let va_update_xmm (x:xmm) (sM:va_state) (sK:va_state) : va_state =
  update_xmm x (eval_xmm x sM) sK

unfold let va_value_opr64 = nat64
unfold let va_value_dst_opr64 = nat64
unfold let va_value_xmm = quad32
[@va_qattr] unfold let va_upd_ok (ok:bool) (s:state) : state = { s with ok = ok }
[@va_qattr] unfold let va_upd_flags (flags:nat64) (s:state) : state = { s with flags = flags }
[@va_qattr] unfold let va_upd_mem (mem:mem) (s:state) : state = { s with mem = mem }
[@va_qattr] unfold let va_upd_reg (r:reg) (v:nat64) (s:state) : state = update_reg r v s
[@va_qattr] unfold let va_upd_xmm (x:xmm) (v:quad32) (s:state) : state = update_xmm x v s

[@va_qattr]
let va_upd_operand_xmm (x:xmm) (v:quad32) (s:state) : state =
  update_xmm x v s

[@va_qattr]
let va_upd_operand_dst_opr64 (o:operand) (v:nat64) (s:state) =
  match o with
  | OConst n -> s
  | OReg r -> update_reg r v s
  | OMem m -> s // TODO: support destination memory operands
let va_lemma_upd_update (sM:state) : Lemma
  (
    (forall (sK:state) (o:operand).{:pattern (va_update_operand_dst_opr64 o sM sK)} va_is_dst_dst_opr64 o sK ==> va_update_operand_dst_opr64 o sM sK == va_upd_operand_dst_opr64 o (eval_operand o sM) sK) /\
    (forall (sK:state) (x:xmm).{:pattern (va_update_operand_xmm x sM sK)} va_update_operand_xmm x sM sK == va_upd_operand_xmm x (eval_xmm x sM) sK)
  )
  = ()

(** Constructors for va_codes *)
[@va_qattr] unfold let va_CNil () : va_codes = []
[@va_qattr] unfold let va_CCons (hd:va_code) (tl:va_codes) : va_codes = hd::tl

(** Constructors for va_code *)
unfold let va_Block (block:va_codes) : va_code = Block block
unfold let va_IfElse (ifCond:ocmp) (ifTrue:va_code) (ifFalse:va_code) : va_code = IfElse ifCond ifTrue ifFalse
unfold let va_While (whileCond:ocmp) (whileBody:va_code) : va_code = While whileCond whileBody

val va_cmp_eq (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_ne (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_le (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_ge (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_lt (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_gt (o1:va_operand) (o2:va_operand) : ocmp

unfold let va_get_block (c:va_code{Block? c}) : va_codes = Block?.block c
unfold let va_get_ifCond (c:va_code{IfElse? c}) : ocmp = IfElse?.ifCond c
unfold let va_get_ifTrue (c:va_code{IfElse? c}) : va_code = IfElse?.ifTrue c
unfold let va_get_ifFalse (c:va_code{IfElse? c}) : va_code = IfElse?.ifFalse c
unfold let va_get_whileCond (c:va_code{While? c}) : ocmp = While?.whileCond c
unfold let va_get_whileBody (c:va_code{While? c}) : va_code = While?.whileBody c

(** Map syntax **)
// syntax for map accesses, m.[key] and m.[key] <- value 
type map (key:eqtype) (value:Type) = Map.t key value
let op_String_Access     = Map.sel
let op_String_Assignment = Map.upd

(** Memory framing **)

(*
unfold let in_mem (addr:int) (m:mem) : bool = m `Map.contains` addr

let disjoint (ptr1:int) (num_bytes1:int) (ptr2:int) (num_bytes2:int) =
    ptr1 + num_bytes1 <= ptr2 \/ ptr2 + num_bytes2 <= ptr1

let validSrcAddrs (mem:mem) (addr:int) (size:int) (num_bytes:int) =
    size == 64 /\
    (forall (a:int) . {:pattern (mem `Map.contains` a)} addr <= a && a < addr+num_bytes && (a - addr) % 8 = 0 ==> mem `Map.contains` a)

let memModified (old_mem:mem) (new_mem:mem) (ptr:int) (num_bytes) =
    (forall (a:int) . {:pattern (new_mem `Map.contains` a)} old_mem `Map.contains` a <==> new_mem `Map.contains` a) /\
    (forall (a:int) . {:pattern (new_mem.[a]) \/ Map.sel new_mem a} a < ptr || a >= ptr + num_bytes ==> old_mem.[a] == new_mem.[a])
*)   

(** Convenient memory-related functions **)
let rec buffers_readable (h: mem) (l: list buffer64) : GTot Type0 (decreases l) =
    match l with
    | [] -> True
    | b :: l'  -> buffer_readable h b /\ buffers_readable h l'

unfold let modifies_buffer (b:buffer64) (h1 h2:mem) = modifies_mem (loc_buffer b) h1 h2
unfold let modifies_buffer_2 (b1 b2:buffer64) (h1 h2:mem) =modifies_mem (M.loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2
unfold let modifies_buffer128 (b:buffer128) (h1 h2:mem) = modifies_mem (loc_buffer b) h1 h2
unfold let modifies_buffer128_2 (b1 b2:buffer128) (h1 h2:mem) = modifies_mem (M.loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2

let validSrcAddrs64 (m:mem) (addr:int) (b:buffer64) (len:int) =
    buffer_readable m b /\
    len <= buffer_length b /\
    buffer_addr b == addr

unfold 
let validDstAddrs64 = validSrcAddrs64

let validSrcAddrs128 (m:mem) (addr:int) (b:buffer128) (len:int) =
    buffer_readable m b /\
    len <= buffer_length b /\
    buffer_addr b == addr

let validDstAddrs128 (m:mem) (addr:int) (b:buffer128) (len:int) =
    buffer_readable m b /\
    len <= buffer_length b /\
    buffer_addr b == addr

let valid_stack_slots (m:mem) (rsp:int) (b:buffer64) (num_slots:int) =
    buffer_readable m b /\
    num_slots <= buffer_length b /\
    (let open FStar.Mul in
     rsp == buffer_addr b + 8 * num_slots /\
     0 <= rsp - 8 * num_slots /\ 
     rsp < pow2_64)

let modifies_buffer_specific128 (b:buffer128) (h1 h2:mem) (start last:nat) : GTot Type0 =
    modifies_buffer128 b h1 h2 /\
    // TODO: Consider replacing this with: modifies (loc_buffer (gsub_buffer b i len)) h1 h2
    (forall (i:nat) . {:pattern (Seq.index (M.buffer_as_seq h2 b) i)}
                        0 <= i /\ i < buffer_length b 
                     /\ (i < start || i > last) 
                    ==> buffer128_read b i h1
                     == buffer128_read b i h2)

let modifies_buffer_specific (b:buffer64) (h1 h2:mem) (start last:nat) : GTot Type0 =
    modifies_buffer b h1 h2 /\
    // TODO: Consider replacing this with: modifies (loc_buffer (gsub_buffer b i len)) h1 h2
    (forall (i:nat) . {:pattern (Seq.index (M.buffer_as_seq h2 b) i)}
                        0 <= i /\ i < buffer_length b 
                     /\ (i < start || i > last) 
                    ==> buffer64_read b i h1
                     == buffer64_read b i h2)

unfold let buffers_disjoint (b1 b2:buffer64) =
    locs_disjoint [loc_buffer b1; loc_buffer b2]

unfold let buffers_disjoint128 (b1 b2:buffer128) =
    locs_disjoint [loc_buffer b1; loc_buffer b2]

unfold let buffers3_disjoint128 (b1 b2 b3:buffer128) =
    locs_disjoint [loc_buffer b1; loc_buffer b2; loc_buffer b3]

val eval_code (c:va_code) (s0:va_state) (f0:va_fuel) (sN:va_state) : Type0
val eval_while_inv (c:va_code) (s0:va_state) (fW:va_fuel) (sW:va_state) : Type0

(* ok for now but no need to actually expose the definition.
   instead expose lemmas about it *)
[@va_qattr]
let va_state_eq (s0:va_state) (s1:va_state) : Type0 = state_eq s0 s1

let va_require_total (c0:va_code) (c1:va_code) (s0:va_state) : Type0 =
  c0 == c1

let va_ensure_total (c0:va_code) (s0:va_state) (s1:va_state) (f1:va_fuel) : Type0 =
  eval_code c0 s0 f1 s1

val eval_ocmp : s:va_state -> c:ocmp -> GTot bool
unfold let va_evalCond (b:ocmp) (s:va_state) : GTot bool = eval_ocmp s b

val valid_ocmp : c:ocmp -> s:va_state -> GTot bool

val lemma_cmp_eq : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_eq o1 o2)) <==> (va_eval_opr64 s o1 == va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_eq o1 o2))]

val lemma_cmp_ne : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_ne o1 o2)) <==> (va_eval_opr64 s o1 <> va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_ne o1 o2))]

val lemma_cmp_le : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_le o1 o2)) <==> (va_eval_opr64 s o1 <= va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_le o1 o2))]

val lemma_cmp_ge : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_ge o1 o2)) <==> (va_eval_opr64 s o1 >= va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_ge o1 o2))]

val lemma_cmp_lt : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_lt o1 o2)) <==> (va_eval_opr64 s o1 < va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_lt o1 o2))]

val lemma_cmp_gt : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_gt o1 o2)) <==> (va_eval_opr64 s o1 > va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_gt o1 o2))]

val lemma_valid_cmp_eq : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_eq o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_eq o1 o2) s)]

val lemma_valid_cmp_ne : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_ne o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_ne o1 o2) s)]

val lemma_valid_cmp_le : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_le o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_le o1 o2) s)]

val lemma_valid_cmp_ge : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_ge o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_ge o1 o2) s)]

val lemma_valid_cmp_lt : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_lt o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_lt o1 o2) s)]

val lemma_valid_cmp_gt : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_gt o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_gt o1 o2) s)]

val va_compute_merge_total (f0:va_fuel) (fM:va_fuel) : va_fuel

val va_lemma_merge_total (b0:va_codes) (s0:va_state) (f0:va_fuel) (sM:va_state) (fM:va_fuel) (sN:va_state) : Ghost (fN:va_fuel)
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (va_Block (Cons?.tl b0)) sM fM sN
  )
  (ensures (fun fN ->
    fN == va_compute_merge_total f0 fM /\
    eval_code (va_Block b0) s0 fN sN
  ))

val va_lemma_empty_total (s0:va_state) (bN:va_codes) : Ghost ((sM:va_state) * (fM:va_fuel))
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (va_Block []) s0 fM sM
  ))

val va_lemma_ifElse_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) : Ghost (bool * va_state * va_state * va_fuel)
  (requires True)
  (ensures  (fun (cond, sM, sN, f0) ->
    cond == eval_ocmp s0 ifb /\
    sM == s0
  ))

val va_lemma_ifElseTrue_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) (f0:va_fuel) (sM:va_state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    eval_ocmp s0 ifb /\
    eval_code ct s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val va_lemma_ifElseFalse_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) (f0:va_fuel) (sM:va_state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    not (eval_ocmp s0 ifb) /\
    eval_code cf s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

let va_whileInv_total (b:ocmp) (c:va_code) (s0:va_state) (sN:va_state) (f0:va_fuel) : Type0 =
  eval_while_inv (While b c) s0 f0 sN

val va_lemma_while_total (b:ocmp) (c:va_code) (s0:va_state) : Ghost ((s1:va_state) * (f1:va_fuel))
  (requires True)
  (ensures fun (s1, f1) ->
    s1 == s0 /\
    eval_while_inv (While b c) s1 f1 s1
  )

val va_lemma_whileTrue_total (b:ocmp) (c:va_code) (s0:va_state) (sW:va_state) (fW:va_fuel) : Ghost ((s1:va_state) * (f1:va_fuel))
  (requires eval_ocmp sW b /\ valid_ocmp b sW)
  (ensures fun (s1, f1) -> s1 == sW /\ f1 == fW)

val va_lemma_whileFalse_total (b:ocmp) (c:va_code) (s0:va_state) (sW:va_state) (fW:va_fuel) : Ghost ((s1:va_state) * (f1:va_fuel))
  (requires
    valid_ocmp b sW /\
    not (eval_ocmp sW b) /\
    eval_while_inv (While b c) s0 fW sW
  )
  (ensures fun (s1, f1) ->
    s1 == sW /\
    eval_code (While b c) s0 f1 s1
  )

val va_lemma_whileMerge_total (c:va_code) (s0:va_state) (f0:va_fuel) (sM:va_state) (fM:va_fuel) (sN:va_state) : Ghost (fN:va_fuel)
  (requires
    While? c /\
    sN.ok /\
    valid_ocmp (While?.whileCond c) sM /\
    eval_ocmp sM (While?.whileCond c) /\
    eval_while_inv c s0 f0 sM /\
    eval_code (While?.whileBody c) sM fM sN
  )
  (ensures (fun fN ->
    eval_while_inv c s0 fN sN
  ))

val printer : Type0
val print_string : string -> FStar.All.ML unit
val print_header : printer -> FStar.All.ML unit
val print_proc : (name:string) -> (code:va_code) -> (label:int) -> (p:printer) -> FStar.All.ML unit
val print_footer : printer -> FStar.All.ML unit
val masm : printer
val gcc : printer
