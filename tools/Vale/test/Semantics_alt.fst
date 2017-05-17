module Semantics_alt

assume new type map (key:eqtype) (value:Type) : Type0

assume val sel: #key:eqtype -> #value:Type -> map key value -> key -> Tot value
assume val upd: #key:eqtype -> #value:Type -> map key value -> key -> value -> Tot (map key value)
assume val contains: #key:eqtype -> #value:Type -> map key value -> key -> Tot bool

assume val lemma_SelUpd1: #key:eqtype -> #value:Type -> m:map key value -> k:key -> v:value ->
                   Lemma (requires True) (ensures (sel (upd m k v) k == v))
		   [SMTPat (sel (upd m k v) k)]

assume val lemma_SelUpd2: #key:eqtype -> #value:Type -> m:map key value -> k1:key -> k2:key -> v:value ->
                   Lemma (requires True) (ensures (k2=!=k1 ==> sel (upd m k2 v) k1 == sel m k1))
                   [SMTPat (sel (upd m k2 v) k1)]

assume val lemma_InDomUpd1: #key:eqtype -> #value:Type -> m:map key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (contains (upd m k1 v) k2 == (k1=k2 || contains m k2)))
                     [SMTPat (contains (upd m k1 v) k2)]

assume new type map_equal (#key:eqtype) (#value:Type) (m1:map key value) (m2:map key value)

assume val lemma_equal_intro: #key:eqtype -> #value:Type -> m1:map key value -> m2:map key value ->
                       Lemma (requires (forall k. sel m1 k == sel m2 k /\
                                                  contains m1 k = contains m2 k))
                       (ensures (map_equal m1 m2))
                       [SMTPatT (map_equal m1 m2)]

assume val lemma_equal_elim: #key:eqtype -> #value:Type -> m1:map key value -> m2:map key value ->
                      Lemma (requires (map_equal m1 m2)) (ensures  (m1 == m2))
                      [SMTPatT (map_equal m1 m2)]

(* Define some transparently refined int types, 
   since we only use them in specs, not in emitted code *)
let nat32_max = 0x100000000
let nat64_max = 0x10000000000000000
let _ = assert_norm (pow2 32 = nat32_max)    (* Sanity check our constant *)
let _ = assert_norm (pow2 64 = nat64_max)    (* Sanity check our constant *)

type nat64 = x:int{0 <= x && x < nat64_max}

(* syntax for map accesses, m.[key] and m.[key] <- value *)
let op_String_Access     = sel
let op_String_Assignment = upd

(* Define the operators we support *)
type reg =
  | Rax
  | Rbx
  | Rcx
  | Rdx
  | Rsi
  | Rdi
  | Rbp
  | Rsp
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15

type maddr =
  | MConst : n:nat -> maddr
  | MReg   : r:reg -> offset:int -> maddr
  | MIndex : base:reg -> scale:int -> index:reg -> offset:int -> maddr

type operand =
  | OConst: n:nat64 -> operand
  | OReg  : r:reg -> operand
  | OMem  : m:maddr -> operand

let valid_dst (o:operand) : bool =
  not(OConst? o || (OReg? o && Rsp? (OReg?.r o) ))

type dst_op = o:operand { valid_dst o }

assume new type ocmp : Type0

assume new type ins : Type0

(*
 * while construct has a loop invariant
 * currently it is a mem_opr, but we could introduce an expression language to enrich it
 *)
type code =
  | Ins   : ins:ins -> code
  | Block : block:list code -> code
  | IfElse: ifCond:ocmp -> ifTrue:code -> ifFalse:code -> code
  | While : whileCond:ocmp -> whileBody:code -> inv:operand -> code

type codes = list code

(* TODO: Eventually this should be a map to bytes.  Simplifying for now *)
type mem = map int nat64

(* state type, noeq qualifier means that this type does not have decidable equality (because of the maps) *)
noeq type state = {
  ok  :bool;
  regs:map reg nat64;
  flags:nat64;
  mem :mem;
}

let eval_reg (r:reg) (s:state) :nat64 =
  s.regs.[r]

let eval_mem (ptr:int) (s:state) :nat64 =
  s.mem.[ptr]

let eval_maddr (m:maddr) (s:state) :int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> (eval_reg reg s) + offset
    | MIndex base scale index offset -> eval_reg base s + scale * eval_reg index s + offset

let eval_operand (o:operand) (s:state) :nat64 =
  match o with
  | OConst n -> n
  | OReg r   -> eval_reg r s
  | OMem m   -> eval_mem (eval_maddr m s) s

assume val cf : (flags:nat64) -> bool

let valid_maddr (m:maddr) (s:state) :bool =
  s.mem `contains` (eval_maddr m s)

let valid_operand (o:operand) (s:state) :bool =
  not (OMem? o) || (OMem? o && valid_maddr (OMem?.m o) s)

let valid_shift_operand (o:operand) (s:state) :bool =
  (OConst? o && 0 <= OConst?.n o && OConst?.n o < 32) 
  || 
  ((OReg? o) && (Rcx? (OReg?.r o)) && eval_operand o s < nat32_max)

(*
 * these functions return an option state
 * None case arises when the while loop invariant fails to hold
 *)

assume val eval_code:  c:code           -> s:state -> Tot (option state)
assume val eval_codes: l:codes          -> s:state -> Tot (option state)
