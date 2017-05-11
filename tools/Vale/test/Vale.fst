module Vale

open Semantics
open FStar.BaseTypes
open FStar.Map

(***** Vale Interface *****)

(*
 * Aseems says, "what are the access qualifiers on Semantics and this interface?"
 *)

(* Type aliases *)
type va_bool = bool
type va_int = int
type va_codes = codes
type va_code = code

type va_state = state
type va_operand = operand
type va_dst_operand = dst_op
type va_shift_amt = operand
type va_cmp = operand
type va_register = reg

(* Constructors *)
let va_op_operand_reg (r:reg) :va_operand = OReg r
let va_const_operand (n:nat64) = OConst n
let va_const_shift_amt (n:nat64) :va_shift_amt = OConst n
let va_op_cmp_reg (r:reg) :va_cmp = OReg r
let va_const_cmp (n:nat64) :va_cmp = OConst n
let va_coerce_register_to_operand (r:va_register) :va_operand = OReg r
let va_op_register (r:reg) :va_register = r
let va_op_dst_operand_reg (r:reg{ not (Rsp? r) }) : va_dst_operand = OReg r
let va_coerce_operand_to_dst_operand (o:va_operand{ valid_dst o }) : va_dst_operand = o
let va_coerce_dst_operand_to_operand (o:va_dst_operand) : va_operand = o

(* Predicates *)
let va_is_src_operand_uint64 (o:operand) (s:va_state) = valid_operand o s
let va_is_dst_operand_uint64 (o:operand) (s:va_state) = valid_dst o
let va_is_dst_dst_operand_uint64 (o:va_dst_operand) (s:va_state) = valid_operand o s
let va_is_src_register_int (r:reg) (s:va_state) :bool = true
let va_is_dst_register (r:reg) (s:va_state) :bool = true
let va_is_src_shift_amt_uint64 (o:operand) (s:va_state) = valid_shift_operand o s

(* Getters *)
let va_get_ok (s:va_state) :bool = s.ok
let va_get_flags (s:va_state) :nat64 = s.flags
let va_get_reg (r:reg) (s:va_state) :nat64 = eval_reg r s
let va_get_mem (s:va_state) :mem = s.mem

(* Framing: va_update_foo means the two states are the same except for foo *)
let va_update_ok (sM:va_state) (sK:va_state) :va_state  = { sK with ok = sM.ok }
let va_update_flags  (sM:va_state) (sK:va_state) :va_state  = { sK with flags = sM.flags }
let va_update_reg (r:reg) (sM:va_state) (sK:va_state) :va_state = { sK with regs = sK.regs.[r] <- va_get_reg r sM }
let va_update_mem (sM:va_state) (sK:va_state) :va_state = { sK with mem = sM.mem }
let va_update_operand (o:operand) (sM:va_state) (sK:va_state) :va_state =
  match o with
  | OConst n -> sK
  | OReg r -> va_update_reg r sM sK
  | OMem m -> va_update_mem sM sK 
let va_update_dst_operand (o:dst_op) (sM:va_state) (sK:va_state) :va_state =
  va_update_operand o sM sK   
let va_update_register (r:reg) (sM:va_state) (sK:va_state) :va_state = va_update_reg r sM sK

(* Evaluation *)
let va_eval_operand_uint64 (s:va_state) (o:va_operand) :nat64 = eval_operand o s
let va_eval_dst_operand_uint64 (s:va_state) (o:va_dst_operand) :nat64 = eval_operand o s
let va_eval_shift_amt_uint64 (s:va_state) (o:va_shift_amt) : nat64 = eval_operand o s
let va_eval_cmp_uint64 (s:va_state) (r:va_cmp) :nat64 = eval_operand r s
let va_eval_register_uint64 (s:va_state) (r:va_register) :nat64 = eval_reg r s


(* Dealing with code *)
let va_CNil () :va_codes = []
let va_CCons (hd:va_code) (tl:va_codes) :va_codes = hd::tl
let va_Block (block:va_codes) :va_code = Block block
let va_IfElse (ifCond:ocmp) (ifTrue:va_code) (ifFalse:va_code) :va_code = IfElse ifCond ifTrue ifFalse
let va_While (whileCond:ocmp) (whileBody:va_code) (inv:operand) :va_code = While whileCond whileBody inv
let va_cmp_le (a:va_operand) (b:va_operand) :ocmp = OLe a b
let va_get_block (c:va_code{Block? c}) :va_codes = Block?.block c
let va_get_ifCond (c:code{IfElse? c}) :ocmp = IfElse?.ifCond c
let va_get_ifTrue (c:code{IfElse? c}) :code = IfElse?.ifTrue c
let va_get_ifFalse (c:code{IfElse? c}) :code = IfElse?.ifFalse c
let va_get_whileCond (c:code{While? c}) :ocmp = While?.whileCond c
let va_get_whileBody (c:code{While? c}) :code = While?.whileBody c


let va_state_eq (s_0:va_state) (s_1:va_state) :Type0 = 
  s_0.ok == s_1.ok /\
  Map.equal s_0.regs s_1.regs /\
  s_0.flags == s_1.flags /\
  Map.equal s_0.mem s_1.mem
  

let va_require (block:va_codes) (c:va_code) (s_0:va_state) (s_1:va_state) :Type0 =
  Cons? block                         /\
  Cons?.hd block == c                 /\
  Some s_1 == eval_code (va_Block block) s_0    /\
  (forall (r:reg). s_0.regs `contains` r)  //what is this?

let va_ensure (b_0:va_codes) (b_1:va_codes) (s_0:va_state) (s_1:va_state) (sN:va_state) :Type0 =
  Cons? b_0                         /\
  Cons?.tl b_0 == b_1                /\
  Some(s_1) == eval_code (Cons?.hd b_0) s_0     /\
  Some(sN)  == eval_code (va_Block b_1) s_1     /\
  (forall (r:reg). s_1.regs `contains` r)

(* the lemmas have out variables, so writing them as pure functions *)

(* abstract? *)

let va_lemma_block (b_0:va_codes) (s_0:state) (sN:state)
  :Pure (state * va_code * va_codes)
        (requires (Cons? b_0 /\ Some(sN) == eval_code (Block b_0) s_0))
        (ensures  (fun (s_1, c_1, b_1) -> b_0 == va_CCons c_1 b_1  /\
	                           Some(s_1) == eval_code c_1 s_0 /\
				   Some(sN) == eval_code (va_Block b_1) s_1))
  = let c_1::b_1 = b_0 in
    Some?.v (eval_code c_1 s_0), c_1, b_1

let va_lemma_empty (s_0:va_state) (sN:va_state)
  :Pure va_state (requires (Some(sN) == eval_code (Block (va_CNil ())) s_0))
                 (ensures  (fun sM -> sM == s_0 /\ sM == sN))
  = s_0

let va_lemma_ifElse (ifb:ocmp) (ct:code) (cf:code) (s_0:va_state) (sN:va_state)
  :Pure (bool * va_state)
        (requires (Some(sN) == eval_code (IfElse ifb ct cf) s_0))
	(ensures  (fun (cond, sM) -> cond == eval_ocmp s_0 ifb /\
	                          sM == s_0                 /\
				  Some(sN) == (if cond then eval_code ct sM else eval_code cf sM)))
  = eval_ocmp s_0 ifb, s_0

let va_whileInv (b:ocmp) (c:code{While? c}) (inv:operand) (s_0:va_state) (sN:va_state) =
  eval_operand inv s_0 >= 0           /\
  (forall (r:reg). s_0.regs `contains` r) /\
  Some(sN) == eval_while c s_0

let va_lemma_while (b:ocmp) (c:code) (inv:operand) (s_0:va_state) (sN:va_state)
  :Pure va_state
        (requires (Some(sN) == eval_code (While b c inv) s_0))
	(ensures  (fun s_1 -> Some(sN) == eval_while (While b c inv) s_0 /\ s_1 == s_0))
  = s_0

let va_lemma_whileTrue (b:ocmp) (c:code) (inv:operand) (s_0:va_state) (sN:va_state)
  :Pure (va_state * va_state)
        (requires (eval_operand inv s_0 > 0 /\
	           Some(sN) == eval_while (While b c inv) s_0))
	(ensures  (fun (s_0', s_1) -> s_0' == s_0         /\
	                          eval_ocmp s_0 b      /\
				  Some(s_1) == eval_code c s_0' /\
				  (if s_1.ok then Some(sN) == eval_while (While b c inv) s_1 else s_1 == sN)))
  = s_0, Some?.v (eval_code c s_0)

let va_lemma_whileFalse (b:ocmp) (c:code) (inv:operand) (s_0:va_state) (sN:va_state)
  :Pure va_state (requires (eval_operand inv s_0 == 0 /\
                            Some(sN) == eval_while (While b c inv) s_0))
		 (ensures  (fun s_1 -> s_0 == s_1 /\ s_1 == sN /\ not (eval_ocmp s_0 b)))
  = s_0

