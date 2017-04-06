module Semantics

type reg =
  | EAX
  | EBX

type opr =
  | OReg  : r:reg -> opr
  | OConst: n:int -> opr

type ocmp =
  | OLe: o1:opr -> o2:opr -> ocmp

type mem_opr =
  | OMem: base:reg -> offset:int -> mem_opr
  | OOpr: o:opr -> mem_opr

type ins =
  | InsImm : dstImm:reg -> imm:int -> ins
  | InsIncr: dstIncr:mem_opr -> ins
  | InsAdd : dstAdd:reg -> srdAdd:opr -> ins

(*
 * while construct has a loop invariant
 * currently it is a mem_opr, but we can introduce an expression language to enrich it
 *)
type code =
  | Ins   : ins:ins -> code
  | Block : block:list code -> code
  | IfElse: ifCond:ocmp -> ifTrue:code -> ifFalse:code -> code
  | While : whileCond:ocmp -> whileBody:code -> inv:mem_opr -> code

type codes = list code

type map (key:eqtype) (value:Type) = Map.t key value

noeq type state = {
  ok  :bool;
  regs:map reg int;
  mem :map int int
}

assume val empty_reg:int

open FStar.Map

let op_String_Access     = sel
let op_String_Assignment = upd

let eval_reg (r:reg) (s:state) :int =
  if s.regs `contains` r then s.regs.[r] else empty_reg

let eval_mem (ptr:int) (s:state) :int =
  if s.mem `contains` ptr then s.mem.[ptr] else empty_reg

let update_reg (r:reg) (s:state) (i:int) :state = { s with regs = s.regs.[r] <- i }

let update_mem (ptr:int) (s:state) (i:int) :state = { s with mem = s.mem.[ptr] <- i }

let eval_opr (o:opr) (s:state) :int =
  match o with
  | OReg r   -> eval_reg r s
  | OConst n -> n

let update_opr (o:opr) (s:state) (i:int) :state =
  match o with
  | OReg r   -> update_reg r s i
   | OConst _ -> { s with ok = false }

let eval_mem_opr (o:mem_opr) (s:state) :int =
  match o with
  | OMem base offset -> eval_mem ((eval_reg base s) + offset) s
  | OOpr o           -> eval_opr o s

let update_mem_opr (o:mem_opr) (s:state) (i:int) :state =
  match o with
  | OMem base offset -> update_mem ((eval_reg base s) + offset) s i
  | OOpr o           -> update_opr o s i

let mem_opr_ok (o:mem_opr) (s:state) :bool =
  match o with
  | OMem base offset -> s.mem `contains` ((eval_reg base s) + offset)
  | OOpr _           -> true

let eval_ocmp (s:state) (c:ocmp) :bool =
  match c with
  | OLe o1 o2 -> (eval_opr o1 s) <= (eval_opr o2 s)

let eval_ins_fn (ins:ins) (s:state) :state =
  if not s.ok then s
  else
    match ins with
    | InsImm dstImm imm    -> update_reg dstImm s imm
    | InsIncr dstIncr      ->
      if mem_opr_ok dstIncr s
      then update_mem_opr dstIncr s ((eval_mem_opr dstIncr s) + 1)
      else { s with ok = false}
    | InsAdd dstAdd srcAdd -> update_reg dstAdd s ((eval_reg dstAdd s) + (eval_opr srcAdd s))

(*
 * the decreases clause
 *)
let decr (c:code) (s:state) :nat =
  match c with
  | While _ _ inv ->
    let n = eval_mem_opr inv s in
    if n >= 0 then n else 0
  | _             -> 0

val eval_code_fn:  c:code           -> s:state -> Tot (option state) (decreases %[c; decr c s; 1])
val eval_codes_fn: l:codes          -> s:state -> Tot (option state) (decreases %[l])
val eval_while_fn: c:code{While? c} -> s:state -> Tot (option state) (decreases %[c; decr c s; 0])

let rec eval_code_fn c s =
  match c with
  | Ins ins                       -> Some (eval_ins_fn ins s)
  | Block l                       -> eval_codes_fn l s
  | IfElse ifCond ifTrue ifFalse  -> if eval_ocmp s ifCond then eval_code_fn ifTrue s else eval_code_fn ifFalse s
  | While _ _ _                   -> eval_while_fn c s
    
and eval_codes_fn l s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code_fn c s in
    if None? s_opt then None else eval_codes_fn tl (Some?.v s_opt)
    
and eval_while_fn c s_0 = (* trying to mimic the eval_while predicate using a function *)
  let While cond body inv = c in
  let n_0 = eval_mem_opr inv s_0 in
  let b = eval_ocmp s_0 cond in

  if n_0 <= 0 then
    if b then None else Some s_0
  else
    if not b then None
    else
      let s_opt = eval_code_fn body s_0 in
      if None? s_opt then None
      else
        let s_1 = Some?.v s_opt in
	if not s_1.ok then Some s_1
	else
	  let n_1 = eval_mem_opr inv s_1 in
	  if n_1 >= n_0 then None
	  else eval_while_fn c s_1

(* now define the predicates as in the reference semantics *)
let eval_ins (ins:ins) (s_0:state) (s_1:state) :Type0 = s_1 == eval_ins_fn ins s_0

let eval_block (block:codes) (s_0:state) (sN:state) :Type0 =
  eval_code_fn (Block block) s_0 == Some sN

let eval_while (b:ocmp) (c:code) (inv:mem_opr) (s_0:state) (sN:state) :Type0 =
  eval_while_fn (While b c inv) s_0 == Some sN

let eval_code (c:code) (s_0:state) (sN:state) :Type0 =
  eval_code_fn c s_0 == Some sN

(***** Vale Interface *****)

(*
 * what are the access qualifiers on the semantics above and interface below?
 *)

type va_bool = bool
type va_int = int
type va_codes = codes
type va_code = code

type va_state = state
let va_get_ok (s:va_state) :bool = s.ok
let va_get_reg (r:reg) (s:va_state) :int = eval_reg r s
let va_get_mem (s:va_state) :map int int = s.mem
let va_update_ok (sM:va_state) (sK:va_state) :va_state  = { sK with ok = sM.ok }
let va_update_reg (r:reg) (sM:va_state) (sK:va_state) :va_state = { sK with regs = sK.regs.[r] <- va_get_reg r sM }
let va_update_mem (sM:va_state) (sK:va_state) :va_state = { sK with mem = sM.mem }


type va_register = reg
let va_op_register (r:reg) :va_register = r
let va_is_src_register_int (r:reg) (s:va_state) :bool = true
let va_is_dst_register (r:reg) (s:va_state) :bool = true
let va_update_register (r:reg) (sM:va_state) (sK:va_state) :va_state = va_update_reg r sM sK
let va_eval_register_int (s:va_state) (r:va_register) :int = eval_reg r s

type va_operand = opr
let va_op_operand_reg (r:reg) :va_operand = OReg r
let va_is_src_operand_int (o:opr) (s:va_state) = true
let va_is_dst_operand_int (o:opr) (s:va_state) = OReg? o
let va_const_operand (o:opr{OReg? o}) (sM:va_state) (sK:va_state) :va_state = va_update_reg (OReg?.r o) sM sK
let va_eval_operand_int (s:va_state) (o:va_operand) :int = eval_opr o s

type va_mem_operand = mem_opr
let va_op_mem_operand_reg (r:reg) :va_mem_operand = OOpr (OReg r)
let va_op_mem_operand_operand (o:opr) :va_mem_operand = OOpr o
let va_is_src_mem_operand_int (o:mem_opr) (s:va_state) :bool = mem_opr_ok o s
let va_is_dst_mem_operand_int (o:mem_opr) (s:va_state) :bool = mem_opr_ok o s && (if OOpr? o then OReg? (OOpr?.o o) else true)
let va_mem_const_operand (x:int) :va_mem_operand = OOpr (OConst x)
let va_update_mem_operand (o:mem_opr{OOpr? o ==> OReg? (OOpr?.o o)}) (sM:va_state) (sK:va_state) :va_state =
  match o with
  | OMem base offset -> { sK with mem = sK.mem.[(eval_reg base sK) + offset] <- eval_mem_opr o sM }
  | OOpr o           -> va_update_reg (OReg?.r o) sM sK
let va_eval_mem_operand_int (s:va_state) (o:va_mem_operand) :int = eval_mem_opr o s

type va_cmp = opr
let va_op_cmp_reg (r:reg) :va_cmp = OReg r
let va_const_cmp (x:int) :va_cmp = OConst x
let va_eval_cmp_int (s:va_state) (r:va_cmp) :int = eval_opr r s

let va_coerce_register_to_operand (r:va_register) :va_operand = OReg r

let va_CNil () :va_codes = []
let va_CCons (hd:va_code) (tl:va_codes) :va_codes = hd::tl
let va_Block (block:va_codes) :va_code = Block block
let va_IfElse (ifCond:ocmp) (ifTrue:va_code) (ifFalse:va_code) :va_code = IfElse ifCond ifTrue ifFalse
let va_While (whileCond:ocmp) (whileBody:va_code) (inv:mem_opr) :va_code = While whileCond whileBody inv
let va_cmp_le (a:va_operand) (b:va_operand) :ocmp = OLe a b
let va_get_block (c:va_code{Block? c}) :va_codes = Block?.block c
let va_get_ifCond (c:code{IfElse? c}) :ocmp = IfElse?.ifCond c
let va_get_ifTrue (c:code{IfElse? c}) :code = IfElse?.ifTrue c
let va_get_ifFalse (c:code{IfElse? c}) :code = IfElse?.ifFalse c
let va_get_whileCond (c:code{While? c}) :ocmp = While?.whileCond c
let va_get_whileBody (c:code{While? c}) :code = While?.whileBody c


let va_state_eq (s_0:va_state) (s_1:va_state) :Type0 = s_0 == s_1

let va_require (block:va_codes) (c:va_code) (s_0:va_state) (s_1:va_state) :Type0 =
  Cons? block                         /\
  Cons?.hd block == c                 /\
  eval_code (va_Block block) s_0 s_1     /\
  (forall (r:reg). s_0.regs `contains` r)  //what is this?

let va_ensure (b_0:va_codes) (b_1:va_codes) (s_0:va_state) (s_1:va_state) (sN:va_state) :Type0 =
  Cons? b_0                         /\
  Cons?.tl b_0 == b_1                /\
  eval_code (Cons?.hd b_0) s_0 s_1     /\
  eval_code (va_Block b_1) s_1 sN     /\
  (forall (r:reg). s_1.regs `contains` r)

(* the lemmas have out variables, so writing them as pure functions *)

(* abstract? *)

let va_lemma_block (b_0:va_codes) (s_0:state) (sN:state)
  :Pure (state * va_code * va_codes)
        (requires (Cons? b_0 /\ eval_code (Block b_0) s_0 sN))
        (ensures  (fun (s_1, c_1, b_1) -> b_0 == va_CCons c_1 b_1  /\
	                           eval_code c_1 s_0 s_1 /\
				   eval_code (va_Block b_1) s_1 sN))
  = let c_1::b_1 = b_0 in
    Some?.v (eval_code_fn c_1 s_0), c_1, b_1

let va_lemma_empty (s_0:va_state) (sN:va_state)
  :Pure va_state (requires (eval_code (Block (va_CNil ())) s_0 sN))
                 (ensures  (fun sM -> sM == s_0 /\ sM == sN))
  = s_0

let va_lemma_ifElse (ifb:ocmp) (ct:code) (cf:code) (s_0:va_state) (sN:va_state)
  :Pure (bool * va_state)
        (requires (eval_code (IfElse ifb ct cf) s_0 sN))
	(ensures  (fun (cond, sM) -> cond == eval_ocmp s_0 ifb /\
	                          sM == s_0                 /\
				  (if cond then eval_code ct sM sN else eval_code cf sM sN)))
  = eval_ocmp s_0 ifb, s_0

let va_whileInv (b:ocmp) (c:code) (inv:mem_opr) (s_0:va_state) (sN:va_state) =
  eval_mem_opr inv s_0 >= 0           /\
  (forall (r:reg). s_0.regs `contains` r) /\
  eval_while b c inv s_0 sN

let va_lemma_while (b:ocmp) (c:code) (inv:mem_opr) (s_0:va_state) (sN:va_state)
  :Pure va_state
        (requires (eval_code (While b c inv) s_0 sN))
	(ensures  (fun s_1 -> eval_while b c inv s_0 sN /\ s_1 == s_0))
  = s_0

let va_lemma_whileTrue (b:ocmp) (c:code) (inv:mem_opr) (s_0:va_state) (sN:va_state)
  :Pure (va_state * va_state)
        (requires (eval_mem_opr inv s_0 > 0 /\
	           eval_while b c inv s_0 sN))
	(ensures  (fun (s_0', s_1) -> s_0' == s_0           /\
	                          eval_ocmp s_0 b      /\
				  eval_code c s_0' s_1 /\
				  (if s_1.ok then eval_while b c inv s_1 sN else s_1 == sN)))
  = s_0, Some?.v (eval_code_fn c s_0)

let va_lemma_whileFalse (b:ocmp) (c:code) (inv:mem_opr) (s_0:va_state) (sN:va_state)
  :Pure va_state (requires (eval_mem_opr inv s_0 == 0 /\
                            eval_while b c inv s_0 sN))
		 (ensures  (fun s_1 -> s_0 == s_1 /\ s_1 == sN /\ not (eval_ocmp s_0 b)))
  = s_0
