module Semantics

open FStar.BaseTypes
open FStar.UInt64
(* REVIEW: Why can't I open this? 
open FStar.Int.Cast *)
open FStar.Map
open FStar.Mul

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

(* REVIEW: Should const be int instead of uint64?  Int gives more flexibility, but 
           it means that eval_operand has to return int, not uint64.
           Same question for the regs field in state below *)
type operand =
  | OConst: n:uint64 -> operand
  | OReg  : r:reg -> operand
  | OMem  : m:maddr -> operand

type dst_op = o:operand { not(OConst? o || (OReg? o && Rsp? (OReg?.r o) )) }

type ocmp =
  | OEq: o1:operand -> o2:operand -> ocmp
  | ONe: o1:operand -> o2:operand -> ocmp
  | OLe: o1:operand -> o2:operand -> ocmp
  | OGe: o1:operand -> o2:operand -> ocmp
  | OLt: o1:operand -> o2:operand -> ocmp
  | OGt: o1:operand -> o2:operand -> ocmp


type ins =
  | Mov64      : dst:dst_op -> src:operand -> ins
  | Add64      : dst:dst_op -> src:operand -> ins
  | AddLea64   : dst:dst_op -> src1:operand -> src2:operand -> ins
  | AddCarry64 : dst:dst_op -> src:operand -> ins
  | Sub64      : dst:dst_op -> src:operand -> ins
  | Mul64      : src:operand -> ins
  | IMul64     : dst:dst_op -> src:operand -> ins
  | Xor64      : dst:dst_op -> src:operand -> ins
  | Shr64      : dst:dst_op -> amt:operand -> ins
  | Shl64      : dst:dst_op -> amt:operand -> ins

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

(* map type from the F* library, it needs the key type to have decidable equality, not an issue here *)
type map (key:eqtype) (value:Type) = Map.t key value

(* TODO: Eventually this should be a map to bytes.  Simplifying for now *)
type mem = map int uint64

(* state type, noeq qualifier means that this type does not have decidable equality (because of the maps) *)
noeq type state = {
  ok  :bool;
  regs:map reg uint64;
  flags:uint64;
  mem :mem;
}

assume val invalid:uint64
assume val havoc : state -> ins -> Tot uint64

(* syntax for map accesses, m.[key] and m.[key] <- value *)
let op_String_Access     = sel
let op_String_Assignment = upd

(*
 * writing all the functions as Tot functions
 *)

(* REVIEW: Is it preferred for r:reg to proceed s:state?  Does it come down to which one (if any) we're more likely to want to curry? *)
let eval_reg (r:reg) (s:state) :uint64 =
  if s.regs `contains` r then s.regs.[r] else invalid

(*
let valid_resolved_addr (ptr:int) (m:mem) :bool =
  m `contains` ptr /\
  m `contains` ptr + 1 /\
  m `contains` ptr + 2 /\
  m `contains` ptr + 3 
*)

(* REVIEW: Is returning invalid the right thing to do here?  Seems like we want !state.ok if this happens *)
let eval_mem (ptr:int) (s:state) :uint64 =
  if s.mem `contains` ptr then s.mem.[ptr] else invalid

let eval_maddr (m:maddr) (s:state) :int =
  match m with
  | MConst n -> n
  | MReg reg offset -> (FStar.UInt64.v (eval_reg reg s)) + offset
  | MIndex _ _ _ _ -> 42
  (* TODO: Should be the following, but it doesn't type check for some reason
  | MIndex base scale index offset -> (FStar.UInt64.v (eval_reg base s)) + (scale * (FStar.UInt64.v (eval_reg index s))) + offset
  *)

let eval_operand (o:operand) (s:state) :uint64 =
  match o with
  | OConst n -> n
  | OReg r   -> eval_reg r s
  | OMem m   -> eval_mem (eval_maddr m s) s

(* REVIEW: Is it strange to have a dangling v before each term? 
   REVIEW: Do the boolean operators below mean what I think they mean? *)
let eval_ocmp (s:state) (c:ocmp) :bool =
  match c with
  | OEq o1 o2 -> v (eval_operand o1 s) =  v (eval_operand o2 s)
  | ONe o1 o2 -> v (eval_operand o1 s) <> v (eval_operand o2 s)
  | OLe o1 o2 -> v (eval_operand o1 s) <= v (eval_operand o2 s)
  | OGe o1 o2 -> v (eval_operand o1 s) >= v (eval_operand o2 s)
  | OLt o1 o2 -> v (eval_operand o1 s) < v (eval_operand o2 s)
  | OGt o1 o2 -> v (eval_operand o1 s) > v (eval_operand o2 s)

let update_reg (r:reg) (s:state) (v:uint64) :state = { s with regs = s.regs.[r] <- v }

let update_mem (ptr:int) (s:state) (v:uint64) :state = { s with mem = s.mem.[ptr] <- v }

let update_operand (o:dst_op) (s:state) (v:uint64) :state =
  match o with
  | OReg r   -> update_reg r s v
  | OMem m   -> update_mem (eval_maddr m s) s v

let update_operand_and_flags (o:dst_op) (s:state) (ins:ins) (v:uint64) :state =
  { (update_operand o s v) with flags = havoc s ins }

(* REVIEW: Is there a cleaner way to write this? *)
let cf (flags:uint64) :bool =
  (v (logand flags (uint_to_t 1))) > 0

(* REVIEW: Is there a way to write a numeric literal without a cast *)
let update_cf (flags:uint64) (cf:bool) :uint64 =
  if cf then logor flags (uint_to_t 1)
  else flags

(* REVIEW: How can I tell I got the constant on the next two lines correct? *)
let uint32_max = 0x100000000
let uint64_max = 0x10000000000000000

(* REVIEW: What's the best way to handle "valid shift amount" for shift instructions?  It depends on ins and state *)
let valid_shift_operand (o:operand) (s:state) :bool =
  (OConst? o && 0 <= v (OConst?.n o) && v (OConst?.n o) < 32) 
  || 
  ((OReg? o) && (Rcx? (OReg?.r o)) && v (eval_operand o s) < uint32_max)

let eval_ins (ins:ins) (s:state) :state =
  if not s.ok then s
  else
    match ins with 
    | Mov64 dst src -> update_operand dst s (eval_operand src s)
    | Add64 dst src -> update_operand_and_flags dst s ins (eval_operand dst s +%^ eval_operand src s)
    | AddLea64 dst src1 src2 -> update_operand_and_flags dst s ins (eval_operand src1 s +%^ eval_operand src2 s)
    | AddCarry64 dst src -> let old_carry = if cf(s.flags) then 1 else 0 in
			   let sum = v (eval_operand dst s) + v (eval_operand src s) + old_carry in			  
			   let new_carry = sum > uint64_max in
			   { update_operand dst s (uint_to_t (sum % uint64_max)) with flags = update_cf s.flags new_carry }
    | Sub64 dst src -> update_operand_and_flags dst s ins (eval_operand dst s -%^ eval_operand src s)
    | Mul64 src -> let product = v (eval_reg Rax s) * v (eval_operand src s) in
		  let hi = uint_to_t (product / uint64_max) in
		  let lo = uint_to_t (product % uint64_max) in
		  { update_reg Rax (update_reg Rdx s hi) lo with flags = havoc s ins }
    | IMul64 dst src -> update_operand_and_flags dst s ins (eval_operand dst s *%^ eval_operand src s)	  
    | Xor64 dst src -> update_operand_and_flags dst s ins (eval_operand dst s ^^ eval_operand src s)	  
    | Shr64 dst amt -> if valid_shift_operand amt s then
			 s
			 (* REVIEW: Why doesn't the following work?
			 update_operand_and_flags dst s ins (shift_right (eval_operand dst s) (UInt32.uint_to_t (v (eval_operand amt s)))) *)
		        (* update_operand_and_flags dst s ins (shift_right (eval_operand dst s) (uint64_to_uint32 (eval_operand amt s))) *)	  
		      else
			{ s with ok = false }
    | Shl64 dst amt -> s  (* TODO: Follow the format of Shr64, once it works *)


(*
 * the decreases clause
 *)
let decr (c:code) (s:state) :nat =
  match c with
  | While _ _ inv ->
    let n = v (eval_operand inv s) in
    if n >= 0 then n else 0
  | _             -> 0

(*
 * these functions return an option state
 * None case arises when the while loop invariant fails to hold
 *)

val eval_code:  c:code           -> s:state -> Tot (option state) (decreases %[c; decr c s; 1])
val eval_codes: l:codes          -> s:state -> Tot (option state) (decreases %[l])
val eval_while: c:code{While? c} -> s:state -> Tot (option state) (decreases %[c; decr c s; 0])

let rec eval_code c s =
  match c with
  | Ins ins                       -> Some (eval_ins ins s)
  | Block l                       -> eval_codes l s
  | IfElse ifCond ifTrue ifFalse  -> if eval_ocmp s ifCond then eval_code ifTrue s else eval_code ifFalse s
  | While _ _ _                   -> eval_while c s
    
and eval_codes l s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c s in
    if None? s_opt then None else eval_codes tl (Some?.v s_opt)
    
and eval_while c s_0 = (* trying to mimic the eval_while predicate using a function *)
  let While cond body inv = c in
  let n_0 = v (eval_operand inv s_0) in
  let b = eval_ocmp s_0 cond in

  if n_0 <= 0 then
    if b then None else Some s_0  //if loop invariant is <= 0, the guard must be false
  else  //loop invariant > 0
    if not b then None  //guard must evaluate to true
    else
      let s_opt = eval_code body s_0 in
      if None? s_opt then None
      else
        let s_1 = Some?.v s_opt in
	if not s_1.ok then Some s_1  //this is from the reference semantics, if ok flag is unset, return
	else
	  let n_1 = v (eval_operand inv s_1) in
	  if n_1 >= n_0 then None  //loop invariant must decrease
	  else eval_while c s_1
