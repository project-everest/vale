module Semantics

open FStar.BaseTypes
open FStar.Map

(* Define some transparently refined int types,
   since we only use them in specs, not in emitted code *)
let nat32_max = 0x100000000
let nat64_max = 0x10000000000000000
abstract (* Sanity check our constants *)
let _ = assert_norm (pow2 32 = nat32_max);    
        assert_norm (pow2 64 = nat64_max)
        
type nat64 = n:nat{n < nat64_max}
type uint64 = FStar.UInt64.t

(* map type from the F* library, it needs the key type to have decidable equality, not an issue here *)
unfold 
type map (key:eqtype) (value:Type) = Map.t key value

(* syntax for map accesses, m.[key] and m.[key] <- value *)
unfold 
let op_String_Access     = sel
unfold 
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
  | OConst: n:uint64 -> operand
  | OReg  : r:reg -> operand
  | OMem  : m:maddr -> operand

let valid_dst (o:operand) : bool =
  not(OConst? o || (OReg? o && Rsp? (OReg?.r o) ))

type dst_op = o:operand { valid_dst o }

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
  | And64      : dst:dst_op -> src:operand -> ins
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

(* TODO: Eventually this should be a map to bytes.  Simplifying for now *)
type mem = map int uint64

(* state type, noeq qualifier means that this type does not have decidable equality (because of the maps) *)
noeq type state = {
  ok  :bool;
  regs:map reg uint64;
  flags:uint64;
  mem :mem;
}

assume val havoc : state -> ins -> Tot uint64

(*
 * writing all the functions as Tot functions
 *)
let eval_reg (r:reg) (s:state) :uint64 =
  s.regs.[r]

(*
let valid_resolved_addr (ptr:int) (m:mem) :bool =
  m `contains` ptr /\
  m `contains` ptr + 1 /\
  m `contains` ptr + 2 /\
  m `contains` ptr + 3
*)

let eval_mem (ptr:int) (s:state) :uint64 =
  s.mem.[ptr]

let eval_maddr (m:maddr) (s:state) :int =
  let open FStar.UInt64 in
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> v (eval_reg reg s) + offset
    | MIndex base scale index offset -> v (eval_reg base s) + scale * v (eval_reg index s) + offset

let eval_operand (o:operand) (s:state) :uint64 =
  match o with
  | OConst n -> n
  | OReg r   -> eval_reg r s
  | OMem m   -> eval_mem (eval_maddr m s) s

let eval_ocmp (s:state) (c:ocmp) :bool =
  let open FStar.UInt64 in
  match c with
  | OEq o1 o2 -> eval_operand o1 s = eval_operand o2 s
  | ONe o1 o2 -> eval_operand o1 s <> eval_operand o2 s
  | OLe o1 o2 -> eval_operand o1 s <=^ eval_operand o2 s
  | OGe o1 o2 -> eval_operand o1 s >=^ eval_operand o2 s
  | OLt o1 o2 -> eval_operand o1 s <^ eval_operand o2 s
  | OGt o1 o2 -> eval_operand o1 s >^ eval_operand o2 s

let update_reg' (r:reg) (v:uint64) (s:state) :state = { s with regs = s.regs.[r] <- v }

let update_mem (ptr:int) (v:uint64) (s:state) :state = { s with mem = s.mem.[ptr] <- v }

let update_operand_preserve_flags' (o:dst_op) (v:uint64) (s:state) :state =
  match o with
  | OReg r   -> update_reg' r v s
  | OMem m   -> update_mem (eval_maddr m s) v s

let update_operand' (o:dst_op) (ins:ins) (v:uint64) (s:state) :state =
  { (update_operand_preserve_flags' o v s) with flags = havoc s ins }

open FStar.UInt64

(* REVIEW: Will we regret exposing a mod here?  Should flags be something with more structure? *)
let cf (flags:uint64) :bool =
  v flags % 2 = 1

let update_cf (flags:uint64) (new_cf:bool) : (new_flags:uint64{cf new_flags == new_cf}) =
  if new_cf then
    if not (cf flags) then
      flags +^ 1uL
    else
      flags
  else
    if (cf flags) then
      flags -^ 1uL
    else
      flags

let valid_maddr (m:maddr) (s:state) :bool =
  s.mem `contains` (eval_maddr m s)

let valid_operand (o:operand) (s:state) :bool =
  not (OMem? o) || (OMem? o && valid_maddr (OMem?.m o) s)

let valid_shift_operand (o:operand) (s:state) :bool =
  (OConst? o && 0uL <=^ OConst?.n o && OConst?.n o <^ 32uL)
  ||
  ((OReg? o) && (Rcx? (OReg?.r o)) && v (eval_operand o s) < nat32_max)


let st (a:Type) = state -> a * state

unfold
let return (#a:Type) (x:a) :st a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok=s0.ok && s1.ok && s2.ok}

unfold
let get :st state =
  fun s -> s, s

unfold
let set (s:state) :st unit =
  fun _ -> (), s

unfold
let fail :st unit =
  fun s -> (), {s with ok=false}

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : state = snd (f s)

(*
let check_eval_operand (valid: operand -> state -> bool) (o:operand) : uint64 * st =
 check (valid o);;
 s <-- get();
 (2, return s)

 (eval_operand o s, return s)
*)
unfold
let update_operand_preserve_flags (dst:dst_op) (v:uint64) :st unit =
  check (valid_operand dst);;
  s <-- get;
  set (update_operand_preserve_flags' dst v s)

(* Default version havocs flags *)
unfold
let update_operand (dst:dst_op) (ins:ins) (v:uint64) :st unit =
  check (valid_operand dst);;
  s <-- get;
  set (update_operand' dst ins v s)

let update_reg (r:reg) (v:uint64) :st unit =
  s <-- get;
  set (update_reg' r v s)

let update_flags (new_flags:uint64) :st unit =
  s <-- get;
  set ( { s with flags = new_flags } )

abstract
let example (dst:dst_op) (src:operand) :st unit =
  check (valid_operand dst);;
  check (valid_operand src);;
  update_operand_preserve_flags dst 2uL

abstract
let test (dst:dst_op) (src:operand) (s:state) :state =
  run (example dst src) s

abstract
let logxor (x:int) (y:int) : int =
  if FStar.UInt.fits x 64
  && FStar.UInt.fits y 64
  then FStar.UInt.logxor #64 x y
  else -1

let logxor_uint64 (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x 64 /\
                    FStar.UInt.fits y 64) ==>
                    logxor x y = FStar.UInt.logxor #64 x y)
          [SMTPat (logxor x y)]
  = ()          

abstract
let logand (x:int) (y:int) : int =
  if FStar.UInt.fits x 64
  && FStar.UInt.fits y 64
  then FStar.UInt.logand #64 x y
  else -1

let logand_uint64 (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x 64 /\
                    FStar.UInt.fits y 64) ==>
                    logand x y = FStar.UInt.logand #64 x y)
          [SMTPat (logand x y)]
  = ()          

abstract
let shift_right (x:int) (y:int) : int =
  if FStar.UInt.fits x 64
  && y >= 0
  then FStar.UInt.shift_right #64 x y
  else -1

let shift_right_uint64 (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x 64 /\
                    y >= 0) ==>
                   shift_right x y = FStar.UInt.shift_right #64 x y)
          [SMTPat (shift_right x y)]
  = ()          

abstract
let shift_left (x:int) (y:int) : int =
  if FStar.UInt.fits x 64
  && y >= 0
  then FStar.UInt.shift_left #64 x y
  else -1

let shift_left_uint64 (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x 64 /\
                    y >= 0) ==>
                   shift_left x y = FStar.UInt.shift_left #64 x y)
          [SMTPat (shift_left x y)]
  = ()          

let u (i:int{FStar.UInt.fits i 64}) : uint64 = FStar.UInt64.uint_to_t i

let eval_ins (ins:ins) : st unit =
  let open FStar.Mul in
  s <-- get;
  match ins with
  | Mov64 dst src ->
    check (valid_operand src);;
    update_operand_preserve_flags dst (eval_operand src s)

  | Add64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (eval_operand dst s +%^ eval_operand src s)

  | AddLea64 dst src1 src2 ->
    check (valid_operand src1);;
    check (valid_operand src2);;
    update_operand_preserve_flags dst (eval_operand src1 s +?^ eval_operand src2 s) //TODO: use the modulo version

  | AddCarry64 dst src ->
    let old_carry = if cf(s.flags) then 1 else 0 in
    let sum = v (eval_operand dst s) + v (eval_operand src s) + old_carry in
    let new_carry = sum >= nat64_max in
    check (valid_operand src);;
    update_operand dst ins (uint_to_t (sum % nat64_max));;
    update_flags (update_cf s.flags new_carry)

  | Sub64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (eval_operand dst s -%^ eval_operand src s)

  | Mul64 src ->
    let hi = eval_reg Rax s */^ eval_operand src s in
    let lo = eval_reg Rax s *%^ eval_operand src s in
    check (valid_operand src);;
    update_reg Rax lo;;
    update_reg Rdx hi;;
    update_flags (havoc s ins)

  | IMul64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (eval_operand dst s *%^ eval_operand src s)

  | Xor64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (u (v (eval_operand dst s) `logxor` v (eval_operand src s)))

  | And64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (u (v (eval_operand dst s) `logand` v (eval_operand src s)))

  | Shr64 dst amt ->
    check (valid_shift_operand amt);;
    update_operand dst ins (u (v (eval_operand dst s) `shift_right` v (eval_operand amt s)))

  | Shl64 dst amt ->
    check (valid_shift_operand amt);;
    update_operand dst ins (u (v (eval_operand dst s) `shift_left` v (eval_operand amt s)))

  | _ -> fail

(*
 * the decreases clause
 *)
let decr (c:code) (s:state) :nat =
  match c with
  | While _ _ inv ->
    let n = eval_operand inv s in
    if v n >= 0 then v n else 0
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
  | Ins ins                       -> Some (run (eval_ins ins) s)
  | Block l                       -> eval_codes l s
  | IfElse ifCond ifTrue ifFalse  -> if eval_ocmp s ifCond then eval_code ifTrue s else eval_code ifFalse s
  | While _ _ _                   -> eval_while c s

and eval_codes l s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c s in
    if None? s_opt then None else eval_codes tl (Some?.v s_opt)

and eval_while c s0 = (* trying to mimic the eval_while predicate using a function *)
  let While cond body inv = c in
  let n0 = eval_operand inv s0 in
  let b = eval_ocmp s0 cond in

  if v n0 <= 0 then
    if b then None else Some s0  //if loop invariant is <= 0, the guard must be false
  else  //loop invariant > 0
    if not b then None  //guard must evaluate to true
    else
      let s_opt = eval_code body s0 in
      if None? s_opt then None
      else
        let s1 = Some?.v s_opt in
        if not s1.ok then Some s1  //this is from the reference semantics, if ok flag is unset, return
        else
          let n1 = eval_operand inv s1 in
          if v n1 >= v n0 then None  //loop invariant must decrease
          else eval_while c s1
