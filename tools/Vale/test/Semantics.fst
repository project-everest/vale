module Semantics

open FStar.BaseTypes
open FStar.Map

(* Define some transparently refined int types, 
   since we only use them in specs, not in emitted code *)
let nat32_max = 0x100000000
let nat64_max = 0x10000000000000000
let _ = assert_norm (pow2 32 = nat32_max)    (* Sanity check our constant *)
let _ = assert_norm (pow2 64 = nat64_max)    (* Sanity check our constant *)

type nat64 = x:int{0 <= x && x < nat64_max}

(* map type from the F* library, it needs the key type to have decidable equality, not an issue here *)
type map (key:eqtype) (value:Type) = Map.t key value

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

(* TODO: Eventually this should be a map to bytes.  Simplifying for now *)
type mem = map int nat64

(* state type, noeq qualifier means that this type does not have decidable equality (because of the maps) *)
noeq type state = {
  ok  :bool;
  regs:map reg nat64;
  flags:nat64;
  mem :mem;
}

assume val havoc : state -> ins -> Tot nat64

type reader (a:Type) = state -> a

noeq type eval_t = {
  get_flags   :unit -> reader nat64;
  eval_reg    :reg -> reader nat64;
  eval_mem    :int -> reader nat64;
  eval_maddr  :maddr -> reader int;
  eval_operand:operand -> reader nat64;
  eval_ocmp   :ocmp -> reader bool
}

let eval :eval_t =
  let return (#a:Type) (x:a) :reader a = fun s -> x in
  let bind (#a:Type) (#b:Type) (f:reader a) (g:a -> reader b) :reader b =
    fun s -> let x = f s in
          g x s
  in
  let get () :reader state = fun s -> s in

  let get_flags :unit -> reader nat64 = fun _ -> s <-- get (); return s.flags in
  let eval_reg :reg -> reader nat64 = fun r -> s <-- get (); return s.regs.[r] in
  let eval_mem :int -> reader nat64 = fun ptr -> s <-- get (); return s.mem.[ptr] in
  let eval_maddr :maddr -> reader int = fun m ->
    let open FStar.Mul in
    match m with
    | MConst n -> return n
    | MReg r offset ->
      x <-- eval_reg r;
      return (x + offset)
    | MIndex base scale index offset ->
      x <-- eval_reg base;
      y <-- eval_reg index;    
      return (x + scale * y + offset)
  in
  let eval_operand :operand -> reader nat64 = fun o ->
    match o with
    | OConst n -> return n
    | OReg r   -> eval_reg r
    | OMem m   ->
      x <-- eval_maddr m;
      eval_mem x
  in
  let eval_ocmp :ocmp -> reader bool = fun c ->
    match c with
    | OEq o1 o2 -> 
      x <-- eval_operand o1;
      y <-- eval_operand o2;
      return (x = y)
    | ONe o1 o2 -> 
      x <-- eval_operand o1;
      y <-- eval_operand o2;
      return (x <> y)
    | OLe o1 o2 ->
      x <-- eval_operand o1;
      y <-- eval_operand o2;
      return (x <= y)
    | OGe o1 o2 ->
      x <-- eval_operand o1;
      y <-- eval_operand o2;
      return (x >= y)
    | OLt o1 o2 ->
      x <-- eval_operand o1;
      y <-- eval_operand o2;
      return (x < y)
    | OGt o1 o2 ->
      x <-- eval_operand o1;
      y <-- eval_operand o2;
      return (x > y)
  in

  {
    get_flags = get_flags;
    eval_reg = eval_reg;
    eval_mem = eval_mem;
    eval_maddr = eval_maddr;
    eval_operand = eval_operand;
    eval_ocmp = eval_ocmp
  }

type st (a:Type) = state -> (option a * state)

unfold let lift (#a:Type) (f:reader a) :st a =
  fun s -> let x = f s in
        (Some x, s)

unfold let return (#a:Type) (x:a) :st a =
  fun s -> (Some x, s)

unfold let bind (#a:Type) (#b:Type) (f:st a) (g:a -> st b) :st b =
  fun s ->
    let (x_opt, s) = f s in
    if None? x_opt then (None, { s with ok = false})
    else g (Some?.v x_opt) s

let get () :st state =
  fun s -> (Some s, s)
  
let set (s:state) :st unit =
  fun _ -> (Some (), s)
  
let fail () :st unit =
  s <-- get ();
  set ({s with ok = false})

let update_reg (r:reg) (v:nat64) :st unit =
  s <-- get ();
  set ({s with regs = s.regs.[r] <- v})

let update_mem (ptr:int) (v:nat64) :st unit =
  s <-- get ();
  set ({s with mem = s.mem.[ptr] <- v})

let update_operand_preserve_flags' (o:dst_op) (v:nat64) :st unit =
  match o with
  | OReg r   -> update_reg r v
  | OMem m   ->
    x <-- lift (eval.eval_maddr m);
    update_mem x v

let update_operand' (o:dst_op) (ins:ins) (v:nat64) :st unit =
  s0 <-- get ();
  update_operand_preserve_flags' o v;;
  s1 <-- get ();
  set ({s1 with flags = havoc s0 ins})

(* REVIEW: Will we regret exposing a mod here?  Should flags be something with more structure? *)
let cf (flags:nat64) :bool =
  flags % 2 = 1

let update_cf (flags:nat64) (new_cf:bool) : (new_flags:nat64{cf new_flags == new_cf}) =
  if new_cf then
    if not (cf flags) then
      flags + 1
    else
      flags
  else 
    if (cf flags) then
      flags - 1
    else
      flags

let check (b:bool) :st unit =
  if b then return () else fail ()

let valid_maddr_b (m:maddr) (s:state) :bool =
  let x = eval.eval_maddr m s in
  s.mem `contains` x

let valid_maddr (m:maddr) :st unit =
  s <-- get ();
  check (valid_maddr_b m s)

let valid_operand_b (o:operand) (s:state) :bool =
  not (OMem? o) || (OMem? o && valid_maddr_b (OMem?.m o) s)

let valid_operand (o:operand) :st unit =
  s <-- get ();
  check (valid_operand_b o s)

let valid_shift_operand_b (o:operand) (s:state) :bool =
  (OConst? o && 0 <= OConst?.n o && OConst?.n o < 32) 
  || 
  ((OReg? o) && (Rcx? (OReg?.r o)) && eval.eval_operand o s < nat32_max)

let valid_shift_operand (o:operand) :st unit =
  s <-- get ();
  check (valid_shift_operand_b o s)

(*
let check_eval_operand (valid: operand -> state -> bool) (o:operand) : nat64 * st =
 check (valid o);;
 s <-- get();
 (2, return s)

 (eval_operand o s, return s)
*)

let update_operand_preserve_flags (dst:dst_op) (v:nat64) :st unit =
  valid_operand dst;;
  update_operand_preserve_flags' dst v

(* Default version havocs flags *)
let update_operand (dst:dst_op) (ins:ins) (v:nat64) :st unit =
  valid_operand dst;;
  update_operand' dst ins v

let update_flags (new_flags:nat64) :st unit =
  s <-- get();
  set ( { s with flags = new_flags } )

let example (dst:dst_op) (src:operand) :st unit =
  valid_operand dst;;
  valid_operand src;;
  update_operand_preserve_flags dst 2

let test (dst:dst_op) (src:operand) (s:state) :state =
   snd ((example dst src) s)

open FStar.Mul

#reset-options "--z3rlimit 200"
let eval_ins (ins:ins) (s:state) :state =
  if not s.ok then s
  else
  snd ((match ins with 
  | Mov64 dst src ->
    valid_operand src;;
    x <-- lift (eval.eval_operand src);
    update_operand_preserve_flags dst x

  | Add64 dst src -> 
    valid_operand src;;
    x <-- lift (eval.eval_operand dst);
    y <-- lift (eval.eval_operand src);
    update_operand dst ins ((x + y) % nat64_max)
  
  | AddLea64 dst src1 src2 ->
    valid_operand src1;;
    valid_operand src2;;
    x <-- lift (eval.eval_operand src1);
    y <-- lift (eval.eval_operand src2);
    update_operand_preserve_flags dst ((x + y) % nat64_max)

  | AddCarry64 dst src ->
    flags <-- lift (eval.get_flags ());
    x <-- lift (eval.eval_operand dst);
    y <-- lift (eval.eval_operand src);
    
    let old_carry = if cf flags then 1 else 0 in
    let sum = x + y + old_carry in
    let new_carry = sum >= nat64_max in
    
    valid_operand src;;
    update_operand dst ins (sum % nat64_max);;
    update_flags (update_cf flags new_carry)
    
  | Sub64 dst src ->
    valid_operand src;;
    x <-- lift (eval.eval_operand dst);
    y <-- lift (eval.eval_operand src);
    update_operand dst ins ((x - y) % nat64_max)

  | Mul64 src ->
    s <-- get ();
    x <-- lift (eval.eval_reg Rax);
    y <-- lift (eval.eval_operand src);
    
    let product = x * y in
    let hi = product / nat64_max in
    let lo = product % nat64_max in
    
    valid_operand src;;
    update_reg Rax lo;;
    update_reg Rdx hi;;
    update_flags (havoc s ins)

  | IMul64 dst src ->
    valid_operand src;;
    x <-- lift (eval.eval_operand dst);
    y <-- lift (eval.eval_operand src);
    update_operand dst ins ((x * y) % nat64_max)

  | Xor64 dst src ->
    valid_operand src;;
    x <-- lift (eval.eval_operand dst);
    y <-- lift (eval.eval_operand src);
    update_operand dst ins (FStar.UInt.logxor #64 x y)
	 
  | Shr64 dst amt ->
    valid_shift_operand amt;;
    x <-- lift (eval.eval_operand dst);
    y <-- lift (eval.eval_operand amt);
    update_operand dst ins (FStar.UInt.shift_right #64 x y)

  | Shl64 dst amt ->
    valid_shift_operand amt;;
    x <-- lift (eval.eval_operand dst);
    y <-- lift (eval.eval_operand amt);
    update_operand dst ins (FStar.UInt.shift_left #64 x y)) s)

(*
    match ins with 
    | Mov64 dst src -> if valid_operand dst s && valid_operand src s then      
			 update_operand dst s (eval_operand src s)
		      else
			 { s with ok = false }
    | Add64 dst src -> update_operand_and_flags dst s ins ((eval_operand dst s + eval_operand src s) % nat64_max)
    | AddLea64 dst src1 src2 -> update_operand_and_flags dst s ins ((eval_operand src1 s + eval_operand src2 s) % nat64_max)
    | AddCarry64 dst src -> let old_carry = if cf(s.flags) then 1 else 0 in
			   let sum = eval_operand dst s + eval_operand src s + old_carry in			  
			   let new_carry = sum > nat64_max in
			   { update_operand dst s (sum % nat64_max) with flags = update_cf s.flags new_carry }
    | Sub64 dst src -> update_operand_and_flags dst s ins ((eval_operand dst s - eval_operand src s) % nat64_max)
    | Mul64 src -> let product = eval_reg Rax s * eval_operand src s in
		  let hi = product / nat64_max in
		  let lo = product % nat64_max in
		  { update_reg Rax (update_reg Rdx s hi) lo with flags = havoc s ins }
    | IMul64 dst src -> update_operand_and_flags dst s ins ((eval_operand dst s * eval_operand src s) % nat64_max)	  
    | Xor64 dst src -> update_operand_and_flags dst s ins (FStar.UInt.logxor #64 (eval_operand dst s) (eval_operand src s))	  
    | Shr64 dst amt -> if valid_shift_operand amt s then			
		        update_operand_and_flags dst s ins (FStar.UInt.shift_right #64 (eval_operand dst s) (eval_operand amt s))
		      else
			{ s with ok = false }
    | Shl64 dst amt -> if valid_shift_operand amt s then			
		        update_operand_and_flags dst s ins (FStar.UInt.shift_left #64 (eval_operand dst s) (eval_operand amt s))
		      else
			{ s with ok = false }
*)

(*
 * the decreases clause
 *)
let decr (c:code) (s:state) :nat =
  match c with
  | While _ _ inv ->
    let n = eval.eval_operand inv s in
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
  | IfElse ifCond ifTrue ifFalse  ->
    let b = eval.eval_ocmp ifCond s in
    if b then eval_code ifTrue s else eval_code ifFalse s
  | While _ _ _                   -> eval_while c s
    
and eval_codes l s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c s in
    if None? s_opt then None else eval_codes tl (Some?.v s_opt)
    
and eval_while c s_0 = (* trying to mimic the eval_while predicate using a function *)
  let While cond body inv = c in
  let n_0 = eval.eval_operand inv s_0 in
  let b = eval.eval_ocmp cond s_0 in

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
	  let n_1 = eval.eval_operand inv s_1 in
	  if n_1 >= n_0 then None  //loop invariant must decrease
	  else eval_while c s_1

  (* let While cond body inv = c in *)
  (* let n_0 = eval.eval_operand inv s_0 in *)
  (* let (b_opt, s_0) = eval_ocmp cond s_0 in *)
  (* match b_opt with *)
  (* | None   -> Some ({ s_0 with ok = false }) *)
  (* | Some b -> *)
  (*   if n_0 <= 0 then *)
  (*     if b then None else Some s_0  //if loop invariant is <= 0, the guard must be false *)
  (*   else  //loop invariant > 0 *)
  (*     if not b then None  //guard must evaluate to true *)
  (*     else *)
  (*       let s_opt = eval_code body s_0 in *)
  (*       if None? s_opt then None *)
  (*       else *)
  (*         let s_1 = Some?.v s_opt in *)
  (* 	  if not s_1.ok then Some s_1  //this is from the reference semantics, if ok flag is unset, return *)
  (* 	  else *)
  (* 	    let n_1 = eval_operand inv s_1 in *)
  (* 	    if n_1 >= n_0 then None  //loop invariant must decrease *)
  (* 	    else eval_while c s_1 *)
