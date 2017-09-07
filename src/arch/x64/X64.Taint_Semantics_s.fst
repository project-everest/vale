module X64.Taint_Semantics_s

open FStar.BaseTypes
open X64.Machine_s
open X64.Semantics_s

type taint =
  | Public
  | Secret

type observation =
  | BranchPredicate: pred:bool -> observation
  | MemAccess: addr:uint64 -> observation
  | MemAccessOffset: base:uint64 -> index:uint64 -> observation

noeq type traceState = {
  state: state;
  trace: list observation;
}

let operand_obs (s:traceState) (o:operand) : list observation =
  match o with
    | OConst _ | OReg _ -> []
    | OMem m -> match m with
      | MConst _ -> []
      | MReg reg _ -> [MemAccess (eval_reg reg s.state)]
      | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s.state) (eval_reg index s.state)]
  
let ins_obs (ins:ins) (s:traceState) : (list observation) =
  match ins with
  | Mov64 dst src ->
      (operand_obs s dst) @ (operand_obs s src)
  | Add64 dst src ->
      (operand_obs s dst) @ (operand_obs s src)
  | AddLea64 dst src1 src2 ->
      (operand_obs s dst) @ (operand_obs s src1) @ (operand_obs s src2)
  | AddCarry64 dst src -> (operand_obs s dst) @ (operand_obs s src)
  | Sub64 dst src -> (operand_obs s dst) @ (operand_obs s src)
  | Mul64 src -> operand_obs s src
  | IMul64 dst src -> (operand_obs s dst) @ (operand_obs s src)
  | Xor64 dst src -> (operand_obs s dst) @ (operand_obs s src)
  | And64 dst src -> (operand_obs s dst) @ (operand_obs s src)
  | Shr64 dst amt -> (operand_obs s dst) @ (operand_obs s amt)
  | Shl64 dst amt -> (operand_obs s dst) @ (operand_obs s amt)

val taint_eval_code: c:code -> s:traceState -> Tot (option traceState)
(decreases %[c; decr c s.state; 1])
val taint_eval_codes: l:codes -> s:traceState -> Tot (option traceState)
(decreases %[l])
val taint_eval_while: c:code{While? c} -> s:traceState -> Tot (option traceState)
(decreases %[c; decr c s.state; 0])


(* Adds the observations to the eval_code.
   Returns None if eval_code returns None *)
let rec taint_eval_code c s =
  match c with
    | Ins ins -> begin match eval_code c s.state with
      | None -> None
      | Some s2 -> Some ({state = s2; trace = ins_obs ins s})
    end
    | Block l -> taint_eval_codes l s
    | IfElse ifCond ifTrue ifFalse ->
      let b = eval_ocmp s.state ifCond in
      (* We add the BranchPredicate to the trace *)
      let s' = {state=s.state; trace=BranchPredicate(b)::s.trace} in
      (* We evaluate the branch with the new trace *)
      if b then taint_eval_code ifTrue s' else taint_eval_code ifFalse s'
    | While _ _ _ -> None

and taint_eval_codes l s =
match l with
      | [] -> Some s
      | c::tl -> 
	let s_opt = taint_eval_code c s in
	if None? s_opt then None
	(* Recursively evaluate on the tail,
	 and append the trace of this instruction *)
	else taint_eval_codes
	  tl
	  ({state = (Some?.v s_opt).state;
	    trace = (Some?.v s_opt).trace @ s.trace})

and taint_eval_while c s0 =
  let While cond body inv = c in
  let n0 = eval_operand inv s0.state in
  let b = eval_ocmp s0.state cond in

  if UInt64.v n0 <= 0 then
    (* if loop invariant <= 0, the guard must be false, and we add the corresponding BranchPredicate *)
    if b then None else Some ({state = s0.state; trace = BranchPredicate(false)::s0.trace})
  else // loop invariant > 0
    if not b then None // guard must evaluate to true
    else
      // We add the branchpredicate to the trace
      let s0 = {state = s0.state; trace = BranchPredicate(true)::s0.trace} in
      let s_opt = taint_eval_code body s0 in
      if None? s_opt then None
      else
        let s1 = Some?.v s_opt in
	if not s1.state.ok then Some s1 // from the reference semantics
	else
	  let n1 = eval_operand inv s1.state in
	  if UInt64.v n1 >= UInt64.v n0 then None // loop invariant must decrease
	  else taint_eval_while c s1
    
