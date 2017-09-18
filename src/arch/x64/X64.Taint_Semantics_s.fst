module X64.Taint_Semantics_s

open FStar.BaseTypes
open FStar.List.Tot.Base

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
  memTaint: map int taint;
}

type ins_tag =
  | Mov
  | Add
  | AddLea
  | AddCarry
  | Sub
  | Mul
  | IMul
  | Xor
  | And
  | Shr
  | Shl

let ndsts (i : ins_tag) : nat = match i with
  | Mul -> 2
  | _ -> 1

let nsrcs (i:ins_tag) : nat = match i with
  | Mov | Mul -> 1
  | AddLea -> 3
  | _ -> 2

let create_ins (ids:(ins_tag * list dst_op * list operand){let i, d, s = ids in length d = ndsts i && length s = nsrcs i}) : ins = let i, dsts, srcs = ids in
  match i with
  | Mov -> Mov64 (hd dsts) (hd srcs)
  | Add -> Add64 (hd dsts) (hd (tl srcs))
  | AddLea -> AddLea64 (hd dsts) (hd (tl srcs)) (hd (tl (tl srcs)))
  | AddCarry -> AddCarry64 (hd dsts) (hd (tl srcs))
  | Sub -> Sub64 (hd dsts) (hd (tl srcs))
  | Mul -> Mul64 (hd srcs)
  | IMul -> IMul64 (hd dsts) (hd (tl srcs))
  | Xor -> Xor64 (hd dsts) (hd (tl srcs))
  | And -> And64 (hd dsts) (hd (tl srcs))
  | Shr -> Shr64 (hd dsts) (hd (tl srcs))
  | Shl -> Shl64 (hd dsts) (hd (tl srcs))

type tainted_ins = |TaintedIns: ids:(ins_tag * list dst_op * list operand){let i, d, s = ids in length d = ndsts i && length s = nsrcs i} -> ins: ins{ins = create_ins ids} -> t:taint -> tainted_ins

let operand_obs (s:traceState) (o:operand) : list observation =
  match o with
    | OConst _ | OReg _ -> []
    | OMem m -> match m with
      | MConst _ -> []
      | MReg reg _ -> [MemAccess (eval_reg reg s.state)]
      | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s.state) (eval_reg index s.state)]

let rec operand_obs_list (s:traceState) (o:list operand) : list observation =
  match o with
  | [] -> []
  | hd :: tl -> operand_obs s hd @ (operand_obs_list s tl)

let dst_to_op (x:dst_op) : operand = x

let ins_obs (ins:tainted_ins) (s:traceState) : (list observation) =
  let (i, dsts, srcs) = ins.ids in
  (operand_obs_list s (List.Tot.Base.map dst_to_op dsts)) @ (operand_obs_list s srcs)

(* Checks if the taint of an operand matches the ins annotation *)
let taint_match (o:operand) (t:taint) (memTaint:map int taint) (s:state) : bool =
  match o with
    | OConst _ | OReg _ -> true
    | OMem m -> 
        let ptr = eval_maddr m s in
	memTaint.[ptr] = t

let rec taint_match_list o t memTaint s : bool = match o with
  | [] -> true
  | hd::tl -> (taint_match hd t memTaint s) && taint_match_list tl t memTaint s

let update_taint (memTaint:map int taint) (dst:dst_op) (t:taint) (s:state) =
  match dst with
    | OReg _ -> memTaint
    | OMem m -> let ptr = eval_maddr m s in
        memTaint.[ptr] <- t

val update_taint_list: (memTaint:map int taint) -> (dst:list dst_op) -> (t:taint) -> (s:state) -> Tot (map int taint) (decreases %[dst])
let rec update_taint_list memTaint (dst:list dst_op) t s = match dst with
  | [] -> memTaint
  | hd :: tl -> update_taint_list (update_taint memTaint hd t s) tl t s

let taint_eval_ins (ins:tainted_ins) (ts: traceState) : traceState =
  let t = ins.t in
  let i, dsts, srcs = ins.ids in
  let s = run (check (taint_match_list srcs t ts.memTaint)) ts.state in
  let memTaint = update_taint_list ts.memTaint dsts t s in
  (* Execute the instruction *)
  let s = run (eval_ins ins.ins) s in
  {state = s; trace = ts.trace; memTaint = memTaint}

type tainted_ocmp = |TaintedOCmp: o:ocmp -> ot:taint -> tainted_ocmp

let get_fst_ocmp (o:ocmp) = match o with
  | OEq o1 _ | ONe o1 _ | OLe o1 _ | OGe o1 _ | OLt o1 _ | OGt o1 _ -> o1

let get_snd_ocmp (o:ocmp) = match o with
  | OEq _ o2 | ONe _ o2 | OLe _ o2 | OGe _ o2 | OLt _ o2 | OGt _ o2 -> o2

let taint_eval_ocmp (ts:traceState) (c:tainted_ocmp) : traceState * bool =
  let t = c.ot in
  let s = run (check (taint_match (get_fst_ocmp c.o) t ts.memTaint);; check (taint_match (get_snd_ocmp c.o) t ts.memTaint)) ts.state in
    {ts with state = s}, eval_ocmp s c.o

type tainted_code = precode tainted_ins tainted_ocmp
type tainted_codes = list tainted_code

let tainted_decr (c:tainted_code) (s:state) : nat =
  match c with
  | While _ _ inv ->
    let n = eval_operand inv s in
    if UInt64.v n >= 0 then UInt64.v n else 0
    | _ -> 0

val taint_eval_code: c:tainted_code -> s:traceState -> Tot (option traceState)
(decreases %[c; tainted_decr c s.state; 1])
val taint_eval_codes: l:tainted_codes -> s:traceState -> Tot (option traceState)
(decreases %[l])
val taint_eval_while: c:tainted_code{While? c} -> s:traceState -> Tot (option traceState)
(decreases %[c; tainted_decr c s.state; 0])

(* Adds the observations to the eval_code.
   Returns None if eval_code returns None *)
let rec taint_eval_code c s =
  match c with
    | Ins ins -> let obs = ins_obs ins s in
      Some ({taint_eval_ins ins s with trace = obs})
    
    | Block l -> taint_eval_codes l s
    
    | IfElse ifCond ifTrue ifFalse ->
      let st, b = taint_eval_ocmp s ifCond in
      (* We add the BranchPredicate to the trace *)
      let s' = {st with trace=BranchPredicate(b)::s.trace} in
      (* We evaluate the branch with the new trace *)
      if b then taint_eval_code ifTrue s' else taint_eval_code ifFalse s'
    
    | While _ _ _ -> taint_eval_while c s

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
	  ({(Some?.v s_opt) with
	    trace = (Some?.v s_opt).trace @ s.trace})

and taint_eval_while c s0 =
  let While cond body inv = c in
  let n0 = eval_operand inv s0.state in
  let (s0, b) = taint_eval_ocmp s0 cond in

  if UInt64.v n0 <= 0 then
    (* if loop invariant <= 0, the guard must be false, and we add the corresponding BranchPredicate *)
    if b then None else Some ({s0 with trace = BranchPredicate(false)::s0.trace})
  else // loop invariant > 0
    if not b then None // guard must evaluate to true
    else
      // We add the branchpredicate to the trace
      let s0 = {s0 with trace = BranchPredicate(true)::s0.trace} in
      let s_opt = taint_eval_code body s0 in
      if None? s_opt then None
      else
        let s1 = Some?.v s_opt in
	if not s1.state.ok then Some s1 // from the reference semantics
	else
	  let n1 = eval_operand inv s1.state in
	  if UInt64.v n1 >= UInt64.v n0 then None // loop invariant must decrease
	  else taint_eval_while c s1
    
