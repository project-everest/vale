module X64.Taint_Semantics_s

open FStar.BaseTypes
open FStar.List.Tot.Base

open X64.Machine_s
open X64.Semantics_s

// syntax for map accesses, m.[key] and m.[key] <- value
let map (key:eqtype) (value:Type) = Map.t key value
unfold let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
unfold let op_String_Assignment = Map.upd

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

// Extract a list of destinations written to and a list of sources read from
let extract_operands (i:ins) : (list operand * list operand) =
  match i with
  | Mov64 dst src -> [dst], [src]
  | Add64 dst src -> [dst], [dst; src]
  | AddLea64 dst src1 src2 -> [dst], [dst; src1; src2]
  | AddCarry64 dst src -> [dst], [dst; src]
  | Sub64 dst src -> [dst], [dst; src]
  | Mul64 src -> [OReg Rax; OReg Rdx], [OReg Rax; src]
  | IMul64 dst src -> [dst], [dst; src]
  | Xor64 dst src -> [dst], [dst; src]
  | And64 dst src -> [dst], [dst; src]
  | Shr64 dst amt -> [dst], [dst; amt]
  | Shl64 dst amt -> [dst], [dst; amt]
  
type tainted_ins = |TaintedIns: ops:(ins * list operand * list operand){let i, d, s = ops in (d,s) = extract_operands i} 
                                -> t:taint -> tainted_ins

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
  let (i, dsts, srcs) = ins.ops in
  (operand_obs_list s dsts @ operand_obs_list s srcs)

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

let update_taint (memTaint:map int taint) (dst:operand) (t:taint) (s:state) =
  match dst with
    | OConst _ -> memTaint
    | OReg _ -> memTaint
    | OMem m -> let ptr = eval_maddr m s in
        memTaint.[ptr] <- t

val update_taint_list: (memTaint:map int taint) -> (dst:list operand) -> (t:taint) -> (s:state) -> Tot (map int taint) (decreases %[dst])
let rec update_taint_list memTaint (dst:list operand) t s = match dst with
  | [] -> memTaint
  | hd :: tl -> update_taint_list (update_taint memTaint hd t s) tl t s

let taint_eval_ins (ins:tainted_ins) (ts: traceState) : traceState =
  let t = ins.t in
  let i, dsts, srcs = ins.ops in
  let s = run (check (taint_match_list srcs t ts.memTaint)) ts.state in
  let memTaint = update_taint_list ts.memTaint dsts t s in
  (* Execute the instruction *)
  let s = run (eval_ins i) s in
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

val taint_eval_code: c:tainted_code -> fuel:nat -> s:traceState -> Tot (option traceState)
(decreases %[fuel; c; 1])
val taint_eval_codes: l:tainted_codes -> fuel:nat -> s:traceState -> Tot (option traceState)
(decreases %[fuel; l])
val taint_eval_while: c:tainted_code{While? c} -> fuel:nat -> s:traceState -> Tot (option traceState)
(decreases %[fuel; c; 0])

(* Adds the observations to the eval_code.
   Returns None if eval_code returns None *)
let rec taint_eval_code c fuel s =
  match c with
    | Ins ins -> let obs = ins_obs ins s in
      Some ({taint_eval_ins ins s with trace = obs @ s.trace})
    
    | Block l -> taint_eval_codes l fuel s
    
    | IfElse ifCond ifTrue ifFalse ->
      let st, b = taint_eval_ocmp s ifCond in
      (* We add the BranchPredicate to the trace *)
      let s' = {st with trace=BranchPredicate(b)::s.trace} in
      (* We evaluate the branch with the new trace *)
      if b then taint_eval_code ifTrue fuel s' else taint_eval_code ifFalse fuel s'
    
    | While _ _ -> taint_eval_while c fuel s

and taint_eval_codes l fuel s =
match l with
      | [] -> Some s
      | c::tl -> 
	let s_opt = taint_eval_code c fuel s in
	if None? s_opt then None
	(* Recursively evaluate on the tail *)
	else taint_eval_codes
	  tl
	  fuel
	  (Some?.v s_opt)

and taint_eval_while c fuel s0 =
  if fuel = 0 then None else
  let While cond body = c in
  let (s0, b) = taint_eval_ocmp s0 cond in
  if not b then Some ({s0 with trace = BranchPredicate(false)::s0.trace})
  else
    let s0 = {s0 with trace = BranchPredicate(true)::s0.trace} in
    let s_opt = taint_eval_code body (fuel - 1) s0 in
    match s_opt with
    | None -> None
    | Some s1 -> if not s1.state.ok then Some s1
      else taint_eval_while c (fuel - 1) s1
