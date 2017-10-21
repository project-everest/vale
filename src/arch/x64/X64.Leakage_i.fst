module X64.Leakage_i
open X64.Machine_s
open X64.Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers_i
open X64.Leakage_Ins_i

open FStar.Tactics

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics'"
let combine_reg_taints regs1 regs2 =
    fun x -> merge_taint (regs1 x) (regs2 x)

let combine_reg_taints_monotone regs1 regs2: Lemma
(forall r. Public? ((combine_reg_taints regs1 regs2) r) ==> Public? (regs1 r) /\ Public? (regs2 r))
= ()

let taintstate_monotone ts ts' = ( forall r. Public? (ts'.regTaint r) ==> Public? (ts.regTaint r)) /\ (Public? (ts'.flagsTaint) ==> Public? (ts.flagsTaint))

val taintstate_monotone_trans: (ts1:taintState) -> (ts2:taintState) -> (ts3:taintState) ->
Lemma (taintstate_monotone ts1 ts2 /\ taintstate_monotone ts2 ts3 ==> taintstate_monotone ts1 ts3)
let taintstate_monotone_trans ts1 ts2 ts3 = ()

val isConstant_monotone: (ts1:taintState) -> (ts2:taintState) -> (code:tainted_code) -> (fuel:nat) -> (s1:traceState) -> (s2:traceState) -> Lemma
(isConstantTimeGivenStates code fuel ts2 s1 s2 /\ taintstate_monotone ts1 ts2 ==> isConstantTimeGivenStates code fuel ts1 s1 s2)

let isConstant_monotone ts1 ts2 code fuel s1 s2 = ()

val isExplicit_monotone: (ts:taintState) -> (ts1:taintState) -> (ts2:taintState) -> (code:tainted_code) -> (fuel:nat) -> (s1:traceState) -> (s2:traceState) -> Lemma
(isExplicitLeakageFreeGivenStates code fuel ts ts1 s1 s2 /\ taintstate_monotone ts1 ts2 ==> isExplicitLeakageFreeGivenStates code fuel ts ts2 s1 s2)

let isExplicit_monotone ts ts1 ts2 code fuel s1 s2 = ()

val isExplicit_monotone2: (ts:taintState) -> (ts1:taintState) -> (ts2:taintState) -> (code:tainted_code) -> (fuel:nat) -> (s1:traceState) -> (s2:traceState) -> Lemma
(isExplicitLeakageFreeGivenStates code fuel ts2 ts s1 s2 /\ taintstate_monotone ts1 ts2 ==> isExplicitLeakageFreeGivenStates code fuel ts1 ts s1 s2)

let isExplicit_monotone2 ts ts1 ts2 code fuel s1 s2 = ()


val combine_taint_states: (ts1:taintState) -> (ts2:taintState) -> (ts:taintState{taintstate_monotone ts1 ts /\ taintstate_monotone ts2 ts})
let combine_taint_states (ts1:taintState) (ts2:taintState) =
  TaintState (combine_reg_taints ts1.regTaint ts2.regTaint) (merge_taint ts1.flagsTaint ts2.flagsTaint)

val check_if_block_consumes_fixed_time: (block:tainted_codes) -> (fuel:nat) -> (ts:taintState) -> Tot (bool * taintState)
(decreases %[fuel; block])
val check_if_code_consumes_fixed_time: (code:tainted_code) -> (fuel:nat) -> (ts:taintState) -> Tot (bool * taintState) (decreases %[fuel; code; 1])
val check_if_loop_consumes_fixed_time: (code:tainted_code{While? code}) -> (fuel:nat) -> (ts:taintState) -> Tot (bool * taintState) (decreases %[fuel; code; 0])


let rec check_if_block_consumes_fixed_time (block:tainted_codes) (fuel:nat) (ts:taintState) : bool * taintState =
  match block with
  | [] -> true, ts
  | hd::tl -> let fixedTime, ts_int = check_if_code_consumes_fixed_time hd fuel ts in
    if (not fixedTime) then fixedTime, ts_int
    else check_if_block_consumes_fixed_time tl fuel ts_int
    

and check_if_code_consumes_fixed_time (code:tainted_code) (fuel:nat) (ts:taintState) : bool * taintState =
  match code with
  | Ins ins -> check_if_ins_consumes_fixed_time ins fuel ts
  
  | Block block -> check_if_block_consumes_fixed_time block fuel ts

  | IfElse ifCond ifTrue ifFalse ->
    let cond_taint = ifCond.ot in
    let o1 = operand_taint (get_fst_ocmp ifCond.o) ts in
    let o2 = operand_taint (get_snd_ocmp ifCond.o) ts in
    let predTaint = merge_taint (merge_taint o1 o2) cond_taint in
    if (Secret? predTaint) then (false, ts)
    else
      let o1Public = operand_does_not_use_secrets (get_fst_ocmp ifCond.o) ts in
      if (not o1Public) then (false, ts)
      else
      let o2Public = operand_does_not_use_secrets (get_snd_ocmp ifCond.o) ts in
      if (not o2Public) then (false, ts)
      else
      let validIfTrue, tsIfTrue = check_if_code_consumes_fixed_time ifTrue fuel ts in
      if (not validIfTrue) then (false, ts)
      else
      let validIfFalse, tsIfFalse = check_if_code_consumes_fixed_time ifFalse fuel ts in
      if (not validIfFalse) then (false, ts)
      else
      (true, combine_taint_states tsIfTrue tsIfFalse)   

  | While cond body -> check_if_loop_consumes_fixed_time code fuel ts 
  
and check_if_loop_consumes_fixed_time c (fuel:nat) (ts:taintState) : bool * taintState =
  if fuel = 0 then true, ts else
  let While pred body = c in
  let cond_taint = pred.ot in
  let o1 = operand_taint (get_fst_ocmp pred.o) ts in
  let o2 = operand_taint (get_snd_ocmp pred.o) ts in
  let predTaint = merge_taint (merge_taint o1 o2) cond_taint in

  if (Secret? predTaint) then false, ts
  else
    let o1Public = operand_does_not_use_secrets (get_fst_ocmp pred.o) ts in
    if (not o1Public) then (false, ts)
    else
    let o2Public = operand_does_not_use_secrets (get_snd_ocmp pred.o) ts in
    if (not o2Public) then (false, ts)
    else
    let fixedTime, next_ts = check_if_code_consumes_fixed_time body (fuel - 1) ts in
    if (not fixedTime) then (false, ts)
    else
    let combined_ts = combine_taint_states ts next_ts in
    check_if_loop_consumes_fixed_time c (fuel - 1) combined_ts

val lemma_equal_eval_isConstant_aux: (code1: tainted_code) -> (code2:tainted_code) -> (fuel:nat) -> (ts:taintState) -> (ts':taintState) -> (s1 : traceState) -> (s2:traceState) -> Lemma ((forall s. taint_eval_code code1 fuel s == taint_eval_code code2 fuel s) ==> 
  isConstantTimeGivenStates code1 fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates code1 fuel ts ts' s1 s2 ==> isConstantTimeGivenStates code2 fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates code2 fuel ts ts' s1 s2)
  
let lemma_equal_eval_isConstant_aux code1 code2 fuel ts ts' s1 s2 = ()

val lemma_equal_eval_isConstant: (code1: tainted_code) -> (code2:tainted_code) -> (fuel:nat) -> (ts:taintState) -> (ts':taintState) -> Lemma ((forall s. taint_eval_code code1 s == taint_eval_code code2 s) ==> 
  isConstantTime code1 fuel ts /\ isLeakageFree code1 fuel ts ts' ==> isConstantTime code2 fuel ts /\ isLeakageFree code2 fuel ts ts')

#set-options "--z3rlimit 20"
let lemma_equal_eval_isConstant code1 code2 fuel ts ts' = FStar.Classical.forall_intro_2 (lemma_equal_eval_isConstant_aux code1 code2 fuel ts ts')

val monotone_ok_eval: (code:tainted_code) -> (fuel:nat) -> (s:traceState) -> Lemma
 (requires True)
 (ensures (let s' = taint_eval_code code fuel s in
    Some? s' /\ (Some?.v s').state.ok ==> s.state.ok))
 (decreases %[code; 0])

val monotone_ok_eval_block: (codes:tainted_codes) -> (fuel:nat) -> (s:traceState) -> Lemma
 (requires True)
 (ensures (let s' = taint_eval_codes codes fuel s in
    Some? s' /\ (Some?.v s').state.ok ==> s.state.ok))
 (decreases %[codes;1])

#set-options "--z3rlimit 20"
let rec monotone_ok_eval code fuel s = match code with
  | Ins ins -> ()
  | Block block -> monotone_ok_eval_block block fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let st, b = taint_eval_ocmp s ifCond in
    let st = {st with trace=BranchPredicate(b)::s.trace} in
    if b then monotone_ok_eval ifTrue fuel st else monotone_ok_eval ifFalse fuel st
  | While cond body -> 
    if fuel = 0 then ()
    else
    let st, b = taint_eval_ocmp s cond in
    if not b then ()
    else 
    let st = {st with trace=BranchPredicate(b)::s.trace} in
    monotone_ok_eval body (fuel-1) st;
    ()

and monotone_ok_eval_block block fuel s =
  match block with
  | [] -> ()
  | hd :: tl -> 
    let s' = taint_eval_code hd fuel s in
    if None? s' then () else
    monotone_ok_eval_block tl fuel (Some?.v s');
    monotone_ok_eval hd fuel s

val lemma_loop_taintstate_monotone: (ts:taintState) -> (code:tainted_code{While? code}) -> (fuel:nat) -> Lemma 
(requires True)
(ensures (let _, ts' = check_if_loop_consumes_fixed_time code fuel ts in
  taintstate_monotone ts ts'))
(decreases %[fuel; code])

#set-options "--z3rlimit 40"
let rec lemma_loop_taintstate_monotone ts code fuel =
  if fuel = 0 then ()
  else
  let While pred body = code in
  let b, ts' = check_if_code_consumes_fixed_time body (fuel-1) ts in
  let combined_ts = combine_taint_states ts ts' in
  lemma_loop_taintstate_monotone combined_ts code (fuel-1)

val lemma_code_explicit_leakage_free: (ts:taintState) -> (code:tainted_code) -> (fuel:nat) -> (s1:traceState) -> (s2:traceState) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_code_consumes_fixed_time code fuel ts in
  (b2t b ==> isConstantTimeGivenStates code fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2)))
 (decreases %[fuel; code; 1])

val lemma_block_explicit_leakage_free: (ts:taintState) -> (codes:tainted_codes) -> (fuel:nat) -> (s1:traceState) -> (s2:traceState) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_block_consumes_fixed_time codes fuel ts in
  (b2t b ==> isConstantTimeGivenStates (Block codes) fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates (Block codes) fuel ts ts' s1 s2)))
 (decreases %[fuel; codes; 2])

val lemma_loop_explicit_leakage_free: (ts:taintState) -> (code:tainted_code{While? code}) -> (fuel:nat) -> (s1:traceState) -> (s2:traceState) -> Lemma  
 (requires True)
 (ensures (let b, ts' = check_if_loop_consumes_fixed_time code fuel ts in
  (b2t b ==> isConstantTimeGivenStates code fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2)))
 (decreases %[fuel; code; 0])

#set-options "--z3rlimit 100"
 let rec lemma_code_explicit_leakage_free ts code fuel s1 s2 = match code with
  | Ins ins -> lemma_ins_leakage_free ts fuel ins
  | Block block -> lemma_block_explicit_leakage_free ts block fuel s1 s2
  | IfElse ifCond ifTrue ifFalse ->     
    let b_fin, ts_fin = check_if_code_consumes_fixed_time code fuel ts in
    let st1, b1 = taint_eval_ocmp s1 ifCond in
    let st1 = {st1 with trace=BranchPredicate(b1)::s1.trace} in
    let st2, b2 = taint_eval_ocmp s2 ifCond in
    let st2 = {st2 with trace=BranchPredicate(b2)::s2.trace} in
    assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.ok /\ st2.state.ok ==> constTimeInvariant ts st1 st2);
    monotone_ok_eval ifTrue fuel st1;
    monotone_ok_eval ifTrue fuel st2;
    lemma_code_explicit_leakage_free ts ifTrue fuel st1 st2;
    monotone_ok_eval ifFalse fuel st1;
    monotone_ok_eval ifFalse fuel st2;
    lemma_code_explicit_leakage_free ts ifFalse fuel st1 st2;
    ()
  | While _ _ -> lemma_loop_explicit_leakage_free ts code fuel s1 s2

and lemma_block_explicit_leakage_free ts block fuel s1 s2 = match block with
  | [] -> ()
  | hd :: tl ->
    let b, ts' = check_if_code_consumes_fixed_time hd fuel ts in
    lemma_code_explicit_leakage_free ts hd fuel s1 s2;
    let s'1 = taint_eval_code hd fuel s1 in
    let s'2 = taint_eval_code hd fuel s2 in
    if None? s'1 || None? s'2 then ()
    else
    let s'1 = Some?.v s'1 in
    let s'2 = Some?.v s'2 in
    lemma_block_explicit_leakage_free ts' tl fuel s'1 s'2;
    monotone_ok_eval (Block tl) fuel s'1;
    monotone_ok_eval (Block tl) fuel s'2

and lemma_loop_explicit_leakage_free ts code fuel s1 s2 =
  if fuel = 0 then ()
  else
  let b_fin, ts_fin = check_if_code_consumes_fixed_time code fuel ts in
  let r1 = taint_eval_code code fuel s1 in
  let r2 = taint_eval_code code fuel s2 in
  let While cond body = code in
  let (st1, b1) = taint_eval_ocmp s1 cond in
  let (st2, b2) = taint_eval_ocmp s2 cond in
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.ok /\ st2.state.ok ==> b1 = b2);
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.ok /\ st2.state.ok ==> constTimeInvariant ts st1 st2);
  if not b1 || not b2 then
  (
  lemma_loop_taintstate_monotone ts code fuel;
  ()
  )
  else
  let st'1 = ({st1 with trace = BranchPredicate(true)::st1.trace}) in
  let st'2 = ({st2 with trace = BranchPredicate(true)::st2.trace}) in
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st'1.state.ok /\ st'2.state.ok ==> constTimeInvariant ts st'1 st'2);
  let b', ts' = check_if_code_consumes_fixed_time body (fuel-1) ts in
  lemma_code_explicit_leakage_free ts body (fuel-1) st'1 st'2;
  monotone_ok_eval body (fuel-1) st'1;
  monotone_ok_eval body (fuel-1) st'2;
  let st1 = taint_eval_code body (fuel - 1) st'1 in
  let st2 = taint_eval_code body (fuel - 1) st'2 in
  assert (None? st1 ==> r1 == st1);
  assert (None? st2 ==> r2 == st2);
  if (None? st1 || None? st2) then ()
  else
  let st1 = Some?.v st1 in
  let st2 = Some?.v st2 in
  if not st1.state.ok || not st2.state.ok then ()
  else
  let combined_ts = combine_taint_states ts ts' in
  let b_aux, ts_aux = check_if_loop_consumes_fixed_time code (fuel-1) combined_ts in
  lemma_loop_explicit_leakage_free combined_ts code (fuel-1) st1 st2;
  isConstant_monotone ts combined_ts code (fuel-1) st1 st2;
  isExplicit_monotone2 ts_aux ts combined_ts code (fuel-1) st1 st2;
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.ok /\ st2.state.ok ==> constTimeInvariant ts' st1 st2);
  ()
  
val lemma_code_leakage_free: (ts:taintState) -> (code:tainted_code) -> (fuel:nat) -> Lemma
 (let b, ts' = check_if_code_consumes_fixed_time code fuel ts in
  (b2t b ==> isConstantTime code fuel ts /\ isLeakageFree code fuel ts ts'))

let lemma_code_leakage_free ts code fuel = FStar.Classical.forall_intro_2 (lemma_code_explicit_leakage_free ts code fuel)
  
(* val check_if_code_is_leakage_free: (code:tainted_code) -> (ts:taintState) -> (tsExpected:taintState) -> (b:bool{b ==> isLeakageFree code ts tsExpected
	 /\ b ==> isConstantTime code ts})


let check_if_code_is_leakage_free code ts tsExpected = 
  let b, ts' = check_if_code_consumes_fixed_time code ts in

  if b then
    publicTaintsAreAsExpected ts' tsExpected
  else
    b

*)
