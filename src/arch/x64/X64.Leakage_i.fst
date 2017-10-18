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

let combine_taint_states (ts:taintState) (ts1:taintState) (ts2:taintState) =
  TaintState (combine_reg_taints ts1.regTaint ts2.regTaint) (merge_taint ts1.flagsTaint ts2.flagsTaint)
  
let rec check_if_block_consumes_fixed_time (block:tainted_codes) (ts:taintState) : bool * taintState =
  match block with
  | [] -> true, ts
  | hd::tl -> let fixedTime, ts_int = check_if_code_consumes_fixed_time hd ts in
    if (not fixedTime) then fixedTime, ts_int
    else check_if_block_consumes_fixed_time tl ts_int
    

and check_if_code_consumes_fixed_time (code:tainted_code) (ts:taintState) : bool * taintState =
  match code with
  | Ins ins -> check_if_ins_consumes_fixed_time ins ts
  
  | Block block -> check_if_block_consumes_fixed_time block ts

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
      let validIfTrue, tsIfTrue = check_if_code_consumes_fixed_time ifTrue ts in
      if (not validIfTrue) then (false, ts)
      else
      let validIfFalse, tsIfFalse = check_if_code_consumes_fixed_time ifFalse ts in
      if (not validIfFalse) then (false, ts)
      else
      (true, combine_taint_states ts tsIfTrue tsIfFalse)
     
  | _ -> false, ts


(*
and check_if_loop_consumes_fixed_time (pred:tainted_ocmp) (body:tainted_code) (ts:taintState) : bool * taintState =
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
    let fixedTime, next_ts = check_if_code_consumes_fixed_time body ts in
    let combined_ts = combine_taint_states ts ts next_ts in
    if (combined_ts = ts) then true, combined_ts
    else check_if_loop_consumes_fixed_time pred body combined_ts
*)
  

val lemma_equal_eval_isConstant_aux: (code1: tainted_code) -> (code2:tainted_code) -> (ts:taintState) -> (ts':taintState) -> (s1 : traceState) -> (s2:traceState) -> Lemma ((forall s. taint_eval_code code1 s == taint_eval_code code2 s) ==> 
  isConstantTimeGivenStates code1 ts s1 s2 /\ isExplicitLeakageFreeGivenStates code1 ts ts' s1 s2 ==> isConstantTimeGivenStates code2 ts s1 s2 /\ isExplicitLeakageFreeGivenStates code2 ts ts' s1 s2)
  
let lemma_equal_eval_isConstant_aux code1 code2 ts ts' s1 s2 = ()

val lemma_equal_eval_isConstant: (code1: tainted_code) -> (code2:tainted_code) -> (ts:taintState) -> (ts':taintState) -> Lemma ((forall s. taint_eval_code code1 s == taint_eval_code code2 s) ==> 
  isConstantTime code1 ts /\ isLeakageFree code1 ts ts' ==> isConstantTime code2 ts /\ isLeakageFree code2 ts ts')
  
let lemma_equal_eval_isConstant code1 code2 ts ts' = FStar.Classical.forall_intro_2 (lemma_equal_eval_isConstant_aux code1 code2 ts ts')

val monotone_ok_eval: (code:tainted_code) -> (s:traceState) ->
  Lemma (let s' = taint_eval_code code s in
    Some? s' /\ (Some?.v s').state.ok ==> s.state.ok)

let rec monotone_ok_eval code s = match code with
  | Ins ins -> ()
  | Block block -> begin
    match block with
    | [] -> ()
    | hd :: tl -> 
      let s_fin = taint_eval_code (Block block) s in
      let s' = taint_eval_code hd s in
      assert (Some? s_fin ==> Some? s');
      if None? s' then ()
      else
      monotone_ok_eval (Block tl) (Some?.v s');
      assert (Some? s_fin /\ (Some?.v s_fin).state.ok ==> (Some?.v s').state.ok);
      admit()
  end
  | _ -> admit()
  

val lemma_code_explicit_leakage_free: (ts:taintState) -> (code:tainted_code) -> (s1:traceState) -> (s2:traceState) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_code_consumes_fixed_time code ts in
  (b2t b ==> isConstantTimeGivenStates code ts s1 s2 /\ isExplicitLeakageFreeGivenStates code ts ts' s1 s2)))
 (decreases %[code; 0])

val lemma_block_explicit_leakage_free: (ts:taintState) -> (codes:tainted_codes) -> (s1:traceState) -> (s2:traceState) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_block_consumes_fixed_time codes ts in
  (b2t b ==> isConstantTimeGivenStates (Block codes) ts s1 s2 /\ isExplicitLeakageFreeGivenStates (Block codes) ts ts' s1 s2)))
 (decreases %[codes;1])

let rec lemma_code_explicit_leakage_free ts code s1 s2 = match code with
  | Ins ins -> lemma_ins_leakage_free ts ins
  | Block block -> lemma_block_explicit_leakage_free ts block s1 s2
  | IfElse ifCond ifTrue ifFalse -> admit()
  | _ -> ()

and lemma_block_explicit_leakage_free ts block s1 s2 = match block with
  | [] -> ()
  | hd :: tl ->
    let b, ts' = check_if_code_consumes_fixed_time hd ts in
    lemma_code_explicit_leakage_free ts hd s1 s2;
    lemma_equal_eval_isConstant_aux hd (Block[hd]) ts ts' s1 s2;
    assert (b2t b ==> isConstantTimeGivenStates (Block [hd]) ts s1 s2  /\ isExplicitLeakageFreeGivenStates (Block [hd]) ts ts' s1 s2);
    let s'1 = taint_eval_code hd s1 in
    let s'2 = taint_eval_code hd s2 in
    if None? s'1 || None? s'2 then ()
    else
    let s'1 = Some?.v s'1 in
    let s'2 = Some?.v s'2 in
    lemma_block_explicit_leakage_free ts' tl s'1 s'2;
    let b_fin, ts_fin = check_if_block_consumes_fixed_time tl ts' in
    assert (b2t b_fin ==> isConstantTimeGivenStates (Block tl) ts' s'1 s'2 /\ isExplicitLeakageFreeGivenStates (Block tl) ts' ts_fin s'1 s'2);
    assert ((b2t b) ==> check_if_block_consumes_fixed_time tl ts' == check_if_code_consumes_fixed_time (Block block) ts);
    assert (forall s. let r = taint_eval_code hd s in taint_eval_code (Block block) s == (if None? r then r else taint_eval_code (Block tl) (Some?.v r)));
    assert (taint_eval_code (Block block) s1 == taint_eval_code (Block tl) s'1); 
    assert (taint_eval_code (Block block) s2 == taint_eval_code (Block tl) s'2); 
    assert (b2t b ==> s1.state.ok /\ s'1.state.ok /\ s2.state.ok /\ s'2.state.ok /\ constTimeInvariant ts s1 s2 ==> constTimeInvariant ts' s'1 s'2); 
    monotone_ok_eval (Block tl) s'1;
    monotone_ok_eval (Block tl) s'2;
    ()

val lemma_code_leakage_free: (ts:taintState) -> (code:tainted_code) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_code_consumes_fixed_time code ts in
  (b2t b ==> isConstantTime code ts /\ isLeakageFree code ts ts')))
 (decreases %[code; 0])

val lemma_block_leakage_free: (ts:taintState) -> (codes:tainted_codes) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_block_consumes_fixed_time codes ts in
  (b2t b ==> isConstantTime (Block codes) ts /\ isLeakageFree (Block codes) ts ts')))
 (decreases %[codes;1])

let rec lemma_code_leakage_free ts code = match code with
  | Ins ins -> lemma_ins_leakage_free ts ins
  | Block block -> lemma_block_leakage_free ts block
  | IfElse ifCond ifTrue ifFalse -> admit()
  | _ -> ()

and lemma_block_leakage_free ts block = match block with
  | [] -> ()
  | hd :: tl -> 
    let b, ts' = check_if_code_consumes_fixed_time hd ts in
    lemma_code_leakage_free ts hd;
    lemma_equal_eval_isConstant hd (Block[hd]) ts ts';
    assume (b2t b ==> isConstantTime (Block [hd]) ts  /\ isLeakageFree (Block [hd]) ts ts');
    lemma_block_leakage_free ts' tl;
    let b_fin, ts_fin = check_if_block_consumes_fixed_time tl ts' in
    assume (b2t b_fin ==> isConstantTime (Block tl) ts' /\ isLeakageFree (Block tl) ts' ts_fin);
    assume ((b2t b) ==> check_if_block_consumes_fixed_time tl ts' == check_if_code_consumes_fixed_time (Block block) ts);
    assert (forall s. let r = taint_eval_code hd s in taint_eval_code (Block block) s == (if None? r then r else taint_eval_code (Block tl) (Some?.v r)));
    
    
    admit()
  
(* val check_if_code_is_leakage_free: (code:tainted_code) -> (ts:taintState) -> (tsExpected:taintState) -> (b:bool{b ==> isLeakageFree code ts tsExpected
	 /\ b ==> isConstantTime code ts})


let check_if_code_is_leakage_free code ts tsExpected = 
  let b, ts' = check_if_code_consumes_fixed_time code ts in

  if b then
    publicTaintsAreAsExpected ts' tsExpected
  else
    b

*)
