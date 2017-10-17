module X64.Leakage_i
open X64.Machine_s
open X64.Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers_i

open FStar.Tactics

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics'"

let merge_taint t1 t2 =
  if Secret? t1 || Secret? t2 then
    Secret
  else
    Public

let operand_taint (op:operand) ts =
  match op with
    | OConst _ -> Public
    | OReg reg -> ts.regTaint reg
    | OMem _ -> Public

let maddr_does_not_use_secrets addr ts =
  match addr with
    | MConst _ -> true
    | MReg r _ -> Public? (operand_taint (OReg r) ts)
    | MIndex base _ index _ ->
        let baseTaint = operand_taint (OReg base) ts in
	let indexTaint = operand_taint (OReg index) ts in
	(Public? baseTaint) && (Public? indexTaint)

let operand_does_not_use_secrets op ts =
  match op with
  | OConst _ | OReg _ -> true
  | OMem m -> maddr_does_not_use_secrets m ts

val lemma_operand_obs:  (ts:taintState) ->  (dst:operand) -> (s1 : traceState) -> (s2:traceState) -> Lemma
 (requires (operand_does_not_use_secrets dst ts) /\ publicValuesAreSame ts s1 s2)
(ensures (operand_obs s1 dst) = (operand_obs s2 dst))

#reset-options "--z3rlimit 20"
let lemma_operand_obs ts dst s1 s2 = match dst with
  | OConst _ | OReg _ -> ()
  | OMem m -> ()
#reset-options "--z3rlimit 5"
  
let set_taint (dst:operand) ts taint =
  match dst with
  | OConst _ -> ts  (* Shouldn't actually happen *)
  | OReg r -> TaintState (fun x -> if x = r then taint else ts.regTaint x) ts.flagsTaint
  | OMem m -> ts (* Ensured by taint semantics *)

let rec operands_do_not_use_secrets ops ts = match ops with
  | [] -> true
  | hd :: tl -> operand_does_not_use_secrets hd ts && (operands_do_not_use_secrets tl ts)

val lemma_operands_imply_op: (ts:taintState) -> (ops:list operand{Cons? ops}) -> Lemma
(requires (operands_do_not_use_secrets ops ts))
(ensures (operand_does_not_use_secrets (List.Tot.Base.hd ops) ts))

let lemma_operands_imply_op ts ops = match ops with
| hd :: tl -> ()

val lemma_operand_obs_list: (ts:taintState) -> (ops:list operand) -> (s1:traceState) -> (s2:traceState) -> Lemma 
(requires (operands_do_not_use_secrets ops ts /\ publicValuesAreSame ts s1 s2))
(ensures  (operand_obs_list s1 ops) = (operand_obs_list s2 ops))

let rec lemma_operand_obs_list ts ops s1 s2 = match ops with
  | [] -> ()
  | hd :: tl -> assert (operand_does_not_use_secrets hd ts); assert_by_tactic (operand_obs s1 hd = operand_obs s2 hd) (apply_lemma (quote (lemma_operand_obs ts))); lemma_operand_obs_list ts tl s1 s2

let rec sources_taint srcs ts taint = match srcs with
  | [] -> taint
  | hd :: tl -> merge_taint (operand_taint hd ts) (sources_taint tl ts taint)

let rec set_taints dsts ts taint = match dsts with
  | [] -> ts
  | hd :: tl -> set_taints tl (set_taint hd ts taint) taint

let ins_consumes_fixed_time (ins : tainted_ins) (ts:taintState) (res:bool*taintState) =
  let b, ts' = res in
  ((b2t b) ==> isConstantTime (Ins ins) ts) (*/\ ((b2t b) ==> isLeakageFree (Ins ins) ts ts')*)

val check_if_ins_consumes_fixed_time: (ins:tainted_ins) -> (ts:taintState) -> (res:(bool*taintState){ins_consumes_fixed_time ins ts res})
#reset-options "--z3rlimit 30"

val lemma_taint_sources: (ins:tainted_ins) -> (ts:taintState) -> Lemma
(let i, d, s = ins.ops in
forall src. List.Tot.Base.mem src s /\ Public? (sources_taint s ts ins.t) ==> Public? (operand_taint src ts))

let lemma_taint_sources ins ts = ()

val lemma_public_op_are_same: (ts:taintState) -> (op:operand) -> (s1:traceState) -> (s2:traceState) -> Lemma 
(requires operand_does_not_use_secrets op ts /\ Public? (operand_taint op ts) /\ publicValuesAreSame ts s1 s2 /\ taint_match op Public s1.memTaint s1.state /\ taint_match op Public s2.memTaint s2.state)
(ensures eval_operand op s1.state = eval_operand op s2.state)

let lemma_public_op_are_same ts op s1 s2 = ()

let check_if_ins_consumes_fixed_time ins ts =
  let i, dsts, srcs = ins.ops in
  let ftSrcs = operands_do_not_use_secrets srcs ts in
  let ftDsts = operands_do_not_use_secrets dsts ts in
  let fixedTime = ftSrcs && ftDsts in

  assert_by_tactic (forall s1 s2. {:pattern (publicValuesAreSame ts s1 s2)} (operands_do_not_use_secrets dsts ts /\ publicValuesAreSame ts s1 s2) ==>
    (operand_obs_list s1 dsts) = (operand_obs_list s2 dsts)) (s1 <-- forall_intro; s2 <-- forall_intro; h <-- implies_intro; apply_lemma (quote (lemma_operand_obs_list ts dsts))); 

  assert_by_tactic (forall s1 s2. (operands_do_not_use_secrets srcs ts /\ publicValuesAreSame ts s1 s2) ==> (operand_obs_list s1 srcs) = (operand_obs_list s2 srcs)) (s1 <-- forall_intro; s2 <-- forall_intro; h <-- implies_intro; apply_lemma (quote (lemma_operand_obs_list ts srcs)));
  assert (fixedTime ==> (isConstantTime (Ins ins) ts));
  let taint = sources_taint srcs ts ins.t in
  let taint = if AddCarry64? i then merge_taint taint ts.flagsTaint else taint in
  let ts' = set_taints dsts ts taint in
  let b, ts' = match i with
    | Mov64 dst src -> begin
      match dst with
	| OConst _ -> false, ts (* Should not happen *)
	| OReg r -> fixedTime, ts'
	| OMem m -> (fixedTime && (not (Secret? taint && Public? (operand_taint (OMem m) ts)))), ts'
    end
    | Mul64 _ -> fixedTime, (TaintState ts'.regTaint Secret)
    | Xor64 dst src -> 
        (* Special case for Xor : xor-ing an operand with itself erases secret data *)
        if dst = src then
	  let ts' = set_taint dst ts' Public in
	  fixedTime, TaintState ts'.regTaint Secret
        else begin match dst with
	  | OReg r -> fixedTime, (TaintState ts'.regTaint Secret)
	  | OMem m -> (fixedTime && (not (Secret? taint && Public? (operand_taint (OMem m) ts)))), (TaintState ts'.regTaint Secret)
        end
    | _ -> 
      match dsts with
	| [OConst _] -> false, ts (* Should not happen *)
	| [OReg r] -> fixedTime, (TaintState ts'.regTaint Secret)
	| [OMem m] ->  (fixedTime && (not (Secret? taint && Public? (operand_taint (OMem m) ts)))), (TaintState ts'.regTaint Secret)
  in
  b, ts'

val lemma_public_flags_same: (ts:taintState) -> (ins:tainted_ins) -> Lemma (forall s1 s2. publicFlagValuesAreSame ts s1 s2 ==> publicFlagValuesAreSame (snd (check_if_ins_consumes_fixed_time ins ts)) (taint_eval_ins ins s1) (taint_eval_ins ins s2))

let lemma_public_flags_same ts ins = ()

val lemma_mov_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Mov64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_mov_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)
  
val lemma_add_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Add64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

#set-options "--z3rlimit 60"
let lemma_add_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_sub_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Sub64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_sub_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_imul_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in IMul64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_imul_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_and_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in And64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_and_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

#set-options "--z3rlimit 80"
val lemma_addlea_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in AddLea64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_addlea_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_addcarry_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in AddCarry64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

#set-options "--z3rlimit 100"
let lemma_addcarry_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match i with
    | AddCarry64 dst src ->  assert (Secret? ts.flagsTaint /\ OReg? dst ==> Secret? (operand_taint dst ts'));
  assert (Public? ts.flagsTaint /\ publicValuesAreSame ts s1 s2 ==> s1.state.flags = s2.state.flags);
  assert (b2t b /\ Public? ins.t /\ Public? (operand_taint src ts) /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> eval_operand src s1.state = eval_operand src s2.state);
  assert (b2t b /\ Public? ins.t /\ Public? (operand_taint dst ts) /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> eval_operand dst s1.state = eval_operand dst s2.state);
  assert (b2t b /\ Secret? (operand_taint src ts) /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2);
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_mul_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Mul64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_mul_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match i with
    | Mul64 src -> 
    assert (b2t b /\ Public? ins.t /\ Public? (operand_taint src ts) /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> eval_operand src s1.state = eval_operand src s2.state);
    assert (Secret? (operand_taint (OReg Rax) ts) /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2);
    assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_shr_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Shr64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_shr_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_shl_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Shl64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_shl_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

#set-options "--z3rlimit 100"
val lemma_xor_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Xor64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

val lemma_aux_xor: (x:int{FStar.UInt.fits x 64}) -> Lemma (logxor x x = 0)

let lemma_aux_xor x = 
  FStar.UInt.logxor_self #64 x
  
let lemma_xor_same_public ts ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match i with
  | Xor64 dst src ->
    if dst = src then (assert_by_tactic (forall (v:int{FStar.UInt.fits v 64}). logxor v v = 0) (v <-- forall_intro; apply_lemma (quote lemma_aux_xor)); 
    assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2))

    else
    assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)



#set-options "--z3rlimit 20"
val lemma_ins_same_public: (ts:taintState) -> (ins:tainted_ins) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2))

let lemma_ins_same_public ts ins s1 s2 = let i, _, _ = ins.ops in
  match i with
  | Mov64 _ _ -> lemma_mov_same_public ts ins s1 s2
  | Add64 _ _ -> lemma_add_same_public ts ins s1 s2
  | AddLea64 _ _ _ -> lemma_addlea_same_public ts ins s1 s2
  | Sub64 _ _ -> lemma_sub_same_public ts ins s1 s2
  | IMul64 _ _ -> lemma_imul_same_public ts ins s1 s2
  | And64 _ _ -> lemma_and_same_public ts ins s1 s2
  | Mul64 _ -> lemma_mul_same_public ts ins s1 s2
  | Xor64 _ _ -> lemma_xor_same_public ts ins s1 s2
  | AddCarry64 _ _ -> lemma_addcarry_same_public ts ins s1 s2
  | Shl64 _ _ -> lemma_shl_same_public ts ins s1 s2
  | Shr64 _ _ -> lemma_shr_same_public ts ins s1 s2

val lemma_ins_leakage_free: (ts:taintState) -> (ins:tainted_ins) -> Lemma
 (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'))

let lemma_ins_leakage_free ts ins =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let p s1 s2 = b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) ts ts' s1 s2 in
  let my_lemma s1 s2 : Lemma(p s1 s2) = lemma_ins_same_public ts ins s1 s2 in
  let open FStar.Classical in
  forall_intro_2 my_lemma

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

let test_lemma (code1: tainted_code) (code2:tainted_code) (ts:taintState) =
  assert ((forall s. taint_eval_code code1 s == taint_eval_code code2 s) /\ check_if_code_consumes_fixed_time code1 ts == check_if_code_consumes_fixed_time code2 ts /\
  isConstantTime code1 ts ==> isConstantTime code2 ts)

#set-options "--z3rlimit 30"
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
    assume (check_if_code_consumes_fixed_time hd ts == check_if_block_consumes_fixed_time [hd] ts);
    assume (forall s. taint_eval_code hd s == taint_eval_code (Block [hd]) s);
    assume (b2t b ==> isConstantTime hd ts /\ isLeakageFree hd ts ts');
    assert (b2t b ==> isConstantTime (Block [hd]) ts); (* /\ isLeakageFree (Block [hd]) ts ts'); *)
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
