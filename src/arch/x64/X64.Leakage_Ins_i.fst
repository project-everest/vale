module X64.Leakage_Ins_i
open X64.Machine_s
open X64.Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers_i

open FStar.Tactics

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics'"

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

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics' --z3rlimit 20"
let lemma_operand_obs ts dst s1 s2 = match dst with
  | OConst _ | OReg _ -> ()
  | OMem m -> ()
#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics' --z3rlimit 5"
  
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
(ensures  (operand_obs_list s1 ops) == (operand_obs_list s2 ops))

let rec lemma_operand_obs_list ts ops s1 s2 = match ops with
  | [] -> ()
  | hd :: tl -> assert (operand_does_not_use_secrets hd ts); assert_by_tactic (operand_obs s1 hd = operand_obs s2 hd) (apply_lemma (quote (lemma_operand_obs ts))); lemma_operand_obs_list ts tl s1 s2

let rec sources_taint srcs ts taint = match srcs with
  | [] -> taint
  | hd :: tl -> merge_taint (operand_taint hd ts) (sources_taint tl ts taint)

let rec set_taints dsts ts taint = match dsts with
  | [] -> ts
  | hd :: tl -> set_taints tl (set_taint hd ts taint) taint

let ins_consumes_fixed_time (ins : tainted_ins) (fuel:nat) (ts:taintState) (res:bool*taintState) =
  let b, ts' = res in
  ((b2t b) ==> isConstantTime (Ins ins) fuel ts)

val check_if_ins_consumes_fixed_time: (ins:tainted_ins) -> (fuel:nat) -> (ts:taintState) -> (res:(bool*taintState){ins_consumes_fixed_time ins fuel ts res})
#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics' --z3rlimit 30"

val lemma_taint_sources: (ins:tainted_ins) -> (ts:taintState) -> Lemma
(let i, d, s = ins.ops in
forall src. List.Tot.Base.mem src s /\ Public? (sources_taint s ts ins.t) ==> Public? (operand_taint src ts))

let lemma_taint_sources ins ts = ()

val lemma_public_op_are_same: (ts:taintState) -> (op:operand) -> (s1:traceState) -> (s2:traceState) -> Lemma 
(requires operand_does_not_use_secrets op ts /\ Public? (operand_taint op ts) /\ publicValuesAreSame ts s1 s2 /\ taint_match op Public s1.memTaint s1.state /\ taint_match op Public s2.memTaint s2.state /\ valid_operand op s1.state /\ valid_operand op s2.state)
(ensures eval_operand op s1.state == eval_operand op s2.state)

let lemma_public_op_are_same ts op s1 s2 = ()

let check_if_ins_consumes_fixed_time ins fuel ts =
  let i, dsts, srcs = ins.ops in
  let ftSrcs = operands_do_not_use_secrets srcs ts in
  let ftDsts = operands_do_not_use_secrets dsts ts in
  let fixedTime = ftSrcs && ftDsts in

  assert_by_tactic (forall s1 s2. {:pattern (publicValuesAreSame ts s1 s2)} (operands_do_not_use_secrets dsts ts /\ publicValuesAreSame ts s1 s2) ==>
    (operand_obs_list s1 dsts) == (operand_obs_list s2 dsts)) (s1 <-- forall_intro; s2 <-- forall_intro; h <-- implies_intro; apply_lemma (quote (lemma_operand_obs_list ts dsts))); 

  assert_by_tactic (forall s1 s2. (operands_do_not_use_secrets srcs ts /\ publicValuesAreSame ts s1 s2) ==> (operand_obs_list s1 srcs) == (operand_obs_list s2 srcs)) (s1 <-- forall_intro; s2 <-- forall_intro; h <-- implies_intro; apply_lemma (quote (lemma_operand_obs_list ts srcs)));
  assert (fixedTime ==> (isConstantTime (Ins ins) fuel ts));
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
	  | OConst _ -> false, ts (* Should not happen *)
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

//val lemma_public_flags_same: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins) -> Lemma (forall s1 s2. publicFlagValuesAreSame ts s1 s2 ==> publicFlagValuesAreSame (snd (check_if_ins_consumes_fixed_time ins fuel ts)) (taint_eval_ins ins s1) (taint_eval_ins ins s2))

//let lemma_public_flags_same ts fuel ins = ()

val lemma_mov_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in Mov64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics' --z3rlimit 80"
let lemma_mov_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src] -> 
	  let v1 = eval_operand src s1.state in
	  let v2 = eval_operand src s2.state in
	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
          assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2) 

val lemma_add_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in Add64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--z3cliopt smt.CASE_SPLIT=3 --initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics' --z3rlimit 100"
let lemma_add_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src1; src2] ->
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = (v11 + v12) % nat64_max in
	  let v2 = (v21 + v22) % nat64_max in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_sub_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in Sub64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_sub_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
 match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src1; src2] ->
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = (v11 - v12) % nat64_max in
	  let v2 = (v21 - v22) % nat64_max in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_imul_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in IMul64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_imul_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
 match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src1; src2] ->
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = FStar.UInt.mul_mod #64 v11 v12 in
	  let v2 = FStar.UInt.mul_mod #64 v21 v22 in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_and_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in And64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_and_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src1; src2] ->
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = FStar.UInt.logand #64 v11 v12 in
	  let v2 = FStar.UInt.logand #64 v21 v22 in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_addlea_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in AddLea64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_addlea_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [dst; src1; src2] ->
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = (v11 + v12) % nat64_max in
	  let v2 = (v21 + v22) % nat64_max in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_addcarry_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in AddCarry64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_addcarry_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src1; src2] ->
	  let c1 = if cf(s1.state.flags) then 1 else 0 in
	  let c2 = if cf(s2.state.flags) then 1 else 0 in
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = (v11 + v12 + c1) % nat64_max in
	  let v2 = (v21 + v22 + c2) % nat64_max in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_mul_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in Mul64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_mul_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_shr_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in Shr64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_shr_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src1; src2] ->
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = FStar.UInt.shift_right #64 v11 v12 in
	  let v2 = FStar.UInt.shift_right #64 v21 v22 in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_shl_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in Shl64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_shl_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] -> 
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src1; src2] ->
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = FStar.UInt.shift_left #64 v11 v12 in
	  let v2 = FStar.UInt.shift_left #64 v21 v22 in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

val lemma_xor_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins{let i, _, _ = ins.ops in Xor64? i}) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

val lemma_aux_xor: (x:int{FStar.UInt.fits x 64}) -> Lemma (FStar.UInt.logxor #64 x x = 0)

let lemma_aux_xor x = 
  FStar.UInt.logxor_self #64 x

let lemma_xor_same_public ts fuel ins s1 s2 =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  assert_by_tactic (forall (v:int{FStar.UInt.fits v 64}). FStar.UInt.logxor #64 v v = 0) (v <-- forall_intro; apply_lemma (quote lemma_aux_xor));
  match dsts with
    | [OConst _] -> ()
    | [OReg _] -> ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
	| [src1; src2] ->
	  let v11 = eval_operand src1 s1.state in
	  let v12 = eval_operand src2 s1.state in
	  let v21 = eval_operand src1 s2.state in
	  let v22 = eval_operand src2 s2.state in	  
	  let v1 = FStar.UInt.logxor #64 v11 v12 in
	  let v2 = FStar.UInt.logxor #64 v21 v22 in
 	  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
	  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
	  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
	  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
	  lemma_frame_store_mem64 ptr2 v2 s2.state.mem;
	  assert (b2t b /\ r1.state.ok /\ r2.state.ok /\ publicValuesAreSame ts s1 s2 ==> publicValuesAreSame ts' r1 r2)

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --using_facts_from '* -FStar.Reflection -FStar.Tactics' --z3rlimit 20"
val lemma_ins_same_public: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins) -> (s1:traceState) -> (s2:traceState) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_ins_same_public ts fuel ins s1 s2 = let i, _, _ = ins.ops in
  match i with
  | Mov64 _ _ -> lemma_mov_same_public ts fuel ins s1 s2
  | Add64 _ _ -> lemma_add_same_public ts fuel ins s1 s2
  | AddLea64 _ _ _ -> lemma_addlea_same_public ts fuel ins s1 s2
  | Sub64 _ _ -> lemma_sub_same_public ts fuel ins s1 s2
  | IMul64 _ _ -> lemma_imul_same_public ts fuel ins s1 s2
  | And64 _ _ -> lemma_and_same_public ts fuel ins s1 s2
  | Mul64 _ -> lemma_mul_same_public ts fuel ins s1 s2
  | Xor64 _ _ -> lemma_xor_same_public ts fuel ins s1 s2
  | AddCarry64 _ _ -> lemma_addcarry_same_public ts fuel ins s1 s2
  | Shl64 _ _ -> lemma_shl_same_public ts fuel ins s1 s2
  | Shr64 _ _ -> lemma_shr_same_public ts fuel ins s1 s2

val lemma_ins_leakage_free: (ts:taintState) -> (fuel:nat) -> (ins:tainted_ins) -> Lemma
 (let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  (b2t b ==> isConstantTime (Ins ins) fuel ts /\ isLeakageFree (Ins ins) fuel ts ts'))

let lemma_ins_leakage_free ts fuel ins =
  let b, ts' = check_if_ins_consumes_fixed_time ins fuel ts in
  let p s1 s2 = b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2 in
  let my_lemma s1 s2 : Lemma(p s1 s2) = lemma_ins_same_public ts fuel ins s1 s2 in
  let open FStar.Classical in
  forall_intro_2 my_lemma
