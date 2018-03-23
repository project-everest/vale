module X64.Leakage_Ins_i
open X64.Machine_s
open X64.Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers_i

val check_if_ins_consumes_fixed_time: (ins:tainted_ins) -> (ts:taintState) -> (res:(bool*taintState){ins_consumes_fixed_time ins ts res})
#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 40"


let check_if_ins_consumes_fixed_time ins ts =
  let i, dsts, srcs = ins.ops in
  let ftSrcs = operands_do_not_use_secrets srcs ts in
  let ftDsts = operands_do_not_use_secrets dsts ts in
  let fixedTime = ftSrcs && ftDsts in

  Classical.forall_intro_2 (fun x y -> lemma_operand_obs_list ts dsts x y);
  Classical.forall_intro_2 (fun x y -> lemma_operand_obs_list ts srcs x y);
  assert (fixedTime ==> (isConstantTime (Ins ins) ts));
  let taint = sources_taint srcs ts ins.t in
  let taint = if AddCarry64? i then merge_taint taint ts.flagsTaint else taint in
  let ts' = set_taints dsts ts taint in
  let b, ts' = match i with
    | Mov64 dst src -> begin
      match dst with
	| OConst _ -> false, ts (* Should not happen *)
	| OReg r -> fixedTime, ts'
	| OMem m -> fixedTime, ts'
    end
    | Mul64 _ -> fixedTime, (TaintState ts'.regTaint Secret)
    | Xor64 dst src ->
        (* Special case for Xor : xor-ing an operand with itself erases secret data *)
        if dst = src then
	  let ts' = set_taint dst ts' Public in
	  fixedTime, TaintState ts'.regTaint Secret
        else
	begin match dst with
	  | OConst _ -> false, (TaintState ts'.regTaint Secret) (* Should not happen *)
	  | OReg r -> fixedTime, (TaintState ts'.regTaint Secret)
	  | OMem m -> fixedTime, (TaintState ts'.regTaint Secret)
        end
    | _ ->
      match dsts with
	| [OConst _] -> true, (TaintState ts'.regTaint Secret) (* Should not happen *)
	| [OReg r] -> fixedTime, (TaintState ts'.regTaint Secret)
	| [OMem m] -> fixedTime, (TaintState ts'.regTaint Secret)
  in
  b, ts'

val lemma_public_flags_same: (ts:taintState) -> (ins:tainted_ins) -> Lemma (forall s1 s2. publicFlagValuesAreSame ts s1 s2 ==> publicFlagValuesAreSame (snd (check_if_ins_consumes_fixed_time ins ts)) (taint_eval_ins ins s1) (taint_eval_ins ins s2))

let lemma_public_flags_same ts ins = ()

val lemma_mov_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Mov64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 2 --max_fuel 2 --z3rlimit 80 --detail_errors"
let lemma_mov_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()

val lemma_add_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Add64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_add_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()

val lemma_sub_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Sub64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_sub_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()

val lemma_imul_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in IMul64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_imul_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()

val lemma_and_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in And64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_and_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()
	  
val lemma_addlea_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in AddLea64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_addlea_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()

val lemma_addcarry_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in AddCarry64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_addcarry_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()

val lemma_mul_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Mul64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--z3rlimit 50"
let lemma_mul_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  ()

val lemma_shr_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Shr64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 1 --max_fuel 1 --z3rlimit 80 --detail_errors"

let lemma_shr_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()
	  
val lemma_shl_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Shl64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_shl_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
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
	  ()

val lemma_xor_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in Xor64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

val lemma_aux_xor: (x:nat64) -> Lemma (FStar.UInt.logxor #64 x x = 0)

let lemma_aux_xor x = 
  FStar.UInt.logxor_self #64 x

let lemma_xor_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  Classical.forall_intro lemma_aux_xor;
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
	  ()

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 2 --max_fuel 2 --z3rlimit 20"
val lemma_ins_same_public: (ts:taintState) -> (ins:tainted_ins) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_ins_same_public ts ins s1 s2 fuel = let i, _, _ = ins.ops in
  match i with
  | Mov64 _ _ -> lemma_mov_same_public ts ins s1 s2 fuel
  | Add64 _ _ -> lemma_add_same_public ts ins s1 s2 fuel
  | AddLea64 _ _ _ -> lemma_addlea_same_public ts ins s1 s2 fuel
  | Sub64 _ _ -> lemma_sub_same_public ts ins s1 s2 fuel
  | IMul64 _ _ -> lemma_imul_same_public ts ins s1 s2 fuel
  | And64 _ _ -> lemma_and_same_public ts ins s1 s2 fuel
  | Mul64 _ -> lemma_mul_same_public ts ins s1 s2 fuel
  | Xor64 _ _ -> lemma_xor_same_public ts ins s1 s2 fuel
  | AddCarry64 _ _ -> lemma_addcarry_same_public ts ins s1 s2 fuel
  | Shl64 _ _ -> lemma_shl_same_public ts ins s1 s2 fuel
  | Shr64 _ _ -> lemma_shr_same_public ts ins s1 s2 fuel

val lemma_ins_leakage_free: (ts:taintState) -> (ins:tainted_ins) -> Lemma
 (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'))

let lemma_ins_leakage_free ts ins =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let p s1 s2 fuel = b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2 in
  let my_lemma s1 s2 fuel : Lemma(p s1 s2 fuel) = lemma_ins_same_public ts ins s1 s2 fuel in
  let open FStar.Classical in
  forall_intro_3 my_lemma
