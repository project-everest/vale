module X64.Leakage_i
open X64.Machine_s
open X64.Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers_i

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

let set_taint (dst:dst_op) ts taint =
  match dst with
  | OReg r -> TaintState (fun x -> if x = r then taint else ts.regTaint x) ts.flagsTaint
  | OMem m -> ts (* Ensured by taint semantics *)
      

let check_if_mov_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = merge_taint (operand_taint src ts) taint in
  match dst with
    | OReg r -> fixedTime, (set_taint dst ts srcTaint)
    | OMem m -> fixedTime, ts (* Handled by taint semantics *)

let check_if_add_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = operand_taint src ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint srcTaint dstTaint) taint in
  match dst with
    | OReg r -> let ts = (set_taint dst ts taint) in
	fixedTime, (TaintState ts.regTaint Secret)
    | OMem m -> (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)

let check_if_addlea_consumes_fixed_time (dst:dst_op) src1 src2 ts taint =
  let ftSrc1 = operand_does_not_use_secrets src1 ts in
  let ftSrc2 = operand_does_not_use_secrets src2 ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc1 && ftSrc2 && ftDst in

  let src1Taint = operand_taint src1 ts in
  let src2Taint = operand_taint src2 ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint src1Taint src2Taint) (merge_taint dstTaint taint) in

  match dst with
    | OReg r -> let ts = (set_taint dst ts taint) in
	   fixedTime, (TaintState ts.regTaint Secret)
    | OMem m ->  (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)

let check_if_addcarry_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = operand_taint src ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint srcTaint dstTaint) taint in

  let taint = merge_taint (ts.flagsTaint) taint in
  match dst with
    | OReg r -> let ts = set_taint dst ts taint in
	  fixedTime, (TaintState ts.regTaint Secret)
    | OMem m -> (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)

let check_if_sub_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = operand_taint src ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint dstTaint srcTaint) taint in

  match dst with
    | OReg r -> let ts = set_taint dst ts taint in
	  fixedTime, (TaintState ts.regTaint Secret)
    | OMem m -> (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)

let check_if_mul_consumes_fixed_time src ts taint =
  let fixedTime = operand_does_not_use_secrets src ts in

  let eaxTaint = operand_taint (OReg Rax) ts in
  let srcTaint = operand_taint src ts in
  let taint = merge_taint (merge_taint srcTaint eaxTaint) taint in

  let ts = set_taint (OReg Rax) ts taint in
  let ts = set_taint (OReg Rdx) ts taint in
  fixedTime, (TaintState ts.regTaint Secret)


let check_if_imul_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = operand_taint src ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint dstTaint srcTaint) taint in

  match dst with
    | OReg r -> let ts = set_taint dst ts taint in
	  fixedTime, (TaintState ts.regTaint Secret)
    | OMem m -> (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)

let check_if_xor_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = operand_taint src ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint dstTaint srcTaint) taint in

  if dst = src then
    let ts = set_taint dst ts Public in
    fixedTime, (TaintState ts.regTaint Secret)
  else match dst with
    | OReg r -> let ts = set_taint dst ts taint in
	  fixedTime, (TaintState ts.regTaint Secret)
    | OMem m -> (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)

let check_if_and_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = operand_taint src ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint dstTaint srcTaint) taint in

  match dst with
    | OReg r -> let ts = set_taint dst ts taint in
	  fixedTime, (TaintState ts.regTaint Secret)
    | OMem m -> (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)

let check_if_shr_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = operand_taint src ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint dstTaint srcTaint) taint in

  match dst with
    | OReg r -> let ts = set_taint dst ts taint in
	  fixedTime, (TaintState ts.regTaint Secret)
    | OMem m -> (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)  

let check_if_shl_consumes_fixed_time (dst:dst_op) src ts taint =
  let ftSrc = operand_does_not_use_secrets src ts in
  let ftDst = operand_does_not_use_secrets dst ts in
  let fixedTime = ftSrc && ftDst in

  let srcTaint = operand_taint src ts in
  let dstTaint = operand_taint dst ts in
  let taint = merge_taint (merge_taint dstTaint srcTaint) taint in

  match dst with
    | OReg r -> let ts = set_taint dst ts taint in
	  fixedTime, (TaintState ts.regTaint Secret)
    | OMem m -> (fixedTime && (not (Secret? taint && Public? dstTaint))), (TaintState ts.regTaint Secret)  


let check_if_instruction_consumes_fixed_time (ins:tainted_ins) ts =
  let taint = match ins.t with
    | None -> Public
    | Some t -> t
  in
  match ins.i with

  | Mov64 dst src -> check_if_mov_consumes_fixed_time dst src ts taint
  | Add64 dst src -> check_if_add_consumes_fixed_time dst src ts taint
  | AddLea64 dst src1 src2 -> check_if_addlea_consumes_fixed_time dst src1 src2 ts taint
  | AddCarry64 dst src -> check_if_addcarry_consumes_fixed_time dst src ts taint
  | Sub64 dst src -> check_if_sub_consumes_fixed_time dst src ts taint
  | Mul64 src -> check_if_mul_consumes_fixed_time src ts taint
  | IMul64 dst src -> check_if_imul_consumes_fixed_time dst src ts taint
  | Xor64 dst src -> check_if_xor_consumes_fixed_time dst src ts taint
  | And64 dst src -> check_if_and_consumes_fixed_time dst src ts taint
  | Shr64 dst amt -> check_if_shr_consumes_fixed_time dst amt ts taint
  | Shl64 dst amt -> check_if_shl_consumes_fixed_time dst amt ts taint

let combine_reg_taints regs1 regs2 =
    fun x -> merge_taint (regs1 x) (regs2 x)

let combine_taint_states (ts:taintState) (ts1:taintState) (ts2:taintState) =
  TaintState (combine_reg_taints ts1.regTaint ts2.regTaint) (merge_taint ts1.flagsTaint ts2.flagsTaint)
  

let rec check_if_block_consumes_fixed_time (block:tainted_codes) (ts:taintState) : bool * taintState =
  match block with
  | [] -> true, ts
  | hd::tl -> let fixedTime, ts_int = check_if_code_consumes_fixed_time hd ts in
    if (not fixedTime) then fixedTime, ts
    else check_if_block_consumes_fixed_time tl ts_int
    

and check_if_code_consumes_fixed_time (code:tainted_code) (ts:taintState) : bool * taintState =
  match code with
  | Ins ins -> check_if_instruction_consumes_fixed_time ins ts
  
  | Block block -> check_if_block_consumes_fixed_time block ts

  | IfElse ifCond ifTrue ifFalse ->
    let cond_taint = match ifCond.ot with
      | None -> Public
      | Some t -> t
    in
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
  
and check_if_loop_consumes_fixed_time (pred:tainted_ocmp) (body:tainted_code) (ts:taintState) : bool * taintState =
  let cond_taint = match pred.ot with
    | None -> Public
    | Some t -> t
  in
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

val check_if_code_is_leakage_free: (code:tainted_code) -> (ts:taintState) -> (tsExpected:taintState) -> (b:bool{b ==> isLeakageFree code ts tsExpected
	 /\ b ==> isConstantTime code ts})


let check_if_code_is_leakage_free code ts tsExpected = 
  let b, ts' = check_if_code_consumes_fixed_time code ts in

  if b then
    publicTaintsAreAsExpected ts' tsExpected
  else
    b
