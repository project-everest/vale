module X64.Leakage_Ins_Xmm_i
open X64.Machine_s
open X64.Memory_i_s
open X64.Semantics_s
open X64.Taint_Semantics_s
module S = X64.Bytes_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers_i
open Types_s
open Words_s
open TypesNative_s
open FStar.FunctionalExtensionality

let xmm_taint (ts:taintState) (x:xmm) = ts.xmmTaint x

let set_xmm_taint (ts:taintState) (xmm:xmm) (taint:taint) : taintState =
  TaintState ts.regTaint ts.flagsTaint ts.cfFlagsTaint (fun x -> if x = xmm then taint else ts.xmmTaint x)

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"
  
val quad32_xor_lemma: (x:quad32) -> Lemma (quad32_xor x x == Mkfour 0 0 0 0) 

let quad32_xor_lemma x =
  assert (quad32_xor x x == Mkfour (nat32_xor x.lo0 x.lo0) (nat32_xor x.lo1 x.lo1)
    (nat32_xor x.hi2 x.hi2) (nat32_xor x.hi3 x.hi3));
  TypesNative_s.reveal_ixor 32 x.lo0 x.lo0;
  TypesNative_s.reveal_ixor 32 x.lo1 x.lo1;
  TypesNative_s.reveal_ixor 32 x.hi2 x.hi2;
  TypesNative_s.reveal_ixor 32 x.hi3 x.hi3;
  FStar.UInt.logxor_self #32 x.lo0;
  FStar.UInt.logxor_self #32 x.lo1;
  FStar.UInt.logxor_self #32 x.hi2;
  FStar.UInt.logxor_self #32 x.hi3

val check_if_pxor_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pxor? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pxor_leakage_free ins ts =
  let S.Pxor dst src, _, _ = ins.ops in
  if src = dst then begin
    let ts' = set_xmm_taint ts dst Public in
    Classical.forall_intro quad32_xor_lemma;
    true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint
  end 
  else begin
    let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
    let ts' = set_xmm_taint ts dst taint in
    true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint
  end

val check_if_paddd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Paddd? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_paddd_leakage_free ins ts =
  let S.Paddd dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_pslld_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pslld? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pslld_leakage_free ins ts =
  let S.Pslld dst amt, _, _ = ins.ops in
  let taint = xmm_taint ts dst in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_psrld_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Psrld? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_psrld_leakage_free ins ts =
  let S.Psrld dst amt, _, _ = ins.ops in
  let taint = xmm_taint ts dst in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pshufb_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pshufb? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pshufb_leakage_free ins ts =
  let S.Pshufb dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_pshufd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pshufd? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pshufd_leakage_free ins ts =
  let S.Pshufd dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pextrq_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pextrq? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

open Words.Two_s
open Words.Four_s

let check_if_pextrq_leakage_free_aux (ins:tainted_ins{let i, _, _ = ins.ops in S.Pextrq? i}) ts =
  let S.Pextrq dst src index, _, _ = ins.ops in
  let fixedTime = operand_does_not_use_secrets dst ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (operand_taint dst ts Public) (xmm_taint ts src) in
  let taint = merge_taint taint ins.t in
  if OMem? dst && taint <> ins.t then false, ts
  else
  let ts' = set_taint dst ts taint in
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint  

val lemma_if_pextrq_leakage_free_aux: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pextrq? i}) -> (ts:taintState) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_pextrq_leakage_free_aux ins ts in b2t b ==>
     isConstantTime (Ins ins) ts /\ isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2)


let lemma_if_pextrq_leakage_free_aux ins ts s1 s2 fuel =
  let S.Pextrq dst src index, _, _ = ins.ops in
  match dst with
  | OConst _ -> ()
  | OReg _ -> ()
  | OMem m ->
  let ptr1 = eval_maddr m s1.state in
  let ptr2 = eval_maddr m s2.state in
  let v1 = eval_xmm src s1.state in
  let v2 = eval_xmm src s2.state in
  let v1 = four_to_two_two v1 in
  let v2 = four_to_two_two v2 in
  let v1 = two_to_nat 32 (two_select v1 (index % 2)) in
  let v2 = two_to_nat 32 (two_select v2 (index % 2)) in
  if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
  else begin
  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
  lemma_frame_store_mem64 ptr2 v2 s2.state.mem  
  end


let check_if_pextrq_leakage_free ins ts =
  Classical.forall_intro_3 (lemma_if_pextrq_leakage_free_aux ins ts);
  check_if_pextrq_leakage_free_aux ins ts

val check_if_pinsrd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pinsrd? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pinsrd_leakage_free ins ts =
  let S.Pinsrd dst src i, _, _ = ins.ops in
  let fixedTime = operand_does_not_use_secrets src ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (xmm_taint ts dst) (operand_taint src ts Public) in
  let taint = merge_taint taint ins.t in
  let ts' = set_xmm_taint ts dst taint in
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pinsrq_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pinsrq? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pinsrq_leakage_free ins ts =
  let S.Pinsrq dst src _, _, _ = ins.ops in
  let fixedTime = operand_does_not_use_secrets src ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (xmm_taint ts dst) (operand_taint src ts Public) in
  let taint = merge_taint taint ins.t in
  let ts' = set_xmm_taint ts dst taint in
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint
  
val check_if_vpslldq_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.VPSLLDQ? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_vpslldq_leakage_free ins ts =
  let S.VPSLLDQ dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pclmuldqd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pclmulqdq? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

#set-options "--z3rlimit 40"

let check_if_pclmuldqd_leakage_free ins ts =
  let S.Pclmulqdq dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_enc_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_enc? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_enc_leakage_free ins ts =
  let S.AESNI_enc dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_enc_last_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_enc_last? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_enc_last_leakage_free ins ts =
  let S.AESNI_enc_last dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_dec_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_dec? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_dec_leakage_free ins ts =
  let S.AESNI_dec dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_dec_last_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_dec_last? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_dec_last_leakage_free ins ts =
  let S.AESNI_dec_last dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_imc_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_imc? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_imc_leakage_free ins ts =
  let S.AESNI_imc dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_keygen_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_keygen_assist? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_keygen_leakage_free ins ts =
  let S.AESNI_keygen_assist dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

let check_if_xmm_ins_consumes_fixed_time ins ts =
  let i, _, _ = ins.ops in
  match i with
    | S.Paddd dst src -> check_if_paddd_leakage_free ins ts
    | S.Pxor dst src -> check_if_pxor_leakage_free ins ts
    | S.Pslld dst amt -> check_if_pslld_leakage_free ins ts
    | S.Psrld dst amt -> check_if_psrld_leakage_free ins ts
    | S.Psrldq _ _ -> (false, ts) // TODO
    | S.Pshufb dst src -> check_if_pshufb_leakage_free ins ts
    | S.Pshufd dst src permutation -> check_if_pshufd_leakage_free ins ts
    | S.Pinsrd _ _ _  -> check_if_pinsrd_leakage_free ins ts
    | S.Pinsrq _ _ _ -> check_if_pinsrq_leakage_free ins ts
    | S.Pcmpeqd _ _ -> (false, ts) // TODO
    | S.Pextrq _ _ _ -> check_if_pextrq_leakage_free ins ts
    | S.VPSLLDQ dst src count -> check_if_vpslldq_leakage_free ins ts
    | S.MOVDQU dst src -> false, ts
    | S.Pclmulqdq dst src imm -> check_if_pclmuldqd_leakage_free ins ts
    | S.AESNI_enc dst src -> check_if_aesni_enc_leakage_free ins ts
    | S.AESNI_enc_last dst src -> check_if_aesni_enc_last_leakage_free ins ts
    | S.AESNI_dec dst src -> check_if_aesni_dec_leakage_free ins ts
    | S.AESNI_dec_last dst src -> check_if_aesni_dec_last_leakage_free ins ts
    | S.AESNI_imc dst src -> check_if_aesni_imc_leakage_free ins ts
    | S.AESNI_keygen_assist dst src imm -> check_if_aesni_keygen_leakage_free ins ts
    
