module X64.Leakage_s

open X64.Machine_s
open X64.Semantics_s
open X64.Taint_Semantics_s

noeq type taintState = 
  | TaintState: regTaint: (reg -> taint) -> flagsTaint: taint -> taintState

let publicFlagValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
  ts.flagsTaint = Public ==> (s1.state.flags = s2.state.flags)
  
let publicRegisterValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
  forall r.
      ts.regTaint r = Public
    ==> (s1.state.regs r = s2.state.regs r)

let publicMemValuesAreSame (s1:traceState) (s2:traceState) =
  forall x. (Public? (s1.memTaint.[x]) || Public? (s2.memTaint.[x])) ==> (valid_mem64 x s1.state.mem /\ valid_mem64 x s2.state.mem) ==> (eval_mem x s1.state == eval_mem x s2.state)

let publicValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
   publicRegisterValuesAreSame ts s1 s2
  /\ publicFlagValuesAreSame ts s1 s2
  /\ publicMemValuesAreSame s1 s2

let constTimeInvariant (ts:taintState) (s:traceState) (s':traceState) =
    publicValuesAreSame ts s s'
  /\ s.trace = s'.trace


let isConstantTimeGivenStates (code:tainted_code) (fuel:nat) (ts:taintState) (s1:traceState) (s2:traceState) =
  let r1 = taint_eval_code code fuel s1 in
  let r2 = taint_eval_code code fuel s2 in
  ( (Some? r1) /\ (Some? r2)
   /\ s1.state.ok /\ (Some?.v r1).state.ok
   /\ s2.state.ok /\ (Some?.v r2).state.ok
   /\ constTimeInvariant ts s1 s2
  ) ==> (Some?.v r1).trace = (Some?.v r2).trace

let isConstantTime (code:tainted_code) (fuel:nat) (ts:taintState) =
  forall s1 s2.
      isConstantTimeGivenStates code fuel ts s1 s2

let isExplicitLeakageFreeGivenStates (code:tainted_code) (fuel:nat) (ts:taintState) (ts':taintState) (s1:traceState) (s2:traceState) =
  let r1 = taint_eval_code code fuel s1 in
  let r2 = taint_eval_code code fuel s2 in
 ( Some? r1 /\ Some? r2
  /\ s1.state.ok /\ (Some?.v r1).state.ok
  /\ s2.state.ok /\ (Some?.v r2).state.ok
  /\ constTimeInvariant ts s1 s2
 ) ==> publicValuesAreSame ts' (Some?.v r1) (Some?.v r2)

let isExplicitLeakageFree (code:tainted_code) (fuel:nat) (ts:taintState) (ts':taintState) =
  forall s1 s2.
    isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2

let isLeakageFree (code:tainted_code) (fuel:nat) (ts:taintState) (ts':taintState) =
    isConstantTime code fuel ts
  /\ isExplicitLeakageFree code fuel ts ts'
