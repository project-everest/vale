module X64.Leakage_Helpers_i
open X64.Semantics_s
open X64.Machine_s
open X64.Taint_Semantics_s
open X64.Leakage_s

let publicFlagValuesAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
  tsExpected.flagsTaint == Public ==> tsAnalysis.flagsTaint == Public

let publicRegisterValuesAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
  forall r. (tsExpected.regTaint r = Public) ==> (tsAnalysis.regTaint r = Public)

let publicTaintsAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
    publicFlagValuesAreAsExpected tsAnalysis tsExpected
  /\ publicRegisterValuesAreAsExpected tsAnalysis tsExpected


