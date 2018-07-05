module X64.Leakage_Helpers_i
open X64.Semantics_s
open X64.Machine_s
open X64.Taint_Semantics_s
open X64.Leakage_s

val publicFlagValuesAreAsExpected: (tsAnalysis:taintState) -> (tsExpected:taintState) -> b:bool{b <==> (Public? tsExpected.flagsTaint ==> Public? tsAnalysis.flagsTaint)}

val publicRegisterValuesAreAsExpected: (tsAnalysis:taintState) -> (tsExpected:taintState) -> b:bool{b <==> (forall r. (Public? (tsExpected.regTaint r) ==> Public? (tsAnalysis.regTaint r)))}

val publicTaintsAreAsExpected: (tsAnalysis:taintState) -> (tsExpected:taintState) -> b:bool

let publicFlagValuesAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
  (tsExpected.flagsTaint = Public && tsAnalysis.flagsTaint = Public) || (tsExpected.flagsTaint = Secret)

let registerAsExpected (r:reg) (tsAnalysis:taintState) (tsExpected:taintState) =
  (tsExpected.regTaint r = Public && tsAnalysis.regTaint r = Public) || (tsExpected.regTaint r = Secret)

let publicRegisterValuesAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
  registerAsExpected  0 tsAnalysis tsExpected &&
  registerAsExpected  1 tsAnalysis tsExpected &&
  registerAsExpected  2 tsAnalysis tsExpected &&
  registerAsExpected  3 tsAnalysis tsExpected &&
  registerAsExpected  4 tsAnalysis tsExpected &&
  registerAsExpected  5 tsAnalysis tsExpected &&
  registerAsExpected  6 tsAnalysis tsExpected &&
  registerAsExpected  7 tsAnalysis tsExpected &&
  registerAsExpected  8 tsAnalysis tsExpected &&
  registerAsExpected  9 tsAnalysis tsExpected &&
  registerAsExpected 10 tsAnalysis tsExpected &&
  registerAsExpected 11 tsAnalysis tsExpected &&
  registerAsExpected 12 tsAnalysis tsExpected &&
  registerAsExpected 13 tsAnalysis tsExpected &&
  registerAsExpected 14 tsAnalysis tsExpected &&
  registerAsExpected 15 tsAnalysis tsExpected

let publicTaintsAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
    publicFlagValuesAreAsExpected tsAnalysis tsExpected
  && publicRegisterValuesAreAsExpected tsAnalysis tsExpected


