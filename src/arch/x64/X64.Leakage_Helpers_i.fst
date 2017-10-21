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
  registerAsExpected Rax tsAnalysis tsExpected &&
  registerAsExpected Rbx tsAnalysis tsExpected &&
  registerAsExpected Rcx tsAnalysis tsExpected &&
  registerAsExpected Rdx tsAnalysis tsExpected &&
  registerAsExpected Rsi tsAnalysis tsExpected &&
  registerAsExpected Rdi tsAnalysis tsExpected &&
  registerAsExpected Rbp tsAnalysis tsExpected &&
  registerAsExpected Rsp tsAnalysis tsExpected &&
  registerAsExpected R8 tsAnalysis tsExpected &&
  registerAsExpected R9 tsAnalysis tsExpected &&
  registerAsExpected R10 tsAnalysis tsExpected &&
  registerAsExpected R11 tsAnalysis tsExpected &&
  registerAsExpected R12 tsAnalysis tsExpected &&
  registerAsExpected R13 tsAnalysis tsExpected &&
  registerAsExpected R14 tsAnalysis tsExpected &&
  registerAsExpected R15 tsAnalysis tsExpected

let publicTaintsAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
    publicFlagValuesAreAsExpected tsAnalysis tsExpected
  && publicRegisterValuesAreAsExpected tsAnalysis tsExpected


