import ThetaGlobal.LocalDigitAverage
import Lean.Util.CollectAxioms

/-! Strict native audit of the actual one-place digit construction.
The final fixed-source adapter is checked separately by EntryAudit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lean Elab Command in
run_cmd do
  for name in #[`ThetaGlobal.LocalDigitArithmetic.thetaPrimeCharacter_eq,
      `ThetaGlobal.LocalDigitArithmetic.probe_additive_eq,
      `ThetaGlobal.LocalDigitArithmetic.primePhase_eq,
      `ThetaGlobal.LocalDigitArithmetic.sphericalDigit_eq,
      `ThetaGlobal.LocalDigitArithmetic.sphericalFactor_eq,
      `ThetaGlobal.LocalDigitArithmetic.forward_mask,
      `ThetaGlobal.LocalDigitArithmetic.zeroth_weyl,
      `ThetaGlobal.LocalDigitEvaluation.bruhat_value,
      `ThetaGlobal.LocalDigitEvaluation.rational_word_value,
      `ThetaGlobal.LocalDigitEvaluation.nonzero_value,
      `ThetaGlobal.LocalDigitEvaluation.nonzero_localDigit,
      `ThetaGlobal.LocalDigitAverage.nonzero_digits] do
    unless ((← getEnv).find? name).isSome do
      throwError "THETA_GLOBAL local digit declaration {name} was not imported"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "THETA_GLOBAL local digit {name} depends on forbidden axiom {axiomName}"
    logInfo m!"THETA_GLOBAL_LOCAL_DIGIT_AXIOMS|{name}|{String.intercalate "," (axioms.toList.map toString)}"
