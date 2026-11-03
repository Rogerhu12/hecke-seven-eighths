import ThetaGlobal.LocalArchHaar
import ThetaGlobal.LocalArchBounds
import Lean.Util.CollectAxioms

/-! Strict native audit of the actual Haar reduction and Bessel profile bounds.
The same fixed-source high K-type constructor is checked by EntryAudit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lean Elab Command in
run_cmd do
  for name in #[`ThetaGlobal.LocalArchHaar.map_normSq_archHaar,
      `ThetaGlobal.LocalArchHaar.radial_integrable,
      `ThetaGlobal.LocalArchHaar.radial_integral,
      `ThetaGlobal.LocalArchHaar.positive_integrable_of_mellin,
      `ThetaGlobal.LocalArchHaar.positive_integral_eq_mellin,
      `ThetaGlobal.LocalArchHaar.radial_hasMellin,
      `ThetaGlobal.LocalArchBounds.archDirectProfile_bound,
      `ThetaGlobal.LocalArchBounds.archReflectedProfile_bound] do
    unless ((← getEnv).find? name).isSome do
      throwError "THETA_GLOBAL local archimedean declaration {name} was not imported"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "THETA_GLOBAL local archimedean declaration {name} depends on forbidden axiom {axiomName}"
    logInfo m!"THETA_GLOBAL_LOCAL_ARCH_AXIOMS|{name}|{String.intercalate "," (axioms.toList.map toString)}"
