import HeckeSkeleton.Theta
import ThetaGlobal.LocalGammaOrientation
import Lean.Util.CollectAxioms

/-!
# Admission gate for the five THETA_GLOBAL entry points

This audit uses the actual skeleton declarations after their complete
dependency closure has been built. It deliberately rejects `sorryAx` and
every nonstandard axiom, including any inherited through a source
constructor. The local high K-type input and exterior digit table are
constructed from the same actual fixed source.

The presence of this file is not a compilation certificate. A successful
run must print all five `THETA_GLOBAL_AXIOMS` records and all 44
`THETA_GLOBAL_INTERFACE_AXIOMS` records, then exit with code 0.
-/

open Lean Elab Command in
run_cmd do
  for name in #[`HeckeSkeleton.finiteMellinData,
      `HeckeSkeleton.finite_valuation_cutoff,
      `HeckeSkeleton.finite_valuation_decay,
      `HeckeSkeleton.marked_reflected_absolute,
      `HeckeSkeleton.marked_reflection] do
    unless ((← getEnv).find? name).isSome do
      throwError "THETA_GLOBAL entry {name} was not imported"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "THETA_GLOBAL entry {name} depends on forbidden axiom {axiomName}"
    logInfo m!"THETA_GLOBAL_AXIOMS|{name}|{String.intercalate "," (axioms.toList.map toString)}"

/- The table specification and returned reflection package are part of the
actual public interface. The orientation lemmas check the character label
used when connecting inverse-character local Mellin formulas. The canonical
archimedean constructor, retained source certificate, actual profiles, Haar
transport, Mellin formulas and bounds are checked in the same strict gate. -/
open Lean Elab Command in
run_cmd do
  for name in #[`HeckeSkeleton.thetaFiniteSource,
      `HeckeSkeleton.FiniteSkeletonSource.coefficient_shell_spec,
      `HeckeSkeleton.FiniteSkeletonSource.data_C₀,
      `HeckeSkeleton.FiniteSkeletonSource.data_A₀,
      `HeckeSkeleton.markedReflection,
      `HeckeSkeleton.thetaRecipe_arithmeticData,
      `HeckeSkeleton.localExteriorDigitInput,
      `ThetaGlobal.LocalDigitInput.input,
      `ThetaGlobal.LocalDigitAverage.nonzero_digits,
      `ThetaGlobal.LocalGammaOrientation.archShift_inv,
      `ThetaGlobal.LocalGammaOrientation.archRadial_inv,
      `ThetaGlobal.LocalGammaOrientation.directGammaProduct_eq_archGammaProduct_inv,
      `ThetaGlobal.LocalGammaOrientation.gammaPair_inv_eq_directGammaPair,
      `ThetaGlobal.LocalGammaOrientation.directGammaPair_inv_eq_gammaPair,
      `ThetaGlobal.LocalGammaOrientation.directGammaPair_product_eq_archGammaProduct_inv,
      `ThetaGlobal.LocalGammaOrientation.reflectionMultiplier_eq_gamma_quotient,
      `ThetaGlobal.LocalArchRootCore.coreInImage_archRootCore,
      `ThetaGlobal.LocalArchRootCore.harmonicInclusion_traceRootCore,
      `ThetaGlobal.LocalArchRootCore.traceJacquet_whittaker,
      `ThetaGlobal.LocalArchRootCore.traceRootCore_value,
      `ThetaGlobal.LocalArchRootCore.traceRootCore_functional_nonzero,
      `ThetaGlobal.LocalArchProfile.inclusion_vector,
      `ThetaGlobal.LocalArchProfile.functional_nonzero,
      `ThetaGlobal.LocalArchProfile.direct_profile,
      `ThetaGlobal.LocalArchProfile.reflected_profile,
      `ThetaGlobal.LocalArchHaar.map_normSq_archHaar,
      `ThetaGlobal.LocalArchHaar.radial_integrable,
      `ThetaGlobal.LocalArchHaar.radial_integral,
      `ThetaGlobal.LocalArchHaar.positive_integrable_of_mellin,
      `ThetaGlobal.LocalArchHaar.positive_integral_eq_mellin,
      `ThetaGlobal.LocalArchHaar.radial_hasMellin,
      `ThetaGlobal.LocalArchMellin.directConstant_nonzero,
      `ThetaGlobal.LocalArchMellin.reflectedConstant_nonzero,
      `ThetaGlobal.LocalArchMellin.direct_mellin,
      `ThetaGlobal.LocalArchMellin.reflected_mellin,
      `ThetaGlobal.LocalArchBounds.archDirectProfile_bound,
      `ThetaGlobal.LocalArchBounds.archReflectedProfile_bound,
      `ThetaGlobal.LocalArchInput.direct_bound,
      `ThetaGlobal.LocalArchInput.reflected_bound,
      `ThetaGlobal.LocalArchInput.input,
      `HeckeSkeleton.localHighKMellinInput,
      `ThetaGlobal.FiniteFullProduct.local_value_nonzero_of_whittaker,
      `ThetaGlobal.FiniteFixedSource.source_nonempty,
      `ThetaGlobal.FiniteFixedSource.Source.archimedean_nonzero] do
    unless ((← getEnv).find? name).isSome do
      throwError "THETA_GLOBAL interface declaration {name} was not imported"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "THETA_GLOBAL interface declaration {name} depends on forbidden axiom {axiomName}"
    logInfo m!"THETA_GLOBAL_INTERFACE_AXIOMS|{name}|{String.intercalate "," (axioms.toList.map toString)}"
