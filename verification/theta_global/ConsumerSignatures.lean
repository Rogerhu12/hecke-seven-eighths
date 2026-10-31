import HeckeSkeleton.Main
import Lean.Util.CollectAxioms

/-!
# THETA_GLOBAL consumer signatures

These checks use the canonical archimedean input selected inside Theta.
They check Principal, Moments and Main without an extra local-data parameter
after the native Main dependency closure has been built.

The consumers still depend on unrelated, pre-existing skeleton admissions.
Their axiom reports therefore allow `sorryAx` and are compatibility records,
not certificates for THETA_GLOBAL or for the seven-eighths endpoint. The
separate EntryAudit.lean rejects `sorryAx` in the five THETA_GLOBAL targets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.maxSteps 1000000

noncomputable section

open NumberField HeckeSkeleton
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP

section FixedContext

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

example
    (hreflection : MarkedCoefficientReflectionInput K (places K c)
      (probeData K c).arithmetic (HeckeSkeleton.finiteMellinData K c)
      (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))) :
    CompletedMarkedEnergy K c :=
  HeckeSkeleton.completedMarkedEnergy K c hreflection

example :
    (probeMeasures K c).principalInput (probeData K c) (targetCharacter K c)
      c.geometry (rayFilter K c) :=
  HeckeSkeleton.principalSource K c

example
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c) (hcubic : CubicSieveBound K c)
    (hreflection : MarkedCoefficientReflectionInput K (places K c)
      (probeData K c).arithmetic (HeckeSkeleton.finiteMellinData K c)
      (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))) :
    CanonicalInverseModelBounds (momentModels K c) :=
  HeckeSkeleton.canonical_inverse_models K c hcal hrows hprofiles
    hquadratic hcubic hreflection

example :
    ISource c.geometry (targetData K c) c.family.lamA :=
  HeckeSkeleton.inverseSource K c

example :
    TSource c.geometry (targetCharacter K c) (targetData K c)
      c.family.B c.family.lamA c.lamB :=
  HeckeSkeleton.sourceT K c

end FixedContext

example (K : Type) [Field K] [NumberField K]
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 12) (omega : HeckeCharacter K) :
    TIPInput K omega :=
  HeckeSkeleton.familyInputs K zeta hzeta omega

-- The complete endpoint type has no additional local-package premise.
-- Its unrelated pre-existing admissions remain recorded below.
example : GeneralHeckeSevenEighths :=
  @HeckeSkeleton.generalHeckeSevenEighths_skeleton

open Lean Elab Command in
run_cmd do
  for name in #[`HeckeSkeleton.completedMarkedEnergy,
      `HeckeSkeleton.principalSource,
      `HeckeSkeleton.canonical_inverse_models,
      `HeckeSkeleton.inverseSource,
      `HeckeSkeleton.sourceT,
      `HeckeSkeleton.familyInputs,
      `HeckeSkeleton.generalHeckeSevenEighths_skeleton] do
    let some info := (← getEnv).find? name
      | throwError "THETA_GLOBAL consumer {name} was not imported"
    logInfo m!"THETA_GLOBAL_CONSUMER_TYPE|{name}|{info.type}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains axiomName do
        throwError "THETA_GLOBAL consumer {name} depends on unexpected axiom {axiomName}"
    logInfo m!"THETA_GLOBAL_CONSUMER_AXIOMS|{name}|{String.intercalate "," (axioms.toList.map toString)}"
  logInfo "THETA_GLOBAL_CONSUMER_SCOPE|Compatibility only; legacy sorryAx is allowed."
