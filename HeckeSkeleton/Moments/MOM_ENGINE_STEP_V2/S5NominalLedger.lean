import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.GeometryContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Scalar consequences of the original S5 geometry

The width and slack follow from the original gcd and radical ledger,
before clipping, allocation or slot deletion. These helpers use no
blueprint task theorem.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

theorem nominal_width
    (G : OriginalNominalGeometry call.workingParameters call.base
      (recipeInductionSigma c)) :
    G.skeleton.nominalWidth ≤
      call.workingParameters.m + call.workingParameters.q - recipeInductionSigma c := by
  have hgap := G.enlargement_bound (recipeInduction_budget (c := c)).1.le
  have hunit := G.unit_length call.domain.scale
  rw [G.skeleton.width_identity, G.parentWidth]
  linarith

theorem nominal_slack
    (G : OriginalNominalGeometry call.workingParameters call.base
      (recipeInductionSigma c)) :
    G.tag.removedLength call.base + G.tag.poolLength (recipeInductionSigma c) ≤
      G.halfSecond - G.secondRadical + G.tag.removedLength call.base +
        G.boundary + G.tag.poolLength (recipeInductionSigma c) :=
  child_allowance_lower G.halfSecond G.secondRadical
    (G.tag.removedLength call.base) G.boundary
    (G.tag.poolLength (recipeInductionSigma c))
    (G.radical_length call.domain.scale) G.boundary_nonneg

theorem class_width
    {p : SourceParameters c} {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} {expansion : PoolExpansion family}
    {second : SecondFamily expansion} {key : SecondClassKey second}
    (G : ClassGeometry key) (side : Bool) :
    (G.nominal side).skeleton.nominalWidth ≤
      call.workingParameters.m + call.workingParameters.q - recipeInductionSigma c :=
  nominal_width (G.nominal side)

theorem class_slack
    {p : SourceParameters c} {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} {expansion : PoolExpansion family}
    {second : SecondFamily expansion} {key : SecondClassKey second}
    (G : ClassGeometry key) (side : Bool) :
    (G.nominal side).tag.removedLength call.base +
      (G.nominal side).tag.poolLength (recipeInductionSigma c) ≤ G.slack side :=
  nominal_slack (G.nominal side)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.nominal_width
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.nominal_slack
