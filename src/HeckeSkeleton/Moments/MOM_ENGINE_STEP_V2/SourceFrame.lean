module

public import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepHypothesis
public import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualEngineProfiles
public import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinUniversalLabels

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed choices and the original source request

The fixed frame precedes the backward profile schedule. The schedule
precedes the source profile coefficient and height degree. A source
request contains only the original scale, height, source index, literal
recursive node and its geometric domain. In particular it contains no
child estimate, kernel, terminal estimate or completed engine output.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

/-- The two genuine Fourier coordinates of the paired producer. -/
abbrev EngineParameter := WithLp 2 (ℝ × ℝ)

/-- The engine and ordinary-reflection parameters occupy separate summands. -/
abbrev CombinedParameter := RecipeMellinParameter EngineParameter

local instance sourceReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance sourceReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

structure SourceFrame where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_small : lower ≤ 1 / 2
  upper_large : 2 ≤ upper
  interval : lower < upper
  decay : ℝ
  decay_gt_one : 1 < decay
  reflection : ℕ → ℕ
  reflection_order : ∀ J, J ≤ reflection J ∧ 1 ≤ reflection J

/-- Only choices made before the source profile budget are stored here. -/
structure OrderSchedule where
  engine : ℕ → ℕ
  minimumCp : ℝ

/-- These constants precede every moving source, node and frequency. -/
structure UniformBounds where
  coefficient : ℝ
  heightDegree : ℝ
  threshold : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  heightDegree_nonneg : 0 ≤ heightDegree
  threshold_one_le : 1 ≤ threshold

def sourcePrimitive (c : TargetContext K) (frame : SourceFrame)
    (schedule : OrderSchedule) (Cp Hp U T : ℝ) :
    MomentData K c.family.omega (targetCharacter K c) →
      PairedInvariantParameters → Prop :=
  recipeDataReflectionPrimitive c (recipeThetaFamily (expansionRecipeRaw K c))
    (actualCompleteSourceBudgetPrimitive c) 1 schedule.engine frame.reflection
    (recipeInductionSigma c) (recipeInductionSigma c / 16)
    frame.decay Cp Hp frame.lower frame.upper U T

def sourceSystem (c : TargetContext K) (frame : SourceFrame)
    (schedule : OrderSchedule) (Cp Hp U T : ℝ) :
    PolynomialSystem.{0} K c.family.omega (targetCharacter K c)
      (recipeInductionSigma c) 2 :=
  recipeDataReflectionSystem c (recipeThetaFamily (expansionRecipeRaw K c))
    (actualCompleteSourceBudgetPrimitive c) 1 schedule.engine frame.reflection
    frame.decay Cp Hp frame.lower frame.upper U T

structure SourceRequest (c : TargetContext K) (frame : SourceFrame)
    (schedule : OrderSchedule) (Cp Hp : ℝ) (bounds : UniformBounds) where
  scale : ℝ
  large : bounds.threshold ≤ scale
  height : ℝ
  height_nonneg : 0 ≤ height
  index : SourceMomentIndexFor K c
    (recipeMomentSourceData K c (expansionRecipeRaw K c)) scale height
  node : (sourceSystem c frame schedule Cp Hp (momentBaseFor index) height).Label
  domain : EngineStep.PairedEngineDomain
    ((sourceSystem c frame schedule Cp Hp (momentBaseFor index) height).node node).centered
    ((sourceSystem c frame schedule Cp Hp (momentBaseFor index) height).node node).data
    ((sourceSystem c frame schedule Cp Hp (momentBaseFor index) height).node node).parameters
    (momentBaseFor index)
    (momentBaseFor index ^
      ((sourceSystem c frame schedule Cp Hp (momentBaseFor index) height).node node).comparison₁)
    (momentBaseFor index ^
      ((sourceSystem c frame schedule Cp Hp (momentBaseFor index) height).node node).comparison₂)
    (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)

namespace SourceRequest

variable {c : TargetContext K} {frame : SourceFrame} {schedule : OrderSchedule}
variable {Cp Hp : ℝ} {bounds : UniformBounds}

def base (request : SourceRequest c frame schedule Cp Hp bounds) : ℝ :=
  momentBaseFor request.index

def parent (request : SourceRequest c frame schedule Cp Hp bounds) :
    Node K c.family.omega (targetCharacter K c) :=
  (sourceSystem c frame schedule Cp Hp request.base request.height).node request.node

def primitive (request : SourceRequest c frame schedule Cp Hp bounds) :
    MomentData K c.family.omega (targetCharacter K c) →
      PairedInvariantParameters → Prop :=
  sourcePrimitive c frame schedule Cp Hp request.base request.height

/-- The original complete recipe and both actual arithmetic budgets are
recovered from the node's existing invariant before any transform. -/
def sourceData (request : SourceRequest c frame schedule Cp Hp bounds) :
    CompleteSourceBudgetData c
      (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
      request.base request.parent.data (pairedInvariantParameters request.parent.parameters) :=
  Classical.choice request.node.down.property.admissible.2.1

theorem fitsMesh (request : SourceRequest c frame schedule Cp Hp bounds) :
    request.parent.data.geometry.fitsMesh (momentMesh K c.family).val :=
  request.node.down.property.admissible.2.2.1

theorem kappa (request : SourceRequest c frame schedule Cp Hp bounds) :
    request.parent.parameters.κ = 2 * c.family.B - 1 :=
  request.node.down.property.admissible.1

end SourceRequest
end HeckeSkeleton.Moments.EngineStepV2
