import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CallData
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ParameterTransport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Assembly on the unchanged induction interfaces

This module receives actual frequency outputs and their outer Mellin
budget explicitly. It imports no unfinished blueprint task. The same
children and positive kernels enter the existing universal node labels.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

local instance reflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance reflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

variable {c : TargetContext K} {frame : SourceFrame} {schedule : OrderSchedule}
variable {Cp Hp : ℝ} {bounds : UniformBounds}

/-- Include the genuine Fourier parameters in the engine summand without
changing either child, any terminal term, or total kernel mass. -/
def parameterOutput (request : SourceRequest c frame schedule Cp Hp bounds)
    (call : PreparedCall request.parent)
    (outputs : ∀ frequency : ℝ × ℝ,
      (call.model frequency).EngineOutput (Ω := EngineParameter)
        request.base (recipeInductionSigma c) (recipeInductionEdgeLoss c)
        (recipeInductionTerminalLoss c) call.engineCoefficient call.engineControl
        (admissibleOfInvariant request.primitive))
    (frequency : ℝ × ℝ) :
    (call.model frequency).EngineOutput (Ω := CombinedParameter)
      request.base (recipeInductionSigma c) (recipeInductionEdgeLoss c)
      (recipeInductionTerminalLoss c) call.engineCoefficient call.engineControl
      (admissibleOfInvariant request.primitive) :=
  (outputs frequency).mapParameter
    (Sum.inl : EngineParameter → CombinedParameter)
    measurableEmbedding_parameterInl
    (parameterInlRetraction (0 : EngineParameter))
    (parameterInlRetraction_leftInverse (0 : EngineParameter))

/-- The original source invariant supplies the geometric node bounds.
Every child is labeled from its own exact invariant certificate. -/
def strictBranch (request : SourceRequest c frame schedule Cp Hp bounds)
    (call : PreparedCall request.parent)
    (outputs : ∀ frequency : ℝ × ℝ,
      (call.model frequency).EngineOutput (Ω := EngineParameter)
        request.base (recipeInductionSigma c) (recipeInductionEdgeLoss c)
        (recipeInductionTerminalLoss c) call.engineCoefficient call.engineControl
        (admissibleOfInvariant request.primitive))
    (budget : call.mellinCost ≤
      bounds.coefficient * (1 + request.height) ^ bounds.heightDegree) :
    MellinStrictBranchAt (Ω := CombinedParameter)
      (sourceSystem c frame schedule Cp Hp request.base request.height)
      request.node request.base request.height bounds.coefficient bounds.heightDegree
      (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c)
      (admissibleOfInvariant request.primitive) where
  cap := call.cap
  order := call.order
  weight := call.weight
  lower := call.lower
  upper := call.upper
  weight_nonneg := call.weight_nonneg
  lower_pos := call.lower_pos
  interval := call.interval
  profileBudget := call.profileBudget
  profileBudget_one_le := call.profileBudget_one_le
  slot_cap := call.slot_cap
  profiles := call.profiles
  engineCoefficient := call.engineCoefficient
  engineControl := call.engineControl
  outputs frequency := universalLabeledEngineOutput request.primitive
    (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    c.geometry.slots (recipeInduction_budget (c := c)).1
    (call.model frequency) request.base
    (recipeInductionEdgeLoss c) (recipeInductionTerminalLoss c)
    call.engineCoefficient call.engineControl
    request.node.down.property.kappa_lower request.node.down.property.kappa_upper
    request.node.down.property.width_le request.node.down.property.slot_count
    (parameterOutput request call outputs frequency)
  budget := budget

/-- Package all actual calls only after the uniform bounds are fixed. -/
def strictFamily (c : TargetContext K) (frame : SourceFrame) (schedule : OrderSchedule)
    (Cp Hp : ℝ) (bounds : UniformBounds)
    (produce : ∀ request : SourceRequest c frame schedule Cp Hp bounds,
      Nonempty (MellinStrictBranchAt (Ω := CombinedParameter)
        (sourceSystem c frame schedule Cp Hp request.base request.height)
        request.node request.base request.height bounds.coefficient bounds.heightDegree
        (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c)
        (admissibleOfInvariant request.primitive))) :
    RecipeMellinStrictFamily EngineParameter (expansionRecipeRaw K c)
      (actualCompleteSourceBudgetPrimitive c) 1 schedule.engine
      frame.reflection frame.decay Cp Hp frame.lower frame.upper where
  coefficient := bounds.coefficient
  heightDegree := bounds.heightDegree
  threshold := bounds.threshold
  coefficient_nonneg := bounds.coefficient_nonneg
  heightDegree_nonneg := bounds.heightDegree_nonneg
  outputs := by
    intro Z hZ T hT i x domain
    exact produce {
      scale := Z
      large := hZ
      height := T
      height_nonneg := hT
      index := i
      node := x
      domain := domain }

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.parameterOutput
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.strictBranch
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.strictFamily
