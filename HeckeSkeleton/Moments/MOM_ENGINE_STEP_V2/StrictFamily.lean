import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LocalProduction
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ParameterTransport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The concrete paired output enters the original Mellin family

The actual finite output is produced by `selectedOutput`. Its same
positive kernels are pushed into the engine summand of the induction
parameter space. The original universal-node constructor labels these
same children from their proved invariant and strict geometry. The
outer Mellin coefficient is paid by the independent scalar budget.
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

local instance strictReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance strictReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

/-- The genuine Fourier output keeps both children, all four terminals
and its total mass when included in the common parameter space. -/
def parameterOutput (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    ((selectedCall request).model frequency).EngineOutput (Ω := CombinedParameter)
      request.base (recipeInductionSigma c) (recipeInductionEdgeLoss c)
      (recipeInductionTerminalLoss c) (selectedCall request).engineCoefficient
      (selectedCall request).engineControl (admissibleOfInvariant request.primitive) :=
  (selectedOutput request frequency).toConclusion.mapParameter
    (Sum.inl : EngineParameter → CombinedParameter)
    measurableEmbedding_parameterInl
    (parameterInlRetraction (0 : EngineParameter))
    (parameterInlRetraction_leftInverse (0 : EngineParameter))

/-- Actual smaller children receive labels in the exact source system,
using its original kappa, mesh, arithmetic and ranked profile invariant. -/
def strictBranch (request : Request c frame Cp Hp hCp hminimum hHp) :
    MellinStrictBranchAt (Ω := CombinedParameter)
      (sourceSystem c frame (selectedSchedule c frame) Cp Hp request.base request.height)
      request.node request.base request.height
      (selectedBounds c frame Cp Hp hCp hminimum hHp).coefficient
      (selectedBounds c frame Cp Hp hCp hminimum hHp).heightDegree
      (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c)
      (admissibleOfInvariant request.primitive) where
  cap := (selectedCall request).cap
  order := (selectedCall request).order
  weight := (selectedCall request).weight
  lower := (selectedCall request).lower
  upper := (selectedCall request).upper
  weight_nonneg := (selectedCall request).weight_nonneg
  lower_pos := (selectedCall request).lower_pos
  interval := (selectedCall request).interval
  profileBudget := (selectedCall request).profileBudget
  profileBudget_one_le := (selectedCall request).profileBudget_one_le
  slot_cap := (selectedCall request).slot_cap
  profiles := (selectedCall request).profiles
  engineCoefficient := (selectedCall request).engineCoefficient
  engineControl := (selectedCall request).engineControl
  outputs frequency := universalLabeledEngineOutput request.primitive
    (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    c.geometry.slots (recipeInduction_budget (c := c)).1
    ((selectedCall request).model frequency) request.base
    (recipeInductionEdgeLoss c) (recipeInductionTerminalLoss c)
    (selectedCall request).engineCoefficient (selectedCall request).engineControl
    request.node.down.property.kappa_lower request.node.down.property.kappa_upper
    request.node.down.property.width_le request.node.down.property.slot_count
    (parameterOutput request frequency)
  budget := selectedCall_budget request

/-- The uniform family uses the exact original quantifier order. -/
def selectedStrictFamily (c : TargetContext K) (frame : SourceFrame) (Cp Hp : ℝ)
    (hCp : 0 < Cp) (hminimum : (selectedSchedule c frame).minimumCp ≤ Cp)
    (hHp : 0 ≤ Hp) :
    RecipeMellinStrictFamily EngineParameter (expansionRecipeRaw K c)
      (actualCompleteSourceBudgetPrimitive c) 1 (selectedSchedule c frame).engine
      frame.reflection frame.decay Cp Hp frame.lower frame.upper where
  coefficient := (selectedBounds c frame Cp Hp hCp hminimum hHp).coefficient
  heightDegree := (selectedBounds c frame Cp Hp hCp hminimum hHp).heightDegree
  threshold := (selectedBounds c frame Cp Hp hCp hminimum hHp).threshold
  coefficient_nonneg := (selectedBounds c frame Cp Hp hCp hminimum hHp).coefficient_nonneg
  heightDegree_nonneg := (selectedBounds c frame Cp Hp hCp hminimum hHp).heightDegree_nonneg
  outputs := by
    intro Z hZ T hT i x domain
    exact ⟨strictBranch {
      scale := Z
      large := hZ
      height := T
      height_nonneg := hT
      index := i
      node := x
      domain := domain }⟩

end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.parameterOutput
#print axioms HeckeSkeleton.Moments.EngineStepV2.selectedStrictFamily
