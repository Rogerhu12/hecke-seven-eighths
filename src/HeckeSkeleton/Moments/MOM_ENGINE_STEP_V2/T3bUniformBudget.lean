module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bFirstColumnBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bNumericalLedger

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The fixed exceptional numerical reserve

The scale schedule gives a step at most one. The original total
length then controls the scalar tilt, and the actual first divisor
window controls the first Poisson tilt. Together with the supported
volume, row and support errors, these losses fit inside thirty-two
copies of the chosen source loss, hence inside the original reserve.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep EngineInduction EngineInduction.Source
open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem step_le_one (c : TargetContext K) : recipeInductionSigma c ≤ 1 :=
  min_le_left _ _

theorem original_scalar_tilt_le (call : Call c) (p : SourceParameters c) :
    4 * p.tilt * (call.node.parameters.n₁ + call.node.parameters.n₂ +
      call.node.parameters.z) ≤ (8 + recipeInductionSigma c / 4) * p.loss := by
  have hA := call.t3b_totalLength_le
  change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤
    2 + recipeInductionSigma c / 16 at hA
  have hs : 0 ≤ 8 + recipeInductionSigma c / 4 := by
    have hstep := (recipeInduction_budget (c := c)).1
    positivity
  calc
    _ ≤ 4 * p.tilt * (2 + recipeInductionSigma c / 16) :=
      mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num) p.tilt_pos.le)
    _ = (8 + recipeInductionSigma c / 4) * p.tilt := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left p.tilt_le_loss hs

theorem original_scalar_tilt_rpow_le (call : Call c) (p : SourceParameters c) :
    call.base ^ (4 * p.tilt * (call.node.parameters.n₁ + call.node.parameters.n₂ +
      call.node.parameters.z)) ≤
      call.base ^ ((8 + recipeInductionSigma c / 4) * p.loss) :=
  Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (original_scalar_tilt_le call p)

def exceptionalErrorBound (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  5 * (4 * p.loss) / 6 + p.loss + (12 * p.loss) / 6 +
    (8 + recipeInductionSigma c / 4) * p.loss +
    (10 + recipeInductionSigma c / 4) * p.loss

theorem exceptionalErrorBound_nonneg : 0 ≤ exceptionalErrorBound c p := by
  have hstep := (recipeInduction_budget (c := c)).1
  have hloss := p.loss_pos
  unfold exceptionalErrorBound
  positivity

theorem exceptionalErrorBound_le_thirtyTwo :
    exceptionalErrorBound c p ≤ 32 * p.loss := by
  have hs := mul_le_mul_of_nonneg_right (step_le_one c) p.loss_pos.le
  have hp := p.loss_pos
  unfold exceptionalErrorBound
  nlinarith

theorem thirtyTwo_loss_le_reserve :
    32 * p.loss ≤ 4096 * ((c.geometry.slots : ℝ) + 1) * p.loss := by
  apply mul_le_mul_of_nonneg_right _ p.loss_pos.le
  have hk : 0 ≤ (c.geometry.slots : ℝ) := Nat.cast_nonneg _
  linarith

theorem exceptionalErrorBound_le_reserve :
    exceptionalErrorBound c p ≤ 4096 * ((c.geometry.slots : ℝ) + 1) * p.loss :=
  exceptionalErrorBound_le_thirtyTwo.trans thirtyTwo_loss_le_reserve

theorem exceptionalErrorBound_le_sourceReserve :
    exceptionalErrorBound c p ≤ sourceReserve c.family.lamA :=
  exceptionalErrorBound_le_reserve.trans p.loss_reserve

/-- The two actual tilt estimates enter the same original error sum. -/
theorem exceptional_errors_le_reserve (scalarTilt firstTilt : ℝ)
    (hscalar : scalarTilt ≤ (8 + recipeInductionSigma c / 4) * p.loss)
    (hfirst : firstTilt ≤ (10 + recipeInductionSigma c / 4) * p.loss) :
    5 * (4 * p.loss) / 6 + p.loss + (12 * p.loss) / 6 + scalarTilt + firstTilt ≤
      4096 * ((c.geometry.slots : ℝ) + 1) * p.loss := by
  apply le_trans (b := exceptionalErrorBound c p) ?_ exceptionalErrorBound_le_reserve
  unfold exceptionalErrorBound
  linarith

theorem exceptional_uniform_terminal_exponent (call : Call c) (p : SourceParameters c) :
    max (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z -
      (call.node.parameters.m + call.node.parameters.q)) 0 +
        3 * recipeInductionSigma c + exceptionalErrorBound c p ≤
      recipeInductionTerminalLoss c - p.loss - p.loss :=
  exceptional_exponent_with_index_reserve call p (exceptionalErrorBound c p)
    exceptionalErrorBound_le_reserve

theorem exceptional_actual_terminal_exponent (call : Call c) (p : SourceParameters c)
    (scalarTilt firstTilt : ℝ)
    (hscalar : scalarTilt ≤ (8 + recipeInductionSigma c / 4) * p.loss)
    (hfirst : firstTilt ≤ (10 + recipeInductionSigma c / 4) * p.loss) :
    max (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z -
      (call.node.parameters.m + call.node.parameters.q)) 0 +
        3 * recipeInductionSigma c +
        (5 * (4 * p.loss) / 6 + p.loss + (12 * p.loss) / 6 + scalarTilt + firstTilt) ≤
      recipeInductionTerminalLoss c - p.loss - p.loss :=
  exceptional_exponent_with_index_reserve call p _
    (exceptional_errors_le_reserve scalarTilt firstTilt hscalar hfirst)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exceptional_uniform_terminal_exponent
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exceptional_actual_terminal_exponent
