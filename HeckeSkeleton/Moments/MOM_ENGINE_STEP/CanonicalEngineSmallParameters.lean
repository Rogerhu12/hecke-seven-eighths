import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCombinedMassCoefficient
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSharpSecondZeroLedger
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

set_option linter.unusedSectionVars false

/-!
# Fixed small parameters for the unified original engine

All choices below precede the moving scale, source, profiles and prime
pool. The same loss controls both annuli and both cutoff exponents.
Both logarithmic tilts are fixed before the Fourier seminorm orders.
The prime analytic contour is selected later from the already fixed
orders, as in the existing full-kappa radius theorem.

These elementary choices pay the actual sharp second-zero ledger,
the strict child-width margin, the pool mesh separation and its one
density loss. They contain no source or terminal estimate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters

/-- One small boundary budget for annuli, cutoffs, clipping and mesh. -/
def boundary (step ε : ℝ) : ℝ :=
  min (1 : ℝ) (min (step / 64) (ε / 4096))

/-- This is also the fixed tilt used by the original combined mass
coefficient, with a reserved fraction of the final power loss. -/
def tilt (lengthBound ε : ℝ) : ℝ :=
  CanonicalLiteralCombinedMassCoefficient.mellinTilt lengthBound (ε / 16)

/-- The first physical endpoint includes two original annulus losses
and one original common cutoff. -/
def supportError (step ε : ℝ) : ℝ := 3 * boundary step ε

def tailSaving (lengthBound : ℝ) : ℝ := 2 * lengthBound + 1

theorem boundary_pos {step ε : ℝ} (hstep : 0 < step) (hε : 0 < ε) :
    0 < boundary step ε := by
  sorry

theorem boundary_le_one (step ε : ℝ) : boundary step ε ≤ 1 := by
  sorry

theorem boundary_le_step (step ε : ℝ) : boundary step ε ≤ step / 64 := by
  sorry

theorem boundary_le_loss (step ε : ℝ) : boundary step ε ≤ ε / 4096 := by
  sorry

theorem boundary_width_margin {step ε : ℝ} (hstep : 0 < step) (hε : 0 < ε) :
    0 ≤ supportError step ε ∧ 2 * supportError step ε ≤ step := by
  sorry

/-- A positive-slot pool has length step/3, while every live slot fits
strictly below half that length. The zero-slot factory uses no pool. -/
theorem boundary_pool_separation {step ε : ℝ} (hstep : 0 < step) (hε : 0 < ε) :
    0 < boundary step ε ∧ boundary step ε < step / 6 ∧
      boundary step ε < step / 3 := by
  sorry

/-- The selected clipping and mesh budgets fit the existing aggregate
ordinary-kernel error ledger with room for the separate label sums. -/
theorem boundary_mass_errors {step ε : ℝ} (hstep : 0 < step) (hε : 0 < ε) :
    boundary step ε ≤ 3 * ε / 40 ∧ boundary step ε ≤ ε / 8 := by
  sorry

theorem tilt_properties {lengthBound ε : ℝ}
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε) :
    0 < tilt lengthBound ε ∧ tilt lengthBound ε ≤ 1 / 4 ∧
      tilt lengthBound ε + tilt lengthBound ε ≤ 1 / 2 := by
  sorry

theorem tilt_linear_budget {lengthBound ε : ℝ}
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε) :
    (6 * lengthBound + 4) * tilt lengthBound ε ≤ ε / 32 := by
  sorry

/-- The actual second-zero small powers, the one pool-density loss,
and the complete original-label cost fit inside one quarter of the
requested power loss. The principal padding+5step/3 is unchanged. -/
theorem second_zero_small_budget {step ε lengthBound : ℝ}
    (hstep : 0 < step) (hε : 0 < ε) (hbound : 0 ≤ lengthBound) :
    supportError step ε + 2 * boundary step ε +
        (4 * lengthBound + 2) * tilt lengthBound ε +
        2 * (lengthBound + 1) * tilt lengthBound ε +
        boundary step ε + ε / 8 ≤ ε / 4 := by
  sorry

theorem tailSaving_properties {lengthBound : ℝ} (hbound : 0 ≤ lengthBound) :
    0 < tailSaving lengthBound ∧ 2 * lengthBound ≤ tailSaving lengthBound := by
  sorry

/-- The same requested small cutoff can pay any earlier fixed
polynomial degree by choosing its rapid-decay order before moving data. -/
theorem exists_decay (degree lengthBound step ε : ℝ)
    (hstep : 0 < step) (hε : 0 < ε) :
    ∃ decay : ℝ, 1 < decay ∧
      firstTailCutoffExponent degree (tailSaving lengthBound) decay ≤ boundary step ε := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.boundary_width_margin
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.boundary_pool_separation
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.tilt_properties
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.second_zero_small_budget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.exists_decay
