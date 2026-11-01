import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCombinedMassCoefficient
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSharpSecondZeroLedger
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

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
    0 < boundary step ε :=
  lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem boundary_le_one (step ε : ℝ) : boundary step ε ≤ 1 := min_le_left _ _

theorem boundary_le_step (step ε : ℝ) : boundary step ε ≤ step / 64 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem boundary_le_loss (step ε : ℝ) : boundary step ε ≤ ε / 4096 :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem boundary_width_margin {step ε : ℝ} (hstep : 0 < step) (hε : 0 < ε) :
    0 ≤ supportError step ε ∧ 2 * supportError step ε ≤ step := by
  have hpos := (boundary_pos hstep hε).le
  have hsmall := boundary_le_step step ε
  unfold supportError
  constructor <;> linarith

/-- A positive-slot pool has length step/3, while every live slot fits
strictly below half that length. The zero-slot factory uses no pool. -/
theorem boundary_pool_separation {step ε : ℝ} (hstep : 0 < step) (hε : 0 < ε) :
    0 < boundary step ε ∧ boundary step ε < step / 6 ∧
      boundary step ε < step / 3 := by
  have h := boundary_le_step step ε
  exact ⟨boundary_pos hstep hε, by linarith, by linarith⟩

/-- The selected clipping and mesh budgets fit the existing aggregate
ordinary-kernel error ledger with room for the separate label sums. -/
theorem boundary_mass_errors {step ε : ℝ} (hstep : 0 < step) (hε : 0 < ε) :
    boundary step ε ≤ 3 * ε / 40 ∧ boundary step ε ≤ ε / 8 := by
  have h := boundary_le_loss step ε
  constructor <;> linarith

theorem tilt_properties {lengthBound ε : ℝ}
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε) :
    0 < tilt lengthBound ε ∧ tilt lengthBound ε ≤ 1 / 4 ∧
      tilt lengthBound ε + tilt lengthBound ε ≤ 1 / 2 := by
  have h := CanonicalLiteralCombinedMassCoefficient.mellinTilt_properties
    hbound (show 0 < ε / 16 by positivity)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem tilt_linear_budget {lengthBound ε : ℝ}
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε) :
    (6 * lengthBound + 4) * tilt lengthBound ε ≤ ε / 32 := by
  have hpos := (tilt_properties hbound hε).1.le
  have hden : 0 < 16 * (lengthBound + 1) := by positivity
  have hsmall : tilt lengthBound ε * (16 * (lengthBound + 1)) ≤ ε / 16 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  nlinarith [mul_nonneg hbound hpos]

/-- The actual second-zero small powers, the one pool-density loss,
and the complete original-label cost fit inside one quarter of the
requested power loss. The principal padding+5step/3 is unchanged. -/
theorem second_zero_small_budget {step ε lengthBound : ℝ}
    (hstep : 0 < step) (hε : 0 < ε) (hbound : 0 ≤ lengthBound) :
    supportError step ε + 2 * boundary step ε +
        (4 * lengthBound + 2) * tilt lengthBound ε +
        2 * (lengthBound + 1) * tilt lengthBound ε +
        boundary step ε + ε / 8 ≤ ε / 4 := by
  have hsmall := boundary_le_loss step ε
  have htilt := tilt_linear_budget hbound hε
  unfold supportError
  nlinarith

theorem tailSaving_properties {lengthBound : ℝ} (hbound : 0 ≤ lengthBound) :
    0 < tailSaving lengthBound ∧ 2 * lengthBound ≤ tailSaving lengthBound := by
  unfold tailSaving
  constructor <;> linarith

/-- The same requested small cutoff can pay any earlier fixed
polynomial degree by choosing its rapid-decay order before moving data. -/
theorem exists_decay (degree lengthBound step ε : ℝ)
    (hstep : 0 < step) (hε : 0 < ε) :
    ∃ decay : ℝ, 1 < decay ∧
      firstTailCutoffExponent degree (tailSaving lengthBound) decay ≤ boundary step ε := by
  refine ⟨tailDecayForWidth degree (tailSaving lengthBound) (boundary step ε), ?_, ?_⟩
  · exact tailDecayForWidth_gt_one degree (tailSaving lengthBound) (boundary step ε)
      (boundary_pos hstep hε)
  · exact firstTailCutoffExponent_le_width degree (tailSaving lengthBound)
      (boundary step ε) degree (boundary_pos hstep hε) le_rfl

end HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.boundary_width_margin
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.boundary_pool_separation
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.tilt_properties
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.second_zero_small_budget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEngineSmallParameters.exists_decay
