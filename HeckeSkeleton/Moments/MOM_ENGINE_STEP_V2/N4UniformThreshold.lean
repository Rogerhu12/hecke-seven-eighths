import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.InputDemands
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: one fixed threshold pays the original annulus power

The maximal upper endpoint covers every rank of the fixed frame. Its
threshold depends only on this frame, the target slot cap and the
previously fixed positive source loss. The actual call supplies only
its existing Regular profile input and the concrete UniformDemand
readiness inequality. No threshold is chosen after the source or its
nonzero column is known.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

def annulusRankBound (c : TargetContext K) : ℕ :=
  6 * (widthBand (recipeInductionSigma c) 2 + 1)

/-- Mellin's upper-endpoint enlargement, at the largest scheduled
annulus. The maximum also covers the base capacity's unit annulus. -/
def uniformAnnulus (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 1 (2 * (frame.upper * (2 : ℝ) ^ annulusRankBound c))

theorem uniformAnnulus_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ uniformAnnulus c frame := le_max_left _ _

/-- An explicit numerical threshold, selected before every call. -/
def annulusDemand {c : TargetContext K} (p : SourceParameters c)
    (frame : SourceFrame) : UniformDemand where
  orders := ∅
  threshold := max 1
    (uniformAnnulus c frame ^ (((2 * c.geometry.slots : ℕ) : ℝ) / p.loss))
  threshold_one_le := le_max_left _ _

theorem fixed_annulus_power_le {c : TargetContext K} (p : SourceParameters c)
    (frame : SourceFrame) {Z : ℝ} (hZ : (annulusDemand p frame).threshold ≤ Z) :
    uniformAnnulus c frame ^ (2 * c.geometry.slots) ≤ Z ^ p.loss := by
  have hA : 0 ≤ uniformAnnulus c frame :=
    zero_le_one.trans (uniformAnnulus_one_le c frame)
  have hthreshold :
      uniformAnnulus c frame ^ (((2 * c.geometry.slots : ℕ) : ℝ) / p.loss) ≤ Z :=
    (le_max_right _ _).trans hZ
  calc
    _ = (uniformAnnulus c frame ^
        (((2 * c.geometry.slots : ℕ) : ℝ) / p.loss)) ^ p.loss := by
      rw [← Real.rpow_mul hA, div_mul_cancel₀ _ p.loss_pos.ne', Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hA _) hthreshold p.loss_pos.le

variable {c : TargetContext K} {call : Call c}

/-- Natural subtraction bounds every rank, without requiring a new
rank condition on the moving call. -/
theorem prepared_upper_le (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) :
    call.prepared.upper ≤ frame.upper * (2 : ℝ) ^ annulusRankBound c := by
  rw [input.regular.upper, hframe]
  change frame.upper * (2 : ℝ) ^ (annulusRankBound c - call.rank) ≤ _
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.sub_le (annulusRankBound c) call.rank))
    (by linarith [frame.upper_large])

theorem call_annulus_le (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) :
    max 1 (2 * call.prepared.upper) ≤ uniformAnnulus c frame := by
  apply max_le (uniformAnnulus_one_le c frame)
  exact (mul_le_mul_of_nonneg_left (prepared_upper_le frame input hframe)
    (by norm_num : (0 : ℝ) ≤ 2)).trans (le_max_right _ _)

/-- The actual source may now spend exactly p.loss on all original
annulus factors. Its nonzero-column argument is separate from this
uniform numerical preparation. -/
theorem uniform_annulus_power_le (p : SourceParameters c) (frame : SourceFrame)
    (input : ProfileInput call) (hframe : call.frame = frame)
    (ready : (annulusDemand p frame).Ready call input) :
    (max 1 (2 * call.prepared.upper)) ^ (2 * c.geometry.slots) ≤ call.base ^ p.loss :=
  (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
    (call_annulus_le frame input hframe) _).trans
      (fixed_annulus_power_le p frame ready.large)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.fixed_annulus_power_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.uniform_annulus_power_le
