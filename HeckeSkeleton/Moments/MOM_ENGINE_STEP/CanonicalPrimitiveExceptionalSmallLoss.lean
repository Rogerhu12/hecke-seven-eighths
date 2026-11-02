import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalGeometry

set_option linter.unusedSectionVars false

/-!
# Fixed small losses for the original exceptional source

The requested outer loss and the volume loss are fixed before any
source or allocation. The support and physical cutoff use the actual
choices in the primitive engine. The slot payment is a sum over the
actual removed set; its cardinality is only used to bound that sum.

The four estimates below have the order required by
`centered_small_loss_bound`: support, volume, removed slots and one
sixth of the paid physical cutoff. No source estimate is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss

open CanonicalPrimitiveEngineChoices

def outerLoss (b : Box) : ℝ := b.ε / 4

def volumeLoss (b : Box) : ℝ := b.ε / 64

/-- This retains both original column losses and the actual cutoff. -/
def cutoffLoss (b : Box) : ℝ :=
  CanonicalLiteralExceptionalGeometry.paidCutoff b.loss b.loss 0

theorem outerLoss_pos (b : Box) : 0 < outerLoss b := by
  sorry

theorem volumeLoss_pos (b : Box) : 0 < volumeLoss b := by
  sorry

theorem outerLoss_half (b : Box) : outerLoss b / 2 = b.ε / 8 := by
  sorry

theorem volumeLoss_eq (b : Box) : volumeLoss b = outerLoss b / 16 := by
  sorry

theorem volume_le (b : Box) : volumeLoss b ≤ outerLoss b / 16 := by
  sorry

theorem support_le (b : Box) : 3 * b.loss ≤ outerLoss b / 16 := by
  sorry

theorem cutoffLoss_nonneg (b : Box) : 0 ≤ cutoffLoss b := by
  sorry

theorem cutoffLoss_eq (b : Box) : cutoffLoss b = 3 * b.loss := by
  sorry

theorem cutoff_le (b : Box) : cutoffLoss b / 6 ≤ outerLoss b / 16 := by
  sorry

/-- The original cap pays the real removed occurrences, including an
empty removed set. The sum itself is never replaced in the source. -/
theorem removed_le_cap_budget (b : Box) {ι : Type*} (removed : Finset ι)
    (hcard : removed.card ≤ b.cap) :
    (∑ _i ∈ removed, b.loss) ≤ b.ε / 4096 := by
  sorry

theorem removed_le (b : Box) {ι : Type*} (removed : Finset ι)
    (hcard : removed.card ≤ b.cap) :
    (∑ _i ∈ removed, b.loss) ≤ outerLoss b / 16 := by
  sorry

/-- The literal complement of the retained slots has the same bound. -/
theorem removed_complement_le (b : Box) {k : ℕ} (keep : Finset (Fin k))
    (hcap : k ≤ b.cap) :
    (∑ _i ∈ Finset.univ \ keep, b.loss) ≤ outerLoss b / 16 := by
  sorry

/-- These are exactly the four small-loss premises of the original
centered exceptional remainder, for either source orientation. -/
theorem centered_conditions (b : Box) {ι : Type*} (removed : Finset ι)
    (hcard : removed.card ≤ b.cap) :
    3 * b.loss ≤ outerLoss b / 16 ∧
      volumeLoss b ≤ outerLoss b / 16 ∧
      (∑ _i ∈ removed, b.loss) ≤ outerLoss b / 16 ∧
      cutoffLoss b / 6 ≤ outerLoss b / 16 := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.support_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.cutoff_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.removed_le_cap_budget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.removed_complement_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.centered_conditions
