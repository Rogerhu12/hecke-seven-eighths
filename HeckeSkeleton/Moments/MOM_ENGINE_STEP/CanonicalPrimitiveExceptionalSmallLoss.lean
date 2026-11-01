import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalGeometry

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

theorem outerLoss_pos (b : Box) : 0 < outerLoss b :=
  div_pos b.ε_pos (by norm_num)

theorem volumeLoss_pos (b : Box) : 0 < volumeLoss b :=
  div_pos b.ε_pos (by norm_num)

theorem outerLoss_half (b : Box) : outerLoss b / 2 = b.ε / 8 := by
  unfold outerLoss
  ring

theorem volumeLoss_eq (b : Box) : volumeLoss b = outerLoss b / 16 := by
  unfold volumeLoss outerLoss
  ring

theorem volume_le (b : Box) : volumeLoss b ≤ outerLoss b / 16 :=
  (volumeLoss_eq b).le

theorem support_le (b : Box) : 3 * b.loss ≤ outerLoss b / 16 := by
  have hl := b.loss_le_ε
  have hε := b.ε_pos
  unfold outerLoss
  linarith

theorem cutoffLoss_nonneg (b : Box) : 0 ≤ cutoffLoss b :=
  CanonicalLiteralExceptionalGeometry.paidCutoff_nonneg
    b.loss_pos.le b.loss_pos.le le_rfl

theorem cutoffLoss_eq (b : Box) : cutoffLoss b = 3 * b.loss := by
  unfold cutoffLoss CanonicalLiteralExceptionalGeometry.paidCutoff
  ring

theorem cutoff_le (b : Box) : cutoffLoss b / 6 ≤ outerLoss b / 16 := by
  have hl := b.loss_le_ε
  have hε := b.ε_pos
  rw [cutoffLoss_eq]
  unfold outerLoss
  linarith

/-- The original cap pays the real removed occurrences, including an
empty removed set. The sum itself is never replaced in the source. -/
theorem removed_le_cap_budget (b : Box) {ι : Type*} (removed : Finset ι)
    (hcard : removed.card ≤ b.cap) :
    (∑ _i ∈ removed, b.loss) ≤ b.ε / 4096 := by
  have hc : (removed.card : ℝ) ≤ (b.cap : ℝ) := by exact_mod_cast hcard
  calc
    (∑ _i ∈ removed, b.loss) = (removed.card : ℝ) * b.loss := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (b.cap : ℝ) * b.loss := mul_le_mul_of_nonneg_right hc b.loss_pos.le
    _ ≤ b.ε / 4096 := b.cap_mul_loss_le_ε

theorem removed_le (b : Box) {ι : Type*} (removed : Finset ι)
    (hcard : removed.card ≤ b.cap) :
    (∑ _i ∈ removed, b.loss) ≤ outerLoss b / 16 := by
  apply (removed_le_cap_budget b removed hcard).trans
  unfold outerLoss
  linarith [b.ε_pos]

/-- The literal complement of the retained slots has the same bound. -/
theorem removed_complement_le (b : Box) {k : ℕ} (keep : Finset (Fin k))
    (hcap : k ≤ b.cap) :
    (∑ _i ∈ Finset.univ \ keep, b.loss) ≤ outerLoss b / 16 := by
  apply removed_le b (Finset.univ \ keep)
  exact (Finset.card_le_univ _).trans
    (by simpa only [Fintype.card_fin] using hcap)

/-- These are exactly the four small-loss premises of the original
centered exceptional remainder, for either source orientation. -/
theorem centered_conditions (b : Box) {ι : Type*} (removed : Finset ι)
    (hcard : removed.card ≤ b.cap) :
    3 * b.loss ≤ outerLoss b / 16 ∧
      volumeLoss b ≤ outerLoss b / 16 ∧
      (∑ _i ∈ removed, b.loss) ≤ outerLoss b / 16 ∧
      cutoffLoss b / 6 ≤ outerLoss b / 16 :=
  ⟨support_le b, volume_le b, removed_le b removed hcard, cutoff_le b⟩

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.support_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.cutoff_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.removed_le_cap_budget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.removed_complement_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalSmallLoss.centered_conditions
