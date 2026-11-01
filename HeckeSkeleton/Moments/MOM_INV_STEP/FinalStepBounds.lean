import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The final numerical allocations in the actual inverse step

One eighth of the prescribed loss is used for each independent cost.
The first center count is included before the production exponent is
compared with the public exponent. The actual principal and rapid-tail
errors retain their separate powers. These are numerical comparisons;
no arithmetic or parent-energy statement is a premise.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FinalStepBounds

theorem production_exponent_le (F eta tau pi eps : ℝ) (hpi : 0 ≤ pi) :
    (F + 40 * eta + tau + 6 * (pi / 8) + eps) + pi / 8 ≤
      F + 40 * eta + tau + pi + eps := by linarith

theorem production_power_le (Z F eta tau pi eps : ℝ)
    (hZ : 1 ≤ Z) (hpi : 0 ≤ pi) :
    Z ^ (pi / 8) * Z ^ (F + 40 * eta + tau + 6 * (pi / 8) + eps) ≤
      Z ^ (F + 40 * eta + tau + pi + eps) := by
  rw [← Real.rpow_add (zero_lt_one.trans_le hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by
    have hp := production_exponent_le F eta tau pi eps hpi
    linarith)

theorem error_exponent_le (F h eta tau pi eps : ℝ)
    (hh : 0 ≤ h) (hmesh : h ≤ eta / 32) (hpi : 0 ≤ pi) (heps : 0 ≤ eps) :
    F + 26 * h + tau + 3 * (pi / 8) ≤
      F + 40 * eta + tau + pi + eps := by linarith

theorem error_tail_exponent_le (F h eta tau pi eps saving : ℝ)
    (hh : 0 ≤ h) (hmesh : h ≤ eta / 32) (hpi : 0 ≤ pi) (heps : 0 ≤ eps)
    (hsaving : 0 ≤ saving) :
    F + 26 * h + tau + 3 * (pi / 8) - saving ≤
      F + 40 * eta + tau + pi + eps := by
  have hb := error_exponent_le F h eta tau pi eps hh hmesh hpi heps
  linarith

theorem error_powers_le (Z F h eta tau pi eps saving : ℝ)
    (hZ : 1 ≤ Z) (hh : 0 ≤ h) (hmesh : h ≤ eta / 32)
    (hpi : 0 ≤ pi) (heps : 0 ≤ eps) (hsaving : 0 ≤ saving) :
    Z ^ (F + 26 * h + tau + 3 * (pi / 8)) +
      Z ^ (F + 26 * h + tau + 3 * (pi / 8) - saving) ≤
      2 * Z ^ (F + 40 * eta + tau + pi + eps) := by
  have hp := Real.rpow_le_rpow_of_exponent_le hZ
    (error_exponent_le F h eta tau pi eps hh hmesh hpi heps)
  have ht := Real.rpow_le_rpow_of_exponent_le hZ
    (error_tail_exponent_le F h eta tau pi eps saving hh hmesh hpi heps hsaving)
  linarith

theorem parent_error_exponent_le (M h pi : ℝ) (hpi : 0 ≤ pi) :
    M + 5 * h + pi / 8 ≤ M + 5 * h + pi := by linarith

theorem parent_tail_exponent_le (M h pi saving : ℝ)
    (hM : 0 ≤ M) (hh : 0 ≤ h) (hpi : 0 ≤ pi) (hsaving : 0 ≤ saving) :
    -saving ≤ M + 5 * h + pi := by linarith

theorem parent_error_powers_le (Z M h pi saving : ℝ)
    (hZ : 1 ≤ Z) (hM : 0 ≤ M) (hh : 0 ≤ h) (hpi : 0 ≤ pi)
    (hsaving : 0 ≤ saving) :
    Z ^ (M + 5 * h + pi / 8) + Z ^ (-saving) ≤ 2 * Z ^ (M + 5 * h + pi) := by
  have hp := Real.rpow_le_rpow_of_exponent_le hZ (parent_error_exponent_le M h pi hpi)
  have ht := Real.rpow_le_rpow_of_exponent_le hZ
    (parent_tail_exponent_le M h pi saving hM hh hpi hsaving)
  linarith

/-- Uniform bounds for the two positive Cauchy factors give the same
bound after their square roots, without a second energy square. -/
theorem sqrt_product_le {X Y B : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hB : 0 ≤ B) (hXB : X ≤ B) (hYB : Y ≤ B) :
    Real.sqrt X * Real.sqrt Y ≤ B := by
  apply (mul_le_mul (Real.sqrt_le_sqrt hXB) (Real.sqrt_le_sqrt hYB)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
  rw [← pow_two, Real.sq_sqrt hB]

theorem seminorm_le_union_left (s t : Finset (ℕ × ℕ)) (W : SchwartzMap ℝ ℂ) :
    s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      (s ∪ t).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W

theorem seminorm_le_union_right (s t : Finset (ℕ × ℕ)) (W : SchwartzMap ℝ ℂ) :
    t.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      (s ∪ t).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W

theorem seminorm_sq_le_union_left (s t : Finset (ℕ × ℕ)) (W : SchwartzMap ℝ ℂ) :
    (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 ≤
      ((s ∪ t).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 :=
  pow_le_pow_left₀ (apply_nonneg _ _) (seminorm_le_union_left s t W) 2

theorem seminorm_sq_le_union_right (s t : Finset (ℕ × ℕ)) (W : SchwartzMap ℝ ℂ) :
    (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 ≤
      ((s ∪ t).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 :=
  pow_le_pow_left₀ (apply_nonneg _ _) (seminorm_le_union_right s t W) 2

end HeckeSkeleton.Moments.MOM_INV_STEP.FinalStepBounds

end
