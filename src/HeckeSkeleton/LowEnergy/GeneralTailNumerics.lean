import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A fixed kernel order absorbs every prescribed polynomial tail

The polynomial exponent is selected before the kernel order.  The chosen
order depends on the prescribed decay and the fixed positive tail gap,
and is uniform in every scale above the threshold.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.GeneralTailNumerics

/-- The order is explicit and is independent of the running scale Z. -/
def tailOrder (B tau L : ℝ) : ℝ := 1 + 2 * (B + L) / tau

theorem tailOrder_ge_one {B tau L : ℝ}
    (hB : 0 ≤ B) (htau : 0 < tau) (hL : 0 ≤ L) :
    1 ≤ tailOrder B tau L := by
  unfold tailOrder
  have h := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (add_nonneg hB hL)) htau.le
  linarith

theorem tailOrder_exponent {B tau L : ℝ} (htau : 0 < tau) :
    B + (tau / 2) * (-(tailOrder B tau L - 1)) = -L := by
  unfold tailOrder
  field_simp [htau.ne']
  <;> ring

/-- The actual fixed polynomial prefactor is paid exactly by the extra
large-argument order; no scale-dependent order is chosen. -/
theorem polynomial_tail_eq {B tau L Z : ℝ} (htau : 0 < tau) (hZ : 0 < Z) :
    Z ^ B * (Z ^ (tau / 2)) ^ (-(tailOrder B tau L - 1)) = Z ^ (-L) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_add hZ, tailOrder_exponent htau]

theorem absorb_polynomial_tail (B tau L : ℝ)
    (hB : 0 ≤ B) (htau : 0 < tau) (hL : 0 < L) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ Z : ℝ, 1 ≤ Z →
      Z ^ B * (Z ^ (tau / 2)) ^ (-(A - 1)) ≤ Z ^ (-L) := by
  refine ⟨tailOrder B tau L, tailOrder_ge_one hB htau hL.le, ?_⟩
  intro Z hZ
  exact (polynomial_tail_eq htau (zero_lt_one.trans_le hZ)).le

/-- A fixed ratio-box loss of sixteen is absorbed by one threshold. -/
theorem exists_ratio_threshold (tau : ℝ) (htau : 0 < tau) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → 16 ≤ Z ^ (tau / 2) := by
  let Z0 : ℝ := 16 ^ (2 / tau)
  have hZ0 : 1 ≤ Z0 := Real.one_le_rpow (by norm_num) (by positivity)
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ
  have hbase : Z0 ^ (tau / 2) = 16 := by
    dsimp [Z0]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
    have he : (2 / tau) * (tau / 2) = 1 := by field_simp [htau.ne' ]
    rw [he, Real.rpow_one]
  rw [← hbase]
  exact Real.rpow_le_rpow (zero_le_one.trans hZ0) hZ (by positivity)

#print axioms absorb_polynomial_tail
#print axioms exists_ratio_threshold

end HeckeSkeleton.LowEnergy.GeneralTailNumerics
