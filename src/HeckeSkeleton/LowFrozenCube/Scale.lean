import HeckeSkeleton.LowFrozenCube.Ledger
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual positive-base power bounds for the frozen-cube ledger

For `Z ≥ 1`, the hybrid scale expression is bounded by six times the
corresponding power of `Z`. The factor six is the product of the two terms in
the quadratic factor and the three terms in the cubic factor. These are
inequalities of real numbers, not asymptotic notation.
-/

namespace HeckeSkeleton.LowFrozenCube

noncomputable def quadraticScale (Z H v ell : ℝ) : ℝ :=
  Z ^ H + Z ^ v * Z ^ ell

noncomputable def cubicScale (Z v z : ℝ) : ℝ :=
  Z ^ v + Z ^ z + (Z ^ v * Z ^ z) ^ (2 / 3 : ℝ)

noncomputable def hybridScale (Z H v ell z : ℝ) : ℝ :=
  quadraticScale Z H v ell * Z ^ ell * cubicScale Z v z

theorem quadraticScale_le (Z H v ell : ℝ) (hZ : 1 ≤ Z) :
    quadraticScale Z H v ell ≤ 2 * Z ^ (max H (v + ell)) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold quadraticScale
  rw [← Real.rpow_add hZpos v ell]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_left H (v + ell))
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_right H (v + ell))
  linarith

theorem cubicScale_nonneg (Z v z : ℝ) (hZ : 0 ≤ Z) :
    0 ≤ cubicScale Z v z := by
  unfold cubicScale
  exact add_nonneg
    (add_nonneg (Real.rpow_nonneg hZ v) (Real.rpow_nonneg hZ z))
    (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hZ v)
      (Real.rpow_nonneg hZ z)) (2 / 3 : ℝ))

theorem cubicScale_le (Z v z : ℝ) (hZ : 1 ≤ Z) :
    cubicScale Z v z ≤ 3 * Z ^ (max v (max z (2 * (v + z) / 3))) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZ0 : 0 ≤ Z := le_of_lt hZpos
  have hp : (Z ^ v * Z ^ z) ^ (2 / 3 : ℝ) = Z ^ (2 * (v + z) / 3) := by
    rw [← Real.rpow_add hZpos v z, ← Real.rpow_mul hZ0]
    congr 1
    ring
  unfold cubicScale
  rw [hp]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ
    (le_max_left v (max z (2 * (v + z) / 3)))
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ
    (le_trans (le_max_left z (2 * (v + z) / 3)) (le_max_right v _))
  have h3 := Real.rpow_le_rpow_of_exponent_le hZ
    (le_trans (le_max_right z (2 * (v + z) / 3)) (le_max_right v _))
  linarith

/-- The actual substitution `K=Z^H`, `N=Z^v`, `B=Z^ell`, `L=Z^z`,
including the mixed `2/3`-power, obeys the ledger with constant six. -/
theorem hybridScale_le (Z H v ell z : ℝ) (hZ : 1 ≤ Z) :
    hybridScale Z H v ell z ≤ 6 * Z ^ (hybridGrowthExponent H v ell z) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZ0 : 0 ≤ Z := le_of_lt hZpos
  have hmid := Real.rpow_nonneg hZ0 ell
  have hA := Real.rpow_nonneg hZ0 (max H (v + ell))
  unfold hybridScale
  calc
    quadraticScale Z H v ell * Z ^ ell * cubicScale Z v z ≤
        (2 * Z ^ (max H (v + ell))) * Z ^ ell *
          (3 * Z ^ (max v (max z (2 * (v + z) / 3)))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (quadraticScale_le Z H v ell hZ) hmid)
        (cubicScale_le Z v z hZ) (cubicScale_nonneg Z v z hZ0)
        (mul_nonneg (mul_nonneg (by norm_num) hA) hmid)
    _ = 6 * Z ^ (hybridGrowthExponent H v ell z) := by
      unfold hybridGrowthExponent
      rw [Real.rpow_add hZpos, Real.rpow_add hZpos]
      ring

/-- Exact real-power bookkeeping after multiplying by the squared external
coefficient, the squared common kernel scalar, and the powerful-row count. -/
theorem frozen_scale_le (Z O H v ell S B z T : ℝ) (hZ : 1 ≤ Z) :
    Z ^ (O / 2) * Z ^ (squaredCoefficientExponent v ell S B) *
        hybridScale Z H v ell z * Z ^ (squaredKernelExponent T v ell) ≤
      6 * Z ^ (reflectedExponent O H v ell S B z T) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZ0 : 0 ≤ Z := le_of_lt hZpos
  have hpre : 0 ≤ Z ^ (O / 2) * Z ^ (squaredCoefficientExponent v ell S B) :=
    mul_nonneg (Real.rpow_nonneg hZ0 _) (Real.rpow_nonneg hZ0 _)
  have hker := Real.rpow_nonneg hZ0 (squaredKernelExponent T v ell)
  calc
    Z ^ (O / 2) * Z ^ (squaredCoefficientExponent v ell S B) *
        hybridScale Z H v ell z * Z ^ (squaredKernelExponent T v ell) ≤
      Z ^ (O / 2) * Z ^ (squaredCoefficientExponent v ell S B) *
        (6 * Z ^ (hybridGrowthExponent H v ell z)) *
          Z ^ (squaredKernelExponent T v ell) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hybridScale_le Z H v ell z hZ) hpre) hker
    _ = 6 * Z ^ (reflectedExponent O H v ell S B z T) := by
      rw [← reflected_exponent_identity O H v ell S B z T]
      simp only [Real.rpow_add hZpos]
      ring

#print axioms quadraticScale_le
#print axioms cubicScale_le
#print axioms hybridScale_le
#print axioms frozen_scale_le

end HeckeSkeleton.LowFrozenCube
