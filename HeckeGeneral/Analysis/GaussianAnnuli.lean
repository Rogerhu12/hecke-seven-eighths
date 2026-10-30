import HeckeGeneral.Analysis.GaussianDerivatives
import Mathlib.Analysis.PSeries

/-!+# Summable Gaussian bounds across logarithmic annuli

The estimates have the quantifiers required for a fixed compact logarithmic
support: every fixed exponential weight and every derivative order are allowed.
The dominating constant is explicit and the remaining integer series is the
genuine geometric majorant `exp (-|k|)`.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open scoped BigOperators

theorem polynomial_weight_le_exp (n : ℕ) (x : ℝ) :
    (1 + |x|) ^ n ≤ Real.exp ((n : ℝ) * |x|) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by positivity)
  simpa only [add_comm] using Real.add_one_le_exp |x|

/-- Completing the square gives a uniform majorant, not an asymptotic placeholder. -/
theorem weighted_gaussian_le_geometric (n : ℕ) (A x : ℝ) {b : ℝ} (hb : 0 < b) :
    Real.exp (A * |x|) * (1 + |x|) ^ n * Real.exp (-b * x ^ 2) ≤
      Real.exp ((A + n + 1) ^ 2 / (4 * b)) * Real.exp (-|x|) := by
  let D : ℝ := A + n + 1
  have hcomplete : D * |x| - b * x ^ 2 =
      D ^ 2 / (4 * b) - b * (|x| - D / (2 * b)) ^ 2 := by
    rw [← sq_abs x]
    field_simp
    ring
  have hquad : A * |x| + (n : ℝ) * |x| - b * x ^ 2 ≤ D ^ 2 / (4 * b) - |x| := by
    have hp : 0 ≤ b * (|x| - D / (2 * b)) ^ 2 := mul_nonneg hb.le (sq_nonneg _)
    dsimp [D] at hcomplete ⊢
    dsimp [D] at hp
    nlinarith
  calc
    _ ≤ Real.exp (A * |x|) * Real.exp ((n : ℝ) * |x|) * Real.exp (-b * x ^ 2) := by
      gcongr
      exact polynomial_weight_le_exp n x
    _ = Real.exp (A * |x| + (n : ℝ) * |x| - b * x ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (D ^ 2 / (4 * b) - |x|) := Real.exp_le_exp.mpr hquad
    _ = _ := by rw [Real.exp_sub, Real.exp_neg]; rfl

theorem summable_exp_neg_abs_int : Summable (fun k : ℤ => Real.exp (-|(k : ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa using Real.summable_exp_neg_nat

/-- Every exponentially weighted polynomial Gaussian is summable over all integer annuli. -/
theorem summable_weighted_gaussian_int (n : ℕ) (A : ℝ) {b : ℝ} (hb : 0 < b) :
    Summable (fun k : ℤ => Real.exp (A * |(k : ℝ)|) * (1 + |(k : ℝ)|) ^ n *
      Real.exp (-b * (k : ℝ) ^ 2)) := by
  apply (summable_exp_neg_abs_int.mul_left (Real.exp ((A + n + 1) ^ 2 / (4 * b)))).of_nonneg_of_le
  · intro k
    positivity
  · intro k
    exact weighted_gaussian_le_geometric n A k hb

/-- Losing a fixed width in the Gaussian exponent costs only a fixed constant. -/
theorem gaussian_annulus_exponent_le (C x : ℝ) (hC : 0 ≤ C) :
    -(max 0 (|x| - C)) ^ 2 / 4 ≤ C ^ 2 / 4 - x ^ 2 / 8 := by
  by_cases h : |x| ≤ C
  · rw [max_eq_left (sub_nonpos.mpr h)]
    have hs := (sq_le_sq₀ (abs_nonneg x) hC).mpr h
    rw [sq_abs] at hs
    nlinarith [sq_nonneg C]
  · rw [max_eq_right (by linarith : 0 ≤ |x| - C)]
    nlinarith [sq_nonneg (|x| - 2 * C), sq_abs x]

theorem annulus_polynomial_weight_le (n : ℕ) (C x : ℝ) (hC : 0 ≤ C) :
    (1 + |x| + C) ^ n ≤ (1 + C) ^ n * (1 + |x|) ^ n := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg hC (abs_nonneg x)]

def gaussianAnnulusMajorant (n : ℕ) (C : ℝ) (k : ℤ) : ℝ :=
  gaussianDerivativeBound n * (1 + |(k : ℝ)| + C) ^ n *
    Real.exp (-(max 0 (|(k : ℝ)| - C)) ^ 2 / 4)

theorem gaussianAnnulusMajorant_nonneg (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (k : ℤ) :
    0 ≤ gaussianAnnulusMajorant n C k := by
  unfold gaussianAnnulusMajorant
  exact mul_nonneg (mul_nonneg (gaussianDerivativeBound_nonneg n) (by positivity)) (by positivity)

theorem gaussianAnnulusMajorant_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (k : ℤ) :
    gaussianAnnulusMajorant n C k ≤
      (gaussianDerivativeBound n * (1 + C) ^ n * Real.exp (C ^ 2 / 4)) *
        ((1 + |(k : ℝ)|) ^ n * Real.exp (-(1 / 8 : ℝ) * (k : ℝ) ^ 2)) := by
  unfold gaussianAnnulusMajorant
  calc
    _ ≤ gaussianDerivativeBound n * ((1 + C) ^ n * (1 + |(k : ℝ)|) ^ n) *
        Real.exp (C ^ 2 / 4 - (k : ℝ) ^ 2 / 8) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (annulus_polynomial_weight_le n C k hC)
          (gaussianDerivativeBound_nonneg n)
      · exact Real.exp_le_exp.mpr (gaussian_annulus_exponent_le C k hC)
      · positivity
      · exact mul_nonneg (gaussianDerivativeBound_nonneg n) (by positivity)
    _ = _ := by
      rw [show C ^ 2 / 4 - (k : ℝ) ^ 2 / 8 = C ^ 2 / 4 + -(1 / 8 : ℝ) * (k : ℝ) ^ 2 by ring,
        Real.exp_add]
      ring

/-- The derivative majorants are summable with every prescribed exponential loss. -/
theorem summable_gaussianAnnulusMajorant (n : ℕ) (C A : ℝ) (hC : 0 ≤ C) :
    Summable (fun k : ℤ => Real.exp (A * |(k : ℝ)|) * gaussianAnnulusMajorant n C k) := by
  let D : ℝ := gaussianDerivativeBound n * (1 + C) ^ n * Real.exp (C ^ 2 / 4)
  have h := (summable_weighted_gaussian_int n A (b := 1 / 8) (by norm_num)).mul_left D
  apply h.of_nonneg_of_le
  · intro k
    exact mul_nonneg (Real.exp_pos _).le (gaussianAnnulusMajorant_nonneg n C hC k)
  · intro k
    calc
      _ ≤ Real.exp (A * |(k : ℝ)|) *
          (D * ((1 + |(k : ℝ)|) ^ n * Real.exp (-(1 / 8 : ℝ) * (k : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left (gaussianAnnulusMajorant_le n C hC k) (Real.exp_pos _).le
      _ = _ := by ring

/-- This summability applies uniformly to one arbitrary point chosen in each annulus. -/
theorem summable_gaussian_annular_derivatives (n : ℕ) (C A : ℝ) (hC : 0 ≤ C)
    (u : ℤ → ℝ) (hu : ∀ k, |u k| ≤ C) :
    Summable (fun k : ℤ => Real.exp (A * |(k : ℝ)|) *
      |iteratedDeriv n (fun x => realLogGaussian ((k : ℝ) + x)) (u k)|) := by
  apply (summable_gaussianAnnulusMajorant n C A hC).of_nonneg_of_le
  · intro k
    positivity
  · intro k
    exact mul_le_mul_of_nonneg_left
      (abs_iteratedDeriv_gaussian_annulus_le n k C (u k) hC (hu k)) (Real.exp_pos _).le

end HeckeGeneral.Analysis
