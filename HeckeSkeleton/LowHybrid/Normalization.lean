import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HeckeSkeleton.LowHybrid.CommonTactics

/-!
# Exact column normalization and annular mass

The only arithmetic input of `annular_normalized_mass_le` is an explicit
linear bound for the size of the specified finite column set. The square-root
normalization and the factor two are proved, including empty sets and zeros.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators

theorem norm_div_sqrt_sq (a : ℂ) (q : ℝ) (hq : 0 ≤ q) :
    ‖a / (Real.sqrt q : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / q := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt hq]

theorem normalized_column_mass {P : Type*} (columns : Finset P)
    (a : P → ℂ) (normP : P → ℝ) (hpos : ∀ p ∈ columns, 0 ≤ normP p) :
    (∑ p ∈ columns, ‖a p / (Real.sqrt (normP p) : ℂ)‖ ^ 2) =
      ∑ p ∈ columns, ‖a p‖ ^ 2 / normP p := by
  exact Finset.sum_congr rfl fun p hp => norm_div_sqrt_sq _ _ (hpos p hp)

/-- The annular normalization has bounded squared mass, using linear ideal
counting once. The coefficient can have an arbitrary fixed support. -/
theorem annular_normalized_mass_le {P : Type*} (columns : Finset P)
    (a : P → ℂ) (normP : P → ℝ) (L C : ℝ) (hL : 0 < L)
    (ha : ∀ p ∈ columns, ‖a p‖ ≤ 1)
    (hlower : ∀ p ∈ columns, L ≤ normP p)
    (hcount : (columns.card : ℝ) ≤ C * (2 * L)) :
    (∑ p ∈ columns, ‖a p / (Real.sqrt (normP p) : ℂ)‖ ^ 2) ≤ 2 * C := by
  rw [normalized_column_mass columns a normP (fun p hp => hL.le.trans (hlower p hp))]
  have hterm (p : P) (hp : p ∈ columns) : ‖a p‖ ^ 2 / normP p ≤ 1 / L := by
    have hs : ‖a p‖ ^ 2 ≤ 1 := by nlinarith [ha p hp, norm_nonneg (a p)]
    calc
      _ ≤ 1 / normP p := div_le_div_of_nonneg_right hs (hL.le.trans (hlower p hp))
      _ ≤ 1 / L := one_div_le_one_div_of_le hL (hlower p hp)
  calc
    _ ≤ ∑ _p ∈ columns, (1 / L : ℝ) := Finset.sum_le_sum hterm
    _ = (columns.card : ℝ) / L := by simp [div_eq_mul_inv]
    _ ≤ (C * (2 * L)) / L := div_le_div_of_nonneg_right hcount hL.le
    _ = 2 * C := by field_simp

/-- The scalar from `q(P)=q(D)q(P')` leaves exactly one reciprocal divisor
norm after taking a square. -/
theorem divisor_column_normalization (D Q : ℝ) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (a : ℂ) :
    a / (Real.sqrt (D * Q) : ℂ) =
      (Real.sqrt D : ℂ)⁻¹ * (a / (Real.sqrt Q : ℂ)) := by
  rw [Real.sqrt_mul hD Q, Complex.ofReal_mul]
  ring

theorem divisor_weight_sq (D : ℝ) (hD : 0 ≤ D) :
    ‖(Real.sqrt D : ℂ)⁻¹‖ ^ 2 = 1 / D := by
  simpa only [one_div, norm_one, one_pow] using norm_div_sqrt_sq (1 : ℂ) D hD

/-- Extracting a scalar from a whole row vector has an exact squared cost. -/
theorem scalar_row_energy {K : Type*} (rows : Finset K) (f : K → ℂ) (a : ℂ) :
    (∑ k ∈ rows, ‖a * f k‖ ^ 2) = ‖a‖ ^ 2 * ∑ k ∈ rows, ‖f k‖ ^ 2 := by
  simp_rw [norm_mul, mul_pow]
  exact (Finset.mul_sum ..).symm

/-- The support must be used before the coefficient is discarded. For
`b = r*c'*h*t^2`, this is exactly the budget needed by weighted Cauchy.
The zero case permits an arbitrary fixed zero extension of the coefficients.
-/
theorem cube_support_weight_budget (wt wc wh r B : ℝ) (beta : ℂ)
    (hwt : 0 < wt) (hwc : 0 ≤ wc) (hwh : 0 < wh) (hr : 0 < r)
    (hB : 0 ≤ B) (hbeta : ‖beta‖ ≤ 1)
    (hsupport : beta ≠ 0 → r * wc * wh * wt ^ 2 ≤ B) :
    wt * wc * ‖beta‖ ^ 2 ≤ (B / r) / (wt * wh) := by
  by_cases hz : beta = 0
  · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    positivity
  · have hsq : ‖beta‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg beta]
    calc
      _ ≤ wt * wc := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (mul_nonneg hwt.le hwc)
      _ ≤ (B / r) / (wt * wh) := by
        apply (le_div_iff₀ (mul_pos hwt hwh)).mpr
        apply (le_div_iff₀ hr).mpr
        calc
          wt * wc * (wt * wh) * r = r * wc * wh * wt ^ 2 := by ring
          _ ≤ B := hsupport hz

#print axioms normalized_column_mass
#print axioms annular_normalized_mass_le
#print axioms divisor_column_normalization
#print axioms divisor_weight_sq
#print axioms scalar_row_energy
#print axioms cube_support_weight_budget

end HeckeSkeleton.LowHybrid
