import HeckeGeneral.Analysis.LogGaussianMellin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact positive powers in the initial physical Mellin identity

All bases are the original positive scales or ideal norms.  Real
logarithms make the exponent balance literal and avoid any branch or
chosen-generator convention in this analytic calculation.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialPowers

def positivePower (x : ℝ) (z : ℂ) : ℂ := Complex.exp ((Real.log x : ℂ) * z)

theorem cpow_positive (x : ℝ) (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = positivePower x z := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  rfl

theorem positivePower_neg_one (x : ℝ) (hx : 0 < x) :
    positivePower x (-1) = (x : ℂ)⁻¹ := by
  rw [← cpow_positive x hx, Complex.cpow_neg_one]

theorem positivePower_half (x : ℝ) (hx : 0 < x) :
    positivePower x (1 / 2) = (Real.sqrt x : ℂ) := by
  rw [← cpow_positive x hx]
  have h := Complex.ofReal_cpow hx.le (1 / 2 : ℝ)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rw [← h, Real.sqrt_eq_rpow]

theorem positivePower_neg_half (x : ℝ) (hx : 0 < x) :
    positivePower x (-1 / 2) = (Real.sqrt x : ℂ)⁻¹ := by
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  simp only [positivePower, mul_neg, Complex.exp_neg]
  exact congrArg Inv.inv (positivePower_half x hx)

/-- The square-root denominator of the original physical probe cancels
the actual denominator norm in Poisson, leaving sqrt(X)/(Y N(A)). -/
theorem denominator_poisson_scale (X Y d A : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hd : 0 < d) (hA : 0 < A) :
    ((Y : ℂ)⁻¹ * (Real.sqrt (d * X) : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹) *
        ((X : ℂ) / (A : ℂ) * (d : ℂ)) =
      (Real.sqrt X : ℂ) / (Y : ℂ) / (A : ℂ) := by
  have hdroot : (Real.sqrt d : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne'
  have hXroot : (Real.sqrt X : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hdsq : (Real.sqrt d : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt hd.le
  have hXsq : (Real.sqrt X : ℂ) ^ 2 = (X : ℂ) := by
    exact_mod_cast Real.sq_sqrt hX.le
  rw [Real.sqrt_mul hd.le, Complex.ofReal_mul, ← hdsq, ← hXsq]
  field_simp [hdroot, hXroot, Complex.ofReal_ne_zero.mpr hY.ne',
    Complex.ofReal_ne_zero.mpr hA.ne']
  <;> ring

/-- Exactly a=s+z-1.  The completed cube, denominator and sixth-power
amplifier produce the four exponents in initialRowEulerTerm. -/
theorem initial_power_balance (X Y Z c n d r u : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (hc : 0 < c) (hn : 0 < n)
    (hd : 0 < d) (hr : 0 < r) (hu : 0 < u) (s w z : ℂ) :
    (((Real.sqrt X : ℂ) / (Y : ℂ)) /
        ((Real.sqrt c : ℂ) * (n : ℂ) * ((c * n ^ 3 : ℝ) : ℂ))) *
      ((c * n ^ 3 / Z : ℝ) : ℂ) ^ (-(s + z - 1)) *
      ((d / Y : ℝ) : ℂ) ^ (-w) *
      ((X / (c * n ^ 3) * (u * r ^ 6) : ℝ) : ℂ) ^ (-z) =
    (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) * (Y : ℂ) ^ (w - 1) *
      (u : ℂ) ^ (-z) * (c : ℂ) ^ (-(1 / 2 : ℂ) - s) *
      (n : ℂ) ^ (-1 - 3 * s) * (d : ℂ) ^ (-w) * (r : ℂ) ^ (-6 * z) := by
  have hA : 0 < c * n ^ 3 := mul_pos hc (pow_pos hn 3)
  have hR : 0 < u * r ^ 6 := mul_pos hu (pow_pos hr 6)
  rw [cpow_positive _ (div_pos hA hZ), cpow_positive _ (div_pos hd hY),
    cpow_positive _ (mul_pos (div_pos hX hA) hR),
    cpow_positive X hX, cpow_positive Z hZ, cpow_positive Y hY,
    cpow_positive u hu, cpow_positive c hc, cpow_positive n hn,
    cpow_positive d hd, cpow_positive r hr]
  rw [show (((Real.sqrt X : ℂ) / (Y : ℂ)) /
        ((Real.sqrt c : ℂ) * (n : ℂ) * ((c * n ^ 3 : ℝ) : ℂ))) =
      positivePower X (1 / 2) * positivePower Y (-1) * positivePower c (-1 / 2) *
        positivePower n (-1) * positivePower (c * n ^ 3) (-1) by
    rw [positivePower_half _ hX, positivePower_neg_one _ hY,
      positivePower_neg_half _ hc, positivePower_neg_one _ hn, positivePower_neg_one _ hA]
    ring]
  simp only [positivePower, ← Complex.exp_add]
  congr 1
  rw [Real.log_div hA.ne' hZ.ne', Real.log_div hd.ne' hY.ne',
    Real.log_mul (div_pos hX hA).ne' hR.ne', Real.log_div hX.ne' hA.ne',
    Real.log_mul hu.ne' (pow_ne_zero 6 hr.ne'),
    Real.log_mul hc.ne' (pow_ne_zero 3 hn.ne'), Real.log_pow, Real.log_pow]
  push_cast
  ring

end Expansion.PhysicalInitialPowers
