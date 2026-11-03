import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A smooth window removing the von Mangoldt logarithm

For P >= 2 and a smooth W supported in [1,2], the function
`W x / (Real.log (P * x) : Complex)` is globally smooth.  Its apparently
singular points lie in x < 1, where W is locally zero.

At a prime-power argument the logarithmic weight cancels exactly, leaving
the factor 1/k.  This module proves that identity, support and smoothness,
and the zeroth-order uniform bound.  Higher-order uniform seminorm bounds
and the Mellin contour argument are separate obligations.
-/

noncomputable section

namespace PrimeCancellationLogWindow

open Function Filter Set
open scoped Topology ContDiff

def logWindow (P : ℝ) (W : ℝ → ℂ) (x : ℝ) : ℂ :=
  W x / (Real.log (P * x) : ℂ)

theorem support_logWindow_subset (P : ℝ) (W : ℝ → ℂ) :
    Function.support (logWindow P W) ⊆ Function.support W := by
  intro x hx
  change W x ≠ 0
  intro hzero
  exact hx (by simp only [logWindow, hzero, zero_div])

theorem support_logWindow_subset_Icc (P : ℝ) (W : ℝ → ℂ)
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2) :
    Function.support (logWindow P W) ⊆ Icc (1 : ℝ) 2 :=
  (support_logWindow_subset P W).trans hsupport

theorem log_scaled_pos {P x : ℝ} (hP : 2 ≤ P) (hx : 1 ≤ x) :
    0 < Real.log (P * x) := by
  have hPpos : 0 < P := by linarith
  have hPx : P ≤ P * x := by
    nlinarith [mul_nonneg hPpos.le (sub_nonneg.mpr hx)]
  exact Real.log_pos (by linarith)

theorem log_le_log_scaled {P x : ℝ} (hP : 2 ≤ P) (hx : 1 ≤ x) :
    Real.log P ≤ Real.log (P * x) := by
  have hPpos : 0 < P := by linarith
  apply Real.log_le_log hPpos
  nlinarith [mul_nonneg hPpos.le (sub_nonneg.mpr hx)]

/-- Global smoothness uses local zero extension below 1, rather than an
incorrect assertion that the denominator is nonzero on the whole line. -/
theorem contDiff_logWindow {P : ℝ} {W : ℝ → ℂ}
    (hP : 2 ≤ P) (hW : ContDiff ℝ ∞ W)
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2) :
    ContDiff ℝ ∞ (logWindow P W) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < 1
  · have hzero : logWindow P W =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have hWy : W y = 0 := by
        by_contra hne
        exact (not_le_of_gt hy) (hsupport hne).1
      simp only [logWindow, hWy, zero_div]
    have hconst : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) x := contDiffAt_const
    exact hconst.congr_of_eventuallyEq hzero
  · have hxone : 1 ≤ x := le_of_not_gt hx
    have hPpos : 0 < P := by linarith
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxone
    have hmul : ContDiffAt ℝ ∞ (fun y : ℝ => P * y) x :=
      contDiffAt_const.mul contDiffAt_id
    have hlog : ContDiffAt ℝ ∞ (fun y : ℝ => Real.log (P * y)) x :=
      hmul.log (mul_ne_zero hPpos.ne' hxpos.ne')
    have hinv : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log (P * y))⁻¹) x :=
      hlog.fun_inv (log_scaled_pos hP hxone).ne'
    have hsmul := hinv.smul hW.contDiffAt
    change ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log (P * y))⁻¹ • W y) x at hsmul
    change ContDiffAt ℝ ∞ (fun y : ℝ => W y / (Real.log (P * y) : ℂ)) x
    simpa only [Complex.real_smul, Complex.ofReal_inv,
      div_eq_mul_inv, mul_comm] using hsmul

theorem hasCompactSupport_logWindow (P : ℝ) (W : ℝ → ℂ)
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2) :
    HasCompactSupport (logWindow P W) := by
  change IsCompact (closure (Function.support (logWindow P W)))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (support_logWindow_subset_Icc P W hsupport) isClosed_Icc)

/-- The logarithm of a prime power produces k, exactly.  Neither smoothness
nor any zero-free hypothesis is used in this algebraic identity. -/
theorem prime_power_log_cancellation (P n : ℝ) (a : ℂ) (W : ℝ → ℂ) (k : ℕ)
    (hP : 0 < P) (hn : 1 < n) (hk : 1 ≤ k) :
    (Real.log n : ℂ) * a ^ k * logWindow P W (n ^ k / P) =
      a ^ k * W (n ^ k / P) / (k : ℂ) := by
  have harg : P * (n ^ k / P) = n ^ k := by
    field_simp [hP.ne']
  have hlog : (Real.log n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hn).ne'
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkzero : (k : ℂ) ≠ 0 := by
    exact_mod_cast hkpos.ne'
  simp only [logWindow, harg, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hlog, hkzero]

/-- Pointwise zeroth-order bound on the active half-line. -/
theorem norm_logWindow_le {P x : ℝ} (W : ℝ → ℂ)
    (hP : 2 ≤ P) (hx : 1 ≤ x) :
    ‖logWindow P W x‖ ≤ ‖W x‖ / Real.log P := by
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  rw [logWindow, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (log_scaled_pos hP hx)]
  exact div_le_div_of_nonneg_left (norm_nonneg (W x)) hlogP (log_le_log_scaled hP hx)

/-- A uniform sup-norm bound is reduced by the factor 1/log P.
The statement is pointwise, so it does not need a separate supremum API. -/
theorem norm_logWindow_le_of_bound {P C : ℝ} {W : ℝ → ℂ}
    (hP : 2 ≤ P) (hC : 0 ≤ C)
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2)
    (hbound : ∀ x ∈ Icc (1 : ℝ) 2, ‖W x‖ ≤ C) (x : ℝ) :
    ‖logWindow P W x‖ ≤ C / Real.log P := by
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · exact (norm_logWindow_le W hP hx.1).trans
      (div_le_div_of_nonneg_right (hbound x hx) hlogP.le)
  · have hWx : W x = 0 := by
      by_contra hne
      exact hx (hsupport hne)
    simp only [logWindow, hWx, zero_div, norm_zero]
    exact div_nonneg hC hlogP.le

#print axioms support_logWindow_subset
#print axioms support_logWindow_subset_Icc
#print axioms log_scaled_pos
#print axioms log_le_log_scaled
#print axioms contDiff_logWindow
#print axioms hasCompactSupport_logWindow
#print axioms prime_power_log_cancellation
#print axioms norm_logWindow_le
#print axioms norm_logWindow_le_of_bound

end PrimeCancellationLogWindow
