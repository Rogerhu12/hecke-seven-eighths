import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
Loss-free numerical specialization of the reflected energy in revised (6.22).
The hypotheses are the actual length and conductor ledger that the reflection
and hybrid estimate still have to produce. No reflected-energy estimate,
coefficient independence, or common-profile bound is asserted here.
-/
set_option autoImplicit false

namespace HeckeSkeleton.LowExponent

/-- The hybrid gain either saturates the active slot length or supplies
at least half the squarefree dual length. -/
theorem hybrid_gain_dichotomy (v za : ℝ) (hv : 0 ≤ v) :
    min v (min za ((v + za) / 3)) = za ∨
      v / 2 ≤ min v (min za ((v + za) / 3)) := by
  by_cases houter : v ≤ min za ((v + za) / 3)
  · right
    rw [min_eq_left houter]
    linarith
  · have houter_eq : min v (min za ((v + za) / 3)) = min za ((v + za) / 3) :=
      min_eq_right (le_of_not_ge houter)
    by_cases hinner : za ≤ (v + za) / 3
    · left
      exact houter_eq.trans (min_eq_left hinner)
    · right
      rw [houter_eq, min_eq_right (le_of_not_ge hinner)]
      linarith

/-- A half-squarefree hybrid gain and the kernel positive part together
pay at least a quarter of the dual length. This also holds outside the
retained range, although the final specialization uses that range. -/
theorem hybrid_and_kernel_quarter
    (v b T u : ℝ) (hv : 0 ≤ v) (hb : 0 ≤ b) (hu : v / 2 ≤ u) :
    T / 4 ≤ u + b + max (T - v - 3 * b) 0 / 2 := by
  have hgain : (v + 3 * b) / 4 ≤ u + b := by linarith
  have hpositive : 0 ≤ max (T - v - 3 * b) 0 := le_max_right _ _
  have hdual : T - v - 3 * b ≤ max (T - v - 3 * b) 0 := le_max_left _ _
  linarith

/-- The low geometry and the conductor deficit put the retained dual
length below the actual residual row length, with saving `3*d`. Here the
completed length has no annular perturbation (`theta_N = 0`). -/
theorem dual_length_le
    (d O H B0 N0 A0 za T : ℝ)
    (hwidth : 0 ≤ (5 / 6 : ℝ) - 2 * d - O - H)
    (hB0 : 0 ≤ B0) (hN0 : 0 ≤ N0)
    (hconductor : 2 * A0 ≤ O) (hslot : za ≤ (1 / 6 : ℝ) - d)
    (hT : T = 2 * H + 2 * A0 + 2 * za - 1 - ((1 / 6 : ℝ) - d) - N0 - 3 * B0) :
    T ≤ H - 3 * d := by
  linarith

/-- Complete loss-free numerical child in the low reflected-energy bound.
With `M' = 5/6 - 2*d`, `ell' = 1/6 - d`, and
`Delta = M' - O - H`, the exact reflected exponent is at most `M'`.
The true reflection, hybrid estimate, and profile assembly remain separate
analytic obligations; all their length data are explicit hypotheses here. -/
theorem reflected_exponent_le
    (d O H S0 B0 N0 A0 za T v b : ℝ)
    (hd : 0 ≤ d) (hd_upper : d ≤ (1 / 6 : ℝ))
    (hwidth : 0 ≤ (5 / 6 : ℝ) - 2 * d - O - H)
    (hO : 0 ≤ O) (hS0 : 0 ≤ S0) (hB0 : 0 ≤ B0)
    (hN0 : 0 ≤ N0) (hA0 : 0 ≤ A0)
    (hconductor : 2 * A0 ≤ O) (hN0_le : N0 ≤ A0)
    (hza : 0 ≤ za) (hslot : za ≤ (1 / 6 : ℝ) - d)
    (hT : T = 2 * H + 2 * A0 + 2 * za - 1 - ((1 / 6 : ℝ) - d) - N0 - 3 * B0)
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hretained : v + 3 * b ≤ T) :
    O / 2 + max H (v + b) - S0 - B0 + za -
        min v (min za ((v + za) / 3)) - b - max (T - v - 3 * b) 0 / 2 ≤
      (5 / 6 : ℝ) - 2 * d := by
  have hdual : T ≤ H - 3 * d :=
    dual_length_le d O H B0 N0 A0 za T hwidth hB0 hN0 hconductor hslot hT
  have hrow : v + b ≤ H := by linarith
  rw [max_eq_left hrow]
  have hpositive : 0 ≤ max (T - v - 3 * b) 0 := le_max_right _ _
  rcases hybrid_gain_dichotomy v za hv with hsaturated | hhalf
  · rw [hsaturated]
    linarith
  · have hquarter := hybrid_and_kernel_quarter v b T
        (min v (min za ((v + za) / 3))) hv hb hhalf
    have hresidual : 0 ≤ 2 * A0 - N0 + B0 + 4 * S0 := by linarith
    have hbudget : za ≤ O / 2 + ((5 / 6 : ℝ) - 2 * d - O - H) +
        S0 + B0 + T / 4 := by
      linarith
    linarith

end HeckeSkeleton.LowExponent
