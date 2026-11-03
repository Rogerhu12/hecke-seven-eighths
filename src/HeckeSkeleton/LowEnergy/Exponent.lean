import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Perturbation-stable exponents for the actual low reflected energy

The input is the explicit arithmetic length ledger, not an energy estimate.
The bounds include the annular shift of the completed scale, the retained
range tolerance, and the fixed-support errors in the row and conductor norms.
`paperExponent` is exactly the exponent in (can-Eref) of the supplied paper.
`ramifiedExponent` is its version with the extra ramified width used by the
ported `HeckePort/Moments/Inversion/TerminalWidths.lean`.

This file imports Mathlib only. It does not assert an actual-row reindexing,
a large-sieve estimate, a reflection identity, or a common-profile theorem.
-/

set_option autoImplicit false

namespace HeckeSkeleton.LowEnergy.Numerics

noncomputable def saving (v z : ℝ) : ℝ := min v (min z ((v + z) / 3))

noncomputable def paperExponent (O H S B z v b T : ℝ) : ℝ :=
  O / 2 + max H (v + b) - S - B + z - saving v z - b -
    max (T - v - 3 * b) 0 / 2

noncomputable def ramifiedExponent (O H S B z v b e T : ℝ) : ℝ :=
  O / 2 + max H (v + b) - S - B + z - saving v z - b - 2 * e / 3 -
    max (T - v - 3 * b - e) 0 / 2

theorem saving_nonneg {v z : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ saving v z := by
  unfold saving
  exact le_min hv (le_min hz (by linarith))

theorem saving_zero {v : ℝ} (hv : 0 ≤ v) : saving v 0 = 0 := by
  unfold saving
  rw [min_eq_left (show (0 : ℝ) ≤ (v + 0) / 3 by linarith), min_eq_right hv]

/-- The cubic gain either removes the full mark length or pays for half
of the squarefree length. No positivity hypothesis on `z` is needed. -/
theorem saving_dichotomy {v z : ℝ} (hv : 0 ≤ v) :
    saving v z = z ∨ v / 2 ≤ saving v z := by
  unfold saving
  by_cases h₁ : v ≤ min z ((v + z) / 3)
  · right
    rw [min_eq_left h₁]
    linarith
  · have h₁' : min v (min z ((v + z) / 3)) = min z ((v + z) / 3) :=
      min_eq_right (le_of_lt (lt_of_not_ge h₁))
    by_cases h₂ : z ≤ (v + z) / 3
    · exact Or.inl (h₁'.trans (min_eq_left h₂))
    · right
      rw [h₁', min_eq_right (le_of_lt (lt_of_not_ge h₂))]
      linarith

/-- A half-column gain and the genuine small-argument kernel scalar pay
one quarter of the effective dual length, including outside the retained range. -/
theorem gain_and_kernel_quarter {v b T u : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hu : v / 2 ≤ u) :
    T / 4 ≤ u + b + max (T - v - 3 * b) 0 / 2 := by
  have hp := le_max_right (T - v - 3 * b) 0
  have ht := le_max_left (T - v - 3 * b) 0
  linarith

/-- Changing the dual threshold by at most `eta` costs at most `eta/2`
in the exponent. This keeps fixed support constants separate from the sieve. -/
theorem paperExponent_threshold_error
    {O H S B z v b T T' eta : ℝ} (hT : T' - eta ≤ T) (heta : 0 ≤ eta) :
    paperExponent O H S B z v b T ≤ paperExponent O H S B z v b T' + eta / 2 := by
  have hmax : max (T' - v - 3 * b) 0 ≤ max (T - v - 3 * b) 0 + eta := by
    apply max_le
    · linarith [le_max_left (T - v - 3 * b) 0]
    · linarith [le_max_right (T - v - 3 * b) 0]
  unfold paperExponent
  linarith

/-- The low-scale dual length with explicit errors in the physical annuli.
`ell` is the actual surviving slot length and `theta` the completed-scale shift. -/
theorem low_dual_length_with_errors
    {d O H A N B z ell theta T eta : ℝ}
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : -eta ≤ theta) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B) :
    T ≤ H - 3 * d + 6 * eta := by
  linarith

/-- The exact low exponent remains bounded with every localization error
present. The constant is independent of the number and lengths of the slots. -/
theorem low_exponent_with_errors
    {d O H A N S B z v b ell theta T eta tau : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hO : 0 ≤ O) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (heta : 0 ≤ eta) (htau : 0 ≤ tau)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta) (hNA : N ≤ A)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B)
    (hretained : v + 3 * b ≤ T + tau) :
    paperExponent O H S B z v b T ≤ (5 / 6 : ℝ) - 2 * d + 8 * eta + tau := by
  have hdual := low_dual_length_with_errors hwidth hconductor hslot hell
    (abs_le.mp htheta).1 hN hB hT
  have hrow : max H (v + b) ≤ H + 6 * eta + tau := by
    apply max_le
    · linarith
    · linarith
  have hkernel : 0 ≤ max (T - v - 3 * b) 0 := le_max_right _ _
  rcases saving_dichotomy (z := z) hv with hsaturated | hhalf
  · unfold paperExponent
    rw [hsaturated]
    linarith
  · have hquarter := gain_and_kernel_quarter hv hb hhalf (T := T)
    have hbase : O / 2 + H - S - B + z - T / 4 ≤
        (5 / 6 : ℝ) - 2 * d + 2 * eta := by
      have hthetaUpper := (abs_le.mp htheta).2
      linarith
    unfold paperExponent
    linarith

/-- The paper has no independent ramified width. This equality makes the
zero-width specialization literal. -/
theorem ramifiedExponent_zero (O H S B z v b T : ℝ) :
    ramifiedExponent O H S B z v b 0 T = paperExponent O H S B z v b T := by
  unfold ramifiedExponent paperExponent
  norm_num

/-- The analogous numerical closure for the ported ramified-width exponent.
The only lower bound on the ramified width is `-eta ≤ e`. -/
theorem low_ramified_exponent_with_errors
    {d O H A N S B z v b e ell theta T eta tau : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hO : 0 ≤ O) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (heta : 0 ≤ eta) (htau : 0 ≤ tau) (he : -eta ≤ e)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta) (hNA : N ≤ A)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B)
    (hretained : v + 3 * b + e ≤ T + tau) :
    ramifiedExponent O H S B z v b e T ≤
      (5 / 6 : ℝ) - 2 * d + 10 * eta + tau := by
  have hdual := low_dual_length_with_errors hwidth hconductor hslot hell
    (abs_le.mp htheta).1 hN hB hT
  have hrow : max H (v + b) ≤ H + 7 * eta + tau := by
    apply max_le
    · linarith
    · linarith
  have hkernel : 0 ≤ max (T - v - 3 * b - e) 0 := le_max_right _ _
  rcases saving_dichotomy (z := z) hv with hsaturated | hhalf
  · unfold ramifiedExponent
    rw [hsaturated]
    linarith
  · have hquarter : (T - e) / 4 ≤ saving v z + b +
        max (T - v - 3 * b - e) 0 / 2 := by
      have hq := gain_and_kernel_quarter hv hb hhalf (T := T - e)
      have heq : T - e - v - 3 * b = T - v - 3 * b - e := by ring
      simpa only [heq] using hq
    have hbase : O / 2 + H - S - B + z - T / 4 ≤
        (5 / 6 : ℝ) - 2 * d + 2 * eta := by
      have hthetaUpper := (abs_le.mp htheta).2
      linarith
    unfold ramifiedExponent
    linarith

/-- The unmarked retained-block simplification, before using conductor
comparisons. This is the complete numerical content of Corollary 4.9. -/
theorem unmarked_exponent_retained
    {O H S B v b T tau : ℝ}
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (htau : 0 ≤ tau) (hretained : v + 3 * b ≤ T + tau) :
    paperExponent O H S B 0 v b T ≤ O / 2 + max H (T - S - B) + tau := by
  have hkernel : 0 ≤ max (T - v - 3 * b) 0 := le_max_right _ _
  unfold paperExponent
  rw [saving_zero hv]
  by_cases hrow : v + b ≤ H
  · rw [max_eq_left hrow]
    linarith [le_max_left H (T - S - B)]
  · rw [max_eq_right (le_of_lt (lt_of_not_ge hrow))]
    linarith [le_max_right H (T - S - B)]

/-- Corollary 4.9 with the fixed-support and retained-range errors exposed. -/
theorem unmarked_exponent_conductor
    {O H S B v b T tau eta M Q V Nstar : ℝ}
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (htau : 0 ≤ tau) (hretained : v + 3 * b ≤ T + tau)
    (hrow : H ≤ M - O + eta)
    (hconductor : T - S - B ≤ 2 * M - O + Q + V - Nstar + eta) :
    paperExponent O H S B 0 v b T ≤
      O / 2 + max (M - O) (2 * M - O + Q + V - Nstar) + eta + tau := by
  have hmax : max H (T - S - B) ≤
      max (M - O) (2 * M - O + Q + V - Nstar) + eta := by
    apply max_le
    · linarith [le_max_left (M - O) (2 * M - O + Q + V - Nstar)]
    · linarith [le_max_right (M - O) (2 * M - O + Q + V - Nstar)]
  have h := unmarked_exponent_retained hS hB hv hb htau hretained (O := O) (H := H)
  linarith

/-- Any desired final exponent is obtained by a concrete, uniform allocation
of the errors; the allocation does not depend on the row or prime tuple. -/
theorem low_error_allocation {eps : ℝ} (heps : 0 < eps) :
    0 < eps / 20 ∧ 0 < eps / 4 ∧ 8 * (eps / 20) + eps / 4 ≤ eps ∧
      10 * (eps / 20) + eps / 4 ≤ eps := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Translate a proved exponent comparison into the genuine power bound. -/
theorem power_bound_of_exponent_bound {Z E M eps C : ℝ}
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hE : E ≤ M + eps) :
    C * Z ^ E ≤ C * Z ^ (M + eps) :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hE) hC

#print axioms saving_dichotomy
#print axioms gain_and_kernel_quarter
#print axioms paperExponent_threshold_error
#print axioms low_dual_length_with_errors
#print axioms low_exponent_with_errors
#print axioms low_ramified_exponent_with_errors
#print axioms unmarked_exponent_retained
#print axioms unmarked_exponent_conductor
#print axioms low_error_allocation
#print axioms power_bound_of_exponent_bound

end HeckeSkeleton.LowEnergy.Numerics
