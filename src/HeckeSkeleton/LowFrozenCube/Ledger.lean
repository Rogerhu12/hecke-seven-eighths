import Mathlib.Analysis.Complex.Basic
import HeckeSkeleton.LowHybrid.CommonTactics

/-!
# The real exponent ledger for the frozen-cube reduction

This module proves only real-variable identities and inequalities. It has no
dependency on a number field, an ideal type, a theta reflection theorem, or an
assumed hybrid-energy estimate. The parameters and inequalities are those in
`eq:can-Eref` and `eq:can-terminal-ledger` of the supplied paper. In particular,
the retained-block tolerance `tau` is kept explicitly.
-/

namespace HeckeSkeleton.LowFrozenCube

/-- The saving in the quadratic--cubic terminal. -/
noncomputable def cubicSaving (v z : ℝ) : ℝ := min v (min z ((v + z) / 3))

theorem cubicSaving_nonneg {v z : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ cubicSaving v z := by
  unfold cubicSaving
  exact le_min hv (le_min hz (by linarith))

theorem cubicSaving_le_left (v z : ℝ) : cubicSaving v z ≤ v :=
  min_le_left _ _

theorem cubicSaving_le_right (v z : ℝ) : cubicSaving v z ≤ z :=
  le_trans (min_le_right _ _) (min_le_left _ _)

/-- The maximum produced by the cubic large sieve, with the exact saving. -/
theorem cubic_growth_identity (v z : ℝ) :
    max v (max z (2 * (v + z) / 3)) = v + z - cubicSaving v z := by
  unfold cubicSaving
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- This is the precise split between the two column branches. -/
theorem cubicSaving_dichotomy {v z : ℝ} (hv : 0 ≤ v) :
    cubicSaving v z = z ∨ v ≤ 2 * cubicSaving v z := by
  unfold cubicSaving
  simp only [min_def]
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr (by linarith)

/-- Exponent of the squared scalar outside the hybrid norm; its column
normalization is already included in that norm. -/
noncomputable def squaredCoefficientExponent (v ell S B : ℝ) : ℝ := -v - 2 * ell - S - B

/-- Exponent of `(K + N B) B (N + L + (N L)^(2/3))` on logarithmic scales. -/
noncomputable def hybridGrowthExponent (H v ell z : ℝ) : ℝ :=
  max H (v + ell) + ell + max v (max z (2 * (v + z) / 3))

/-- The common kernel scalar has this exponent after squaring. -/
noncomputable def squaredKernelExponent (T v ell : ℝ) : ℝ :=
  -(max (T - v - 3 * ell) 0) / 2

/-- The exponent in `eq:can-Eref`, including the powerful-row count. -/
noncomputable def reflectedExponent (O H v ell S B z T : ℝ) : ℝ :=
  O / 2 + max H (v + ell) - S - B + z - cubicSaving v z - ell -
    (max (T - v - 3 * ell) 0) / 2

/-- The coefficient, sieve, kernel and powerful-row factors produce the
claimed exponent with no discarded terms. -/
theorem reflected_exponent_identity (O H v ell S B z T : ℝ) :
    O / 2 + squaredCoefficientExponent v ell S B +
      hybridGrowthExponent H v ell z + squaredKernelExponent T v ell =
        reflectedExponent O H v ell S B z T := by
  unfold squaredCoefficientExponent hybridGrowthExponent squaredKernelExponent
    reflectedExponent
  rw [cubic_growth_identity]
  ring

/-- The row branch of the terminal ledger. The only margin needed here is
the first invariant. -/
theorem terminal_row_branch
    (F M O H v ell S B z T Q z0 c : ℝ)
    (hO : 0 ≤ O) (hS : 0 ≤ S) (hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hv : 0 ≤ v) (hz : 0 ≤ z) (hQ : 0 ≤ Q)
    (hz0 : z ≤ z0) (hH : H ≤ M - O)
    (hmargin : c ≤ F - M - Q - z0)
    (hrow : v + ell ≤ H) :
    reflectedExponent O H v ell S B z T ≤ F - c := by
  have hu := cubicSaving_nonneg hv hz
  have hk : 0 ≤ max (T - v - 3 * ell) 0 := le_max_right _ _
  unfold reflectedExponent
  rw [max_eq_left hrow]
  linarith

/-- The column branch with `u = z`. `Nstar = N - 3 bh` records the
cube completion, and `tau` records the retained dual range. -/
theorem terminal_column_equal_branch
    (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ)
    (hF : F = N + V) (hNstar : Nstar = N - 3 * bh)
    (hO : 0 ≤ O) (hell : 0 ≤ ell) (hQ : 0 ≤ Q)
    (hV : V ≤ d0) (hbh : bh ≤ d0) (hz0 : z ≤ z0)
    (hmargin : c ≤ F - M - Q - z0)
    (hconductor : T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z)
    (hretained : v + 3 * ell ≤ T + tau)
    (hcolumn : H ≤ v + ell) (hu : cubicSaving v z = z) :
    reflectedExponent O H v ell S B z T ≤ F - 2 * c + 5 * d0 + tau := by
  have hk : 0 ≤ max (T - v - 3 * ell) 0 := le_max_right _ _
  unfold reflectedExponent
  rw [max_eq_right hcolumn, hu]
  linarith

/-- The other column branch. Both invariant margins are used. -/
theorem terminal_column_other_branch
    (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ)
    (hF : F = N + V) (hNstar : Nstar = N - 3 * bh)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hV : V ≤ d0) (hbh : bh ≤ d0) (hz0 : z ≤ z0)
    (hmargin1 : c ≤ F - M - Q - z0)
    (hmargin2 : c ≤ 4 * F - 3 * M - 6 * z0)
    (hconductor : T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z)
    (hretained : v + 3 * ell ≤ T + tau)
    (hcolumn : H ≤ v + ell) (hu : v ≤ 2 * cubicSaving v z) :
    reflectedExponent O H v ell S B z T ≤
      F - M / 4 - 3 * c / 4 + 5 * d0 / 2 + tau / 2 := by
  have hk : 0 ≤ max (T - v - 3 * ell) 0 := le_max_right _ _
  unfold reflectedExponent
  rw [max_eq_right hcolumn]
  linarith

/-- The three terminal exponents, with their explicit localization losses. -/
noncomputable def terminalBound (F M c d0 tau : ℝ) : ℝ :=
  max (F - c) (max (F - 2 * c + 5 * d0 + tau)
    (F - M / 4 - 3 * c / 4 + 5 * d0 / 2 + tau / 2))

/-- The complete terminal ledger as a single inequality. The premises are
range conditions and conductor/invariant comparisons, not energy bounds. -/
theorem terminal_ledger
    (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ)
    (hF : F = N + V) (hNstar : Nstar = N - 3 * bh)
    (hO : 0 ≤ O) (hS : 0 ≤ S) (hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hv : 0 ≤ v) (hz : 0 ≤ z) (hQ : 0 ≤ Q)
    (hV : V ≤ d0) (hbh : bh ≤ d0) (hz0 : z ≤ z0)
    (hH : H ≤ M - O)
    (hmargin1 : c ≤ F - M - Q - z0)
    (hmargin2 : c ≤ 4 * F - 3 * M - 6 * z0)
    (hconductor : T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z)
    (hretained : v + 3 * ell ≤ T + tau) :
    reflectedExponent O H v ell S B z T ≤ terminalBound F M c d0 tau := by
  by_cases hrow : v + ell ≤ H
  · exact le_trans
      (terminal_row_branch F M O H v ell S B z T Q z0 c
        hO hS hB hell hv hz hQ hz0 hH hmargin1 hrow)
      (le_max_left _ _)
  · have hcolumn : H ≤ v + ell := le_of_lt (lt_of_not_ge hrow)
    rcases cubicSaving_dichotomy hv with hu | hu
    · exact le_trans
        (terminal_column_equal_branch F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau
          hF hNstar hO hell hQ hV hbh hz0 hmargin1 hconductor hretained hcolumn hu)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans
        (terminal_column_other_branch F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau
          hF hNstar hS hB hell hV hbh hz0 hmargin1 hmargin2 hconductor hretained
          hcolumn hu)
        (le_trans (le_max_right _ _) (le_max_right _ _))

/-- A quantitative common saving once step size and localization tolerance
are chosen within fixed fractions of the node margin. -/
theorem terminalBound_le_half_margin
    (F M c d0 tau : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hd : d0 ≤ c / 100) (htau : tau ≤ c / 8) :
    terminalBound F M c d0 tau ≤ F - c / 2 := by
  unfold terminalBound
  apply max_le
  · linarith
  · apply max_le <;> linarith

#print axioms cubic_growth_identity
#print axioms cubicSaving_dichotomy
#print axioms reflected_exponent_identity
#print axioms terminal_row_branch
#print axioms terminal_column_equal_branch
#print axioms terminal_column_other_branch
#print axioms terminal_ledger
#print axioms terminalBound_le_half_margin

end HeckeSkeleton.LowFrozenCube
