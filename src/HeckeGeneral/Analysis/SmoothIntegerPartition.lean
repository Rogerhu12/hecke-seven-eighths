import HeckeGeneral.Analysis.GaussianAnnularTruncation
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A fixed smooth compact integer-translation partition

Taking the difference of two consecutive smooth transitions gives an actual
compact cutoff. At every x only the shifts floor(x) and floor(x)+1 can be
nonzero, and their two values sum to one. The resulting Gaussian compact
approximations therefore have no externally supplied partition hypothesis.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open scoped Topology ContDiff

def fixedIntegerCutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x

theorem contDiff_fixedIntegerCutoff : ContDiff ℝ ∞ fixedIntegerCutoff := by
  have hshift : ContDiff ℝ ∞ (fun x : ℝ => x + 1) := contDiff_id.add contDiff_const
  exact (Real.smoothTransition.contDiff.comp hshift).sub Real.smoothTransition.contDiff

theorem fixedIntegerCutoff_nonneg (x : ℝ) : 0 ≤ fixedIntegerCutoff x :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith : x ≤ x + 1))

theorem fixedIntegerCutoff_le_one (x : ℝ) : fixedIntegerCutoff x ≤ 1 := by
  unfold fixedIntegerCutoff
  linarith [Real.smoothTransition.le_one (x + 1), Real.smoothTransition.nonneg x]

theorem fixedIntegerCutoff_zero_of_le {x : ℝ} (hx : x ≤ -1) : fixedIntegerCutoff x = 0 := by
  unfold fixedIntegerCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem fixedIntegerCutoff_zero_of_ge {x : ℝ} (hx : 1 ≤ x) : fixedIntegerCutoff x = 0 := by
  unfold fixedIntegerCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le hx, sub_self]

theorem tsupport_fixedIntegerCutoff : tsupport fixedIntegerCutoff ⊆ Set.Icc (-1) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (fixedIntegerCutoff_zero_of_le (lt_of_not_ge h).le)
  · by_contra h
    exact hx (fixedIntegerCutoff_zero_of_ge (lt_of_not_ge h).le)

theorem hasCompactSupport_fixedIntegerCutoff : HasCompactSupport fixedIntegerCutoff :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) tsupport_fixedIntegerCutoff

theorem fixedIntegerCutoff_shift_zero (x : ℝ) (k : ℤ)
    (hk : k ∉ ({⌊x⌋, ⌊x⌋ + 1} : Finset ℤ)) : fixedIntegerCutoff (x - k) = 0 := by
  have hne : k ≠ ⌊x⌋ ∧ k ≠ ⌊x⌋ + 1 := by simpa only [Finset.mem_insert,
    Finset.mem_singleton, not_or] using hk
  have hfloor := Int.floor_le x
  have hnext := Int.lt_floor_add_one x
  by_cases hlow : k ≤ ⌊x⌋
  · have hk' : (k : ℝ) + 1 ≤ (⌊x⌋ : ℝ) := by
      exact_mod_cast (show k + 1 ≤ ⌊x⌋ by omega)
    exact fixedIntegerCutoff_zero_of_ge (by linarith)
  · have hk' : (⌊x⌋ : ℝ) + 2 ≤ (k : ℝ) := by
      exact_mod_cast (show ⌊x⌋ + 2 ≤ k by omega)
    exact fixedIntegerCutoff_zero_of_le (by linarith)

/-- The fixed cutoff really forms a partition under every integer translation. -/
theorem fixedIntegerCutoff_partition (x : ℝ) :
    (∑' k : ℤ, fixedIntegerCutoff (x - k)) = 1 := by
  rw [tsum_eq_sum (s := ({⌊x⌋, ⌊x⌋ + 1} : Finset ℤ))]
  · rw [Finset.sum_pair (by omega : ⌊x⌋ ≠ ⌊x⌋ + 1)]
    have hfloor := Int.floor_le x
    have hnext := Int.lt_floor_add_one x
    push_cast at hnext ⊢
    unfold fixedIntegerCutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - (⌊x⌋ : ℝ) + 1),
      Real.smoothTransition.zero_of_nonpos (by linarith : x - ((⌊x⌋ : ℝ) + 1) ≤ 0)]
    have heq : x - ((⌊x⌋ : ℝ) + 1) + 1 = x - (⌊x⌋ : ℝ) := by ring
    rw [heq]
    ring
  · exact fixedIntegerCutoff_shift_zero x

/-- All prescribed finite derivative orders admit actual smooth compact Gaussian approximants. -/
theorem exists_compact_realLogGaussian_approximation (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧
      ∀ n ≤ m, ∀ x : ℝ, |iteratedDeriv n realLogGaussian x - iteratedDeriv n p x| < ε :=
  exists_compact_realLogGaussian_approximation_of_partition fixedIntegerCutoff
    contDiff_fixedIntegerCutoff hasCompactSupport_fixedIntegerCutoff 1 zero_le_one
    tsupport_fixedIntegerCutoff fixedIntegerCutoff_partition m hε

end HeckeGeneral.Analysis
