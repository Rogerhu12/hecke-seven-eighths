import HeckeSkeleton.LowHybrid.Counting
import HeckeSkeleton.LowHybrid.Normalization

/-!
# Cutoff-counting and coefficient-mass bridges

These interfaces connect a customary norm-cutoff count to the harmonic
estimates, and retain an arbitrary squared beta mass in the cube budget.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators
noncomputable section

/-- A cardinal bound for complete norm cutoffs controls every finite
norm-bounded subset, without needing an enumeration of that subset. -/
theorem linear_norm_counting_of_cutoffs
    {I : Type*} (q : I → ℕ) (C : ℝ) (cutoff : ℕ → Finset I)
    (hmem : ∀ N : ℕ, ∀ i : I, q i ≤ N → i ∈ cutoff N)
    (hcard : ∀ N : ℕ, ((cutoff N).card : ℝ) ≤ C * N) :
    LinearNormCounting q C := by
  intro N s hs
  have hsub : s ⊆ cutoff N := fun i hi => hmem N i (hs i hi)
  exact (show (s.card : ℝ) ≤ ((cutoff N).card : ℝ) from
    Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcard N)

/-- The counting theorem applies to a real-valued norm once its natural
ideal norm has been identified. The constant is uniform in actual supports. -/
theorem real_norm_reciprocal_sum_subpower
    {I : Type*} (q : I → ℕ) (normI : I → ℝ) (hnorm : ∀ i, normI i = (q i : ℝ))
    (C : ℝ) (hC : 0 < C) (hq : ∀ i : I, 1 ≤ q i)
    (hcount : LinearNormCounting q C) (eps : ℝ) (heps : 0 < eps) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset I,
      (∀ i ∈ s, normI i ≤ X) →
        (∑ i ∈ s, 1 / normI i) ≤ CH * X ^ eps := by
  obtain ⟨CH, hCH, hb⟩ := reciprocal_sum_subpower_of_linear_counting
    q C hC hq hcount eps heps
  refine ⟨CH, hCH, ?_⟩
  intro X hX s hs
  have hs' : ∀ i ∈ s, (q i : ℝ) ≤ X := by
    intro i hi
    simpa only [hnorm] using hs i hi
  simpa only [hnorm] using hb X hX s hs'

/-- The true cube-support budget with an arbitrary squared beta mass.
The factor betaMass occurs exactly once in the final estimate. -/
theorem cube_support_weight_budget_mass
    (wt wc wh r B betaMass : ℝ) (beta : ℂ)
    (hwt : 0 < wt) (hwc : 0 ≤ wc) (hwh : 0 < wh) (hr : 0 < r)
    (hB : 0 ≤ B) (hmass : 0 ≤ betaMass)
    (hbeta : ‖beta‖ ^ 2 ≤ betaMass)
    (hsupport : beta ≠ 0 → r * wc * wh * wt ^ 2 ≤ B) :
    wt * wc * ‖beta‖ ^ 2 ≤ (betaMass * B / r) / (wt * wh) := by
  by_cases hzero : beta = 0
  · simp only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact div_nonneg (div_nonneg (mul_nonneg hmass hB) (le_of_lt hr))
      (le_of_lt (mul_pos hwt hwh))
  have hden : 0 < r * wt * wh := mul_pos (mul_pos hr hwt) hwh
  have hbase : wt * wc ≤ B / (r * wt * wh) := by
    apply (le_div_iff₀ hden).mpr
    calc
      wt * wc * (r * wt * wh) = r * wc * wh * wt ^ 2 := by ring
      _ ≤ B := hsupport hzero
  calc
    wt * wc * ‖beta‖ ^ 2 ≤ (B / (r * wt * wh)) * betaMass :=
      mul_le_mul hbase hbeta (sq_nonneg _) (div_nonneg hB (le_of_lt hden))
    _ = _ := by
      simp only [div_eq_mul_inv]
      ring

#print axioms linear_norm_counting_of_cutoffs
#print axioms real_norm_reciprocal_sum_subpower
#print axioms cube_support_weight_budget_mass

end
end HeckeSkeleton.LowHybrid
