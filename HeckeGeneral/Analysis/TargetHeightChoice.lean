import HeckeGeneral.Analysis.EndpointClosure

/-!
# Target-dependent height choices after a common saving

The common `σ` is fixed first.  Polynomial height degree, remainder
exponent and a permitted height ceiling may then depend on the target.
Only then is `τ` chosen, followed by the external tail order `N`.
This is exponent bookkeeping, not a proof of the physical error estimate.
-/

namespace HeckeGeneral.Analysis

/-- For fixed common saving, arbitrary target-dependent height data can
be absorbed without reducing that saving for other family members. -/
theorem exists_target_height_and_tail_order {σ ceiling : ℝ}
    (hσ : 0 < σ) (hceiling : 0 < ceiling) (A R C : ℝ) (hA : 0 ≤ A) :
    ∃ τ : ℝ, 0 < τ ∧ τ < ceiling ∧
      C - 2 * σ + A * τ ≤ C - σ ∧
      ∃ N : ℕ, R - τ * N ≤ C - σ := by
  let τ : ℝ := min (ceiling / 2) (σ / (2 * (A + 1)))
  have hden : 0 < 2 * (A + 1) := by linarith
  have hτ : 0 < τ := lt_min (by positivity) (div_pos hσ hden)
  have hτc : τ < ceiling :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hτa : τ * (2 * (A + 1)) ≤ σ :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hprod : 0 ≤ A * τ := mul_nonneg hA hτ.le
  have hfirst : C - 2 * σ + A * τ ≤ C - σ := by nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((R - C + σ) / τ)
  have htail : R - C + σ < (N : ℝ) * τ := (div_lt_iff₀ hτ).mp hN
  exact ⟨τ, hτ, hτc, hfirst, N, by nlinarith⟩

/-- The order of these quantifiers intentionally permits a different
height exponent for each target, while keeping `σ` outside `∀ i`. -/
theorem family_target_height_choices {ι : Type*} {σ : ℝ} (hσ : 0 < σ)
    (ceiling A R : ι → ℝ) (C : ℝ)
    (hceiling : ∀ i, 0 < ceiling i) (hA : ∀ i, 0 ≤ A i) :
    ∀ i, ∃ τ : ℝ, 0 < τ ∧ τ < ceiling i ∧
      C - 2 * σ + A i * τ ≤ C - σ ∧
      ∃ N : ℕ, R i - τ * N ≤ C - σ := by
  intro i
  exact exists_target_height_and_tail_order hσ (hceiling i) (A i) (R i) C (hA i)

end HeckeGeneral.Analysis
