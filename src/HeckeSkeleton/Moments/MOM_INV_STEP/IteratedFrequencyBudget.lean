import HeckeSkeleton.Moments.MOM_INV_STEP.NestedMellinBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCommonEnvelope

/-! Uniform integration of the actual polynomial spectral costs. -/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.IteratedFrequencyBudget

open MeasureTheory CommonKernel FirstCommonEnvelope NestedMellinBudget
open scoped Classical

theorem coordinate_polynomial_bound (L : LogPlane →L[ℝ] ℝ) (m : ℕ) (ξ : LogPlane) :
    (1 + |L ξ|) ^ m ≤ max 1 ‖L‖ ^ m * (1 + ‖ξ‖) ^ m := by
  have hL := L.le_opNorm ξ
  rw [Real.norm_eq_abs] at hL
  have h : 1 + |L ξ| ≤ max 1 ‖L‖ * (1 + ‖ξ‖) := by
    nlinarith [le_max_left (1 : ℝ) ‖L‖, le_max_right (1 : ℝ) ‖L‖, norm_nonneg ξ]
  exact (pow_le_pow_left₀ (by positivity) h m).trans_eq (mul_pow _ _ _)

theorem weighted_coordinate_bound (L : LogPlane →L[ℝ] ℝ) (m : ℕ) (ξ : LogPlane) :
    frequencyEnvelope m ξ * (1 + |L ξ|) ^ m ≤ max 1 ‖L‖ ^ m * fourierEnvelope ξ := by
  apply (mul_le_mul_of_nonneg_left (coordinate_polynomial_bound L m ξ)
    (frequencyEnvelope_nonneg m ξ)).trans_eq
  calc
    _ = max 1 ‖L‖ ^ m * ((1 + ‖ξ‖) ^ m * frequencyEnvelope m ξ) := by ring
    _ = _ := by rw [frequencyEnvelope_moment]

theorem weighted_coordinate_integrable (L : LogPlane →L[ℝ] ℝ) (m : ℕ) :
    Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ * (1 + |L ξ|) ^ m) := by
  apply (fourierEnvelope_integrable.const_mul (max 1 ‖L‖ ^ m)).mono_nonneg
    ((frequencyEnvelope_continuous m).mul
      ((continuous_const.add L.continuous.abs).pow m)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ =>
      mul_nonneg (frequencyEnvelope_nonneg m ξ)
        (pow_nonneg (add_nonneg zero_le_one (abs_nonneg (L ξ))) m)
  · exact Filter.Eventually.of_forall (weighted_coordinate_bound L m)

theorem polynomial_integral_bound (L : LogPlane →L[ℝ] ℝ) (m : ℕ)
    (B : ℝ) (hB : 0 ≤ B) (f : LogPlane → ℝ) (hf : ∀ ξ, 0 ≤ f ξ)
    (hb : ∀ ξ, f ξ ≤ B * (1 + |L ξ|) ^ m) :
    (∫ ξ : LogPlane, frequencyEnvelope m ξ * f ξ) ≤
      (max 1 ‖L‖ ^ m * ∫ ξ : LogPlane, fourierEnvelope ξ) * B := by
  calc
    _ ≤ ∫ ξ : LogPlane, B * (max 1 ‖L‖ ^ m * fourierEnvelope ξ) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ξ => mul_nonneg (frequencyEnvelope_nonneg m ξ) (hf ξ))
        ((fourierEnvelope_integrable.const_mul _).const_mul _)
      exact Filter.Eventually.of_forall fun ξ => by
        calc
          _ ≤ frequencyEnvelope m ξ * (B * (1 + |L ξ|) ^ m) :=
            mul_le_mul_of_nonneg_left (hb ξ) (frequencyEnvelope_nonneg m ξ)
          _ = B * (frequencyEnvelope m ξ * (1 + |L ξ|) ^ m) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_coordinate_bound L m ξ) hB
    _ = _ := by rw [integral_const_mul, integral_const_mul]; ring

/-- The final child seminorm is integrated against the actual second
Mellin density. The exact mass from Cauchy is included once. -/
def finalTestCost (s : Finset (ℕ × ℕ)) (a t τ : ℝ) : ℝ :=
  moment a t 0 * ∫ u : ℝ, ‖secondDensity a t u‖ *
    (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (FinalMellinTests.weightedTest 0 (u + τ))) ^ 2

theorem finalTestCost_nonneg (s : Finset (ℕ × ℕ)) (a t τ : ℝ) :
    0 ≤ finalTestCost s a t τ :=
  mul_nonneg (moment_nonneg _ _ _) (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem finalTestCost_bound (s : Finset (ℕ × ℕ)) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a t τ : ℝ,
      finalTestCost s a t τ ≤ C * cauchyCost a t k * (1 + |τ|) ^ k := by
  obtain ⟨m, B, hB, hb⟩ := FinalMellinTests.combined_frequency_seminorm_bound 0 s
  refine ⟨2 * m, B ^ 2, sq_nonneg B, fun a t τ => ?_⟩
  have hp (u : ℝ) :
      (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (FinalMellinTests.weightedTest 0 (u + τ))) ^ 2 ≤
      B ^ 2 * (1 + |u|) ^ (2 * m) * (1 + |τ|) ^ (2 * m) := by
    have hh := pow_le_pow_left₀ (apply_nonneg _ _) (hb u τ) 2
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hi : (∫ u : ℝ, ‖secondDensity a t u‖ *
      (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (FinalMellinTests.weightedTest 0 (u + τ))) ^ 2) ≤
      (B ^ 2 * (1 + |τ|) ^ (2 * m)) * moment a t (2 * m) := by
    calc
      _ ≤ ∫ u : ℝ, (B ^ 2 * (1 + |τ|) ^ (2 * m)) *
          ((1 + |u|) ^ (2 * m) * ‖secondDensity a t u‖) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun u => mul_nonneg (norm_nonneg _) (sq_nonneg _))
          ((moment_integrable a t (2 * m)).const_mul _)
        exact Filter.Eventually.of_forall fun u =>
          (mul_le_mul_of_nonneg_left (hp u) (norm_nonneg _)).trans_eq (by ring)
      _ = _ := integral_const_mul _ _
  exact (mul_le_mul_of_nonneg_left hi (moment_nonneg a t 0)).trans_eq (by
    dsimp only [cauchyCost]
    ring)

/-- The remaining first Fourier frequency is integrated uniformly,
with the two actual Mellin Cauchy costs and the original test squared. -/
theorem nested_cost_bound (a : ℝ) (k : ℕ) (L : LogPlane →L[ℝ] ℝ) :
    ∃ m : ℕ, ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2),
        (∫ ξ : LogPlane, frequencyEnvelope m ξ *
          ((∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
            (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * cauchyCost a (t + L ξ) k))) ≤
          C * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨m, s, A, hA, hb⟩ := two_pass_cauchyCost_bound a k
  let Q := max 1 ‖L‖ ^ m * ∫ ξ : LogPlane, fourierEnvelope ξ
  have hQ : 0 ≤ Q := mul_nonneg (by positivity) (integral_nonneg fourierEnvelope_nonneg)
  refine ⟨m, s, Q * A, mul_nonneg hQ hA, fun W hW => ?_⟩
  exact (polynomial_integral_bound L m
    (A * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2) (by positivity)
    (fun ξ => (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
      (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * cauchyCost a (t + L ξ) k))
    (fun ξ => mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (cauchyCost_nonneg _ _ _)))
    (fun ξ => hb W hW (L ξ))).trans_eq (by dsimp only [Q]; ring)

end HeckeSkeleton.Moments.MOM_INV_STEP.IteratedFrequencyBudget

end

