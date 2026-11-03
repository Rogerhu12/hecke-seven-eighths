import HeckePort.CenteredMoment.Cancellation
import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound

/-!
# Trivial bounds for masked ideal sums

Port of `OAI.SevenEighths.CenteredMomentCounting` (openai/math,
`OAI/NumberTheory/DirichletL/Moments/Counting.lean`, revision `fd4aeeb2`).
openai counts the ideals of norm at most `H` in `ℤ[ω]` by `128 H`; over a general
field the constant is `idealCountConstant K`, from the upstream
`exists_ideal_count_bound`.
-/

noncomputable section

namespace HeckePort.CenteredMomentCounting

open scoped NumberField Classical BigOperators
open DedekindZetaZeroFree.LargeSieve HeckePort.CenteredMomentCancellation

variable (K : Type*) [Field K] [NumberField K]

/-- A constant `C ≥ 1` with at most `C X` ideals of norm at most `X ≥ 1`. -/
def idealCountConstant : ℝ := Classical.choose (exists_ideal_count_bound K)

theorem one_le_idealCountConstant : 1 ≤ idealCountConstant K :=
  (Classical.choose_spec (exists_ideal_count_bound K)).1

theorem card_le_idealCountConstant (s : Finset (Ideal (𝓞 K))) (H : ℝ) (hH : 1 ≤ H)
    (hs : ∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ H) :
    (s.card : ℝ) ≤ idealCountConstant K * H := by
  have hsub : s ⊆ boundedNormIdeals K H := fun I hI => mem_boundedNormIdeals.mpr (hs I hI)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    ((Classical.choose_spec (exists_ideal_count_bound K)).2 H hH)

variable {K}

theorem norm_tsum_ideal_ball (f : Ideal (𝓞 K) → ℂ) (H M : ℝ)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hzero : f ⊥ = 0)
    (hbound : ∀ I, ‖f I‖ ≤ M)
    (hsupport : ∀ I, f I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ H) :
    ‖∑' I : Ideal (𝓞 K), f I‖ ≤ idealCountConstant K * M * H := by
  classical
  have hC := one_le_idealCountConstant K
  have hfinite : (Function.support f).Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Nat.ceil H)).subset
    intro I hI
    exact_mod_cast (hsupport I hI).trans (Nat.le_ceil H)
  let S := hfinite.toFinset
  have hmem (I : Ideal (𝓞 K)) : I ∈ S ↔ f I ≠ 0 := hfinite.mem_toFinset
  have htsum : (∑' I : Ideal (𝓞 K), f I) = ∑ I ∈ S, f I := by
    exact tsum_eq_sum (fun I hI => not_ne_iff.mp (mt (hmem I).mpr hI))
  rw [htsum]
  by_cases hS : S.Nonempty
  · obtain ⟨I, hI⟩ := hS
    have hI0 : I ≠ ⊥ := by intro h; exact (hmem I).mp hI (h ▸ hzero)
    have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hI0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH1 : 1 ≤ H := hn.trans (hsupport I ((hmem I).mp hI))
    have hcount := card_le_idealCountConstant K S H hH1
      (fun J hJ => hsupport J ((hmem J).mp hJ))
    calc
      _ ≤ ∑ I ∈ S, ‖f I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ S, M := Finset.sum_le_sum (fun I _ => hbound I)
      _ = (S.card : ℝ) * M := by simp
      _ ≤ (idealCountConstant K * H) * M := mul_le_mul_of_nonneg_right hcount hM
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hC) hM) hH

omit [NumberField K] in
theorem masked_coefficient_norm_le_one (Ψ : Ideal (𝓞 K) → ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1)
    (R I : Ideal (𝓞 K)) :
    ‖(if IsCoprime I R then (1 : ℂ) else 0) * Ψ I‖ ≤ 1 := by
  split_ifs
  · simpa only [one_mul] using hΨ I
  · simp only [zero_mul, norm_zero, zero_le_one]

theorem maskedSum_absolute (Ψ : Ideal (𝓞 K) → ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (b M X : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hW : ∀ y, ‖W y‖ ≤ M) (hs : Function.support W ⊆ Set.Iic b) :
    ‖maskedSum Ψ R W X‖ ≤ (idealCountConstant K * b * M) * X := by
  have h := norm_tsum_ideal_ball
    (fun I => (if IsCoprime I R then (1 : ℂ) else 0) *
      (Ψ I * W ((Ideal.absNorm I : ℝ) / X)))
    (b * X) M (mul_nonneg hb hX.le) hM
    (by simp only [hΨ0, zero_mul, mul_zero])
    (by
      intro I
      rw [← mul_assoc, norm_mul]
      exact (mul_le_mul (masked_coefficient_norm_le_one Ψ hΨ R I)
        (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
    (by
      intro I hI
      have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
        intro hz
        exact hI (by simp only [hz, mul_zero])
      exact (div_le_iff₀ hX).mp (hs hw))
  change ‖maskedSum Ψ R W X‖ ≤ _ at h
  convert h using 1 ; ring

theorem norm_linear_coefficient_le (S : ℝ → ℂ) (v : ℂ) (C E : ℝ) (hE : 0 ≤ E)
    (herror : ∀ X : ℝ, 0 < X → ‖S X - (X : ℂ) * v‖ ≤ E)
    (habsolute : ∀ X : ℝ, 0 < X → ‖S X‖ ≤ C * X) : ‖v‖ ≤ C := by
  by_contra hn
  have hδ : 0 < ‖v‖ - C := sub_pos.mpr (lt_of_not_ge hn)
  let X := (E + 1) / (‖v‖ - C)
  have hX : 0 < X := div_pos (by linarith) hδ
  have heq : X * (‖v‖ - C) = E + 1 := div_mul_cancel₀ _ hδ.ne'
  have h := norm_le_norm_sub_add ((X : ℂ) * v) (S X)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hX.le, norm_sub_rev] at h
  have ha := habsolute X hX
  have hb := herror X hX
  nlinarith

end HeckePort.CenteredMomentCounting
