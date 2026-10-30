import HeckePort.Moments.Descent.MarkedTwists

/-!
# Reflection of marked completed sums

Port of the formal part of openai/math `OAI/NumberTheory/DirichletL/Descent/MarkedReflection.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

openai applies the canonical smoothed reflection `completedT_canonical_smoothed_reflection`
(the theta reflection of the cubic Eisenstein field, via `fixedThetaQuotient`, `quotientTrace`
and `finiteTwistCusp`) to each twist `markTwist p T * Ψ` of the character and recombines the
twists with the signs `(-1) ^ |T|`.  The theta reflection is `ℤ[ω]`-specific (its general-field
analogue is the theta reflection of the skeleton), so it enters as the hypothesis `hrefl`: for
each twist `T` the completed sum is `scal * ∑_h coeff T h * ker h`.  Ported:

* `markTwist` (the coprimality-mask product `∏_{i ∈ T} [IsCoprime (P i) A]` as a function of the
  ideal) with `markTwist_norm` and `markTwist_mul`;
* `markedCompletedT_reflection_of_twists`: the signed recombination, which is the algebra at the
  end of `markedCompletedT_canonical_reflection` (with
  `markedThetaQuotient_twists` replaced by the coefficientwise identity `hcoeff`).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ι : Type*}

def markTwist (P : ι → Ideal (𝓞 K)) (T : Finset ι) (A : Ideal (𝓞 K)) : ℂ :=
  ∏ i ∈ T, if IsCoprime (P i) A then (1 : ℂ) else 0

theorem markTwist_norm (P : ι → Ideal (𝓞 K)) (T : Finset ι) (A : Ideal (𝓞 K)) :
    ‖markTwist P T A‖ ≤ 1 := by
  unfold markTwist
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  by_cases h : IsCoprime (P i) A <;> simp [h]

theorem markTwist_mul (P : ι → Ideal (𝓞 K)) (T : Finset ι) (A B : Ideal (𝓞 K)) :
    markTwist P T (A * B) = markTwist P T A * markTwist P T B := by
  unfold markTwist
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [IsCoprime.mul_right_iff]
  by_cases hA : IsCoprime (P i) A <;> by_cases hB : IsCoprime (P i) B <;> simp [hA, hB]

variable {s : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}

/-- openai `markedCompletedT_canonical_reflection`, the recombination of the twisted
reflections.  `hrefl T` is the reflection of the completed sum marked by `markTwist P T`;
`hcoeff` says that the coefficient of the marked theta function is the signed sum of those of
its twists. -/
theorem markedCompletedT_reflection_of_twists (hs : CompletedSummand s)
    (S : Finset ι) (P : ι → Ideal (𝓞 K)) (hP : ∀ i ∈ S, Prime (P i))
    {H : Type*} [Fintype H] (scal : ℂ) (coeff : Finset ι → H → ℂ) (mcoeff : H → ℂ)
    (ker : H → ℂ)
    (hrefl : ∀ T ∈ S.powerset,
      markedCompletedT s (markTwist P T) = scal * ∑ h, coeff T h * ker h)
    (hcoeff : ∀ h, mcoeff h = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * coeff T h) :
    markedCompletedT s (fun A => ∏ i ∈ S, if P i ∣ A then (1 : ℂ) else 0) =
      scal * ∑ h, mcoeff h * ker h := by
  rw [markedCompletedT_prime_product_twists hs S P hP]
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (scal * ∑ h, coeff T h * ker h) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [← hrefl T hT]
      rfl
    _ = scal * ∑ h, (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * coeff T h) * ker h := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro T _
      ring
    _ = _ := by simp_rw [hcoeff]

end HeckePort.Moments

end
