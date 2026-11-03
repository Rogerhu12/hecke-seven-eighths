import HeckePort.Moments.Descent.MarkedFourier

/-!
# Marked completed sums as twisted completed sums

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/MarkedTwists.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

In openai `markedCompletedT Ψ W X d` is the completed sum with the summand depending on the
Hecke character `Ψ`, and `completedT (φ * Ψ)` the same sum with the character twisted by the
monoid homomorphism `φ`.  As in `Descent/Completion` the summand is the abstract function
`s : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ`; the relation "twisting `Ψ` by `φ` multiplies the summand at
`(I, J)` by `φ (I * J ^ 3)`" (openai's `summand_mul_fixed_twist` together with
`primaryGenerator_mul`) is the explicit hypothesis `hs'` of `markedCompletedT_monoid`.

* `markedCompletedT_monoid`: the twisted summand `s'` satisfies `s' I J = s I J * φ (I * J ^ 3)`.
* `whole_prime_mark_eq_mask_complement`: for a prime ideal, divisibility is `1 - [coprime]`
  (openai uses `coprimalityMask p (primaryGenerator A)`; the mask on ideals is
  `if IsCoprime P A then 1 else 0`).
* `markedCompletedT_prime_product_twists`: the product of prime marks is the signed sum of
  completed sums marked by the coprimality masks.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- For a prime ideal `P`, `IsCoprime P A` is `¬ P ∣ A`. -/
theorem prime_isCoprime_iff_not_dvd (P A : Ideal (𝓞 K)) (hP : Prime P) :
    IsCoprime P A ↔ ¬ P ∣ A := by
  have : P.IsPrime := Ideal.isPrime_of_prime hP
  have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP.ne_zero
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.dvd_iff_le]
  constructor
  · intro h hle
    rw [sup_eq_left.mpr hle] at h
    exact hmax.ne_top h
  · intro h
    exact hmax.out.2 _ (lt_of_le_of_ne le_sup_left (fun he => h (sup_eq_left.mp he.symm)))

variable {s : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}

/-- openai `markedCompletedT_monoid`: marking by `φ` equals twisting the summand by `φ`. -/
theorem markedCompletedT_monoid (φ : Ideal (𝓞 K) → ℂ) (s' : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hs' : ∀ I J, s' I J = s I J * φ (I * J ^ 3)) :
    markedCompletedT s φ = markedCompletedT s' (fun _ => 1) := by
  unfold markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [hs' I J, mul_one]

theorem whole_prime_mark_eq_mask_complement (P : Ideal (𝓞 K)) (hP : Prime P)
    (A : Ideal (𝓞 K)) :
    (if P ∣ A then (1 : ℂ) else 0) = 1 - (if IsCoprime P A then 1 else 0) := by
  rw [prime_isCoprime_iff_not_dvd P A hP]
  by_cases h : P ∣ A <;> simp [h]

theorem markedCompletedT_prime_product_twists (hs : CompletedSummand s) {ι : Type*}
    (S : Finset ι) (P : ι → Ideal (𝓞 K)) (hP : ∀ i ∈ S, Prime (P i)) :
    markedCompletedT s (fun A => ∏ i ∈ S, if P i ∣ A then (1 : ℂ) else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        markedCompletedT s (fun A => ∏ i ∈ T, if IsCoprime (P i) A then (1 : ℂ) else 0) := by
  have he : ∀ A : Ideal (𝓞 K),
      (∏ i ∈ S, if P i ∣ A then (1 : ℂ) else 0) =
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          ∏ i ∈ T, if IsCoprime (P i) A then (1 : ℂ) else 0 := by
    intro A
    calc
      _ = ∏ i ∈ S, (1 - if IsCoprime (P i) A then (1 : ℂ) else 0) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact whole_prime_mark_eq_mask_complement (P i) (hP i hi) A
      _ = _ := by
        rw [Finset.prod_sub]
        simp
  simp_rw [he]
  rw [markedCompletedT_finset_sum hs S.powerset]
  apply Finset.sum_congr rfl
  intro T hT
  exact markedCompletedT_const_mul _ _

end HeckePort.Moments

end
