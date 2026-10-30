import HeckePort.Moments.Descent.IdealMasks

/-!
# Bounds for prime marks over pairwise coprime primes

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/MarkBounds.lean`
(revision `fd4aeeb2`).

openai indexes the pool by elements `p i : ℤ[ω]` with `span {p i}` maximal and pairwise
coprime; here the pool is given directly by maximal ideals `P i` of `𝓞 K`
(`span {p i}` becomes `P i`, and `primeProductNorm p U` becomes `N(∏ i ∈ U, P i)`).
The constant depends on `K` through the upstream divisor bound.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum

variable {K : Type*} [Field K] [NumberField K]

theorem primeSupport_prod_pool {ι : Type*} (P : ι → Ideal (𝓞 K))
    (hP0 : ∀ i, P i ≠ ⊥) [∀ i, (P i).IsMaximal] (U : Finset ι) :
    primeSupport (∏ i ∈ U, P i) = U.image P := by
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (hP0 i) inferInstance
  have hne : (∏ i ∈ U, P i) ≠ ⊥ :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hP0 i)
  ext Q
  rw [Finset.mem_image]
  constructor
  · intro hQ
    have hQp : Prime Q := support_prime hQ
    have hdvd : Q ∣ ∏ i ∈ U, P i := (prime_mem_support_iff_dvd Q _ hQp hne).mp hQ
    obtain ⟨i, hi, hQi⟩ := (Prime.dvd_finset_prod_iff hQp _).mp hdvd
    refine ⟨i, hi, ?_⟩
    have hasc : Associated Q (P i) := hQp.associated_of_dvd (hprime i) hQi
    exact (associated_iff_eq.mp hasc).symm
  · rintro ⟨i, hi, rfl⟩
    exact (prime_mem_support_iff_dvd _ _ (hprime i) hne).mpr (Finset.dvd_prod_of_mem _ hi)

theorem finite_primeSupport_card {ι : Type*} (P : ι → Ideal (𝓞 K))
    (hP0 : ∀ i, P i ≠ ⊥) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (U : Finset ι) :
    (primeSupport (∏ i ∈ U, P i)).card = U.card := by
  rw [primeSupport_prod_pool P hP0 U]
  apply Finset.card_image_of_injOn
  intro i _ j _ hij
  by_contra hne
  have hc : IsCoprime (P i) (P j) := hcop hne
  rw [hij] at hc
  exact (inferInstance : (P j).IsMaximal).ne_top (Ideal.isUnit_iff.mp (isCoprime_self.mp hc))

theorem finite_primeMark_small_power (K : Type*) [Field K] [NumberField K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (P : ι → Ideal (𝓞 K)) (_hP : ∀ i, P i ≠ ⊥) [∀ i, (P i).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime P))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ U : Finset ι,
      ‖primeMark slots lists a U‖ ≤ C * (Ideal.absNorm (∏ i ∈ U, P i) : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := prime_support_subsets_bound K ε hε
  refine ⟨C, hC, ?_⟩
  intro ι σ _ _ P hP _ hcop slots lists a hslots ha U
  have hI : (∏ i ∈ U, P i) ≠ ⊥ := Finset.prod_ne_zero_iff.mpr (fun i _ => hP i)
  have hh := hb _ hI
  rw [finite_primeSupport_card P hP hcop U] at hh
  exact (primeMark_norm_le_divisor_count slots lists a U hslots ha).trans hh

theorem finite_primeMark_extracted_bound (K : Type*) [Field K] [NumberField K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (P : ι → Ideal (𝓞 K)) (_hP : ∀ i, P i ≠ ⊥) [∀ i, (P i).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime P))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ A U : Finset ι,
      ‖primeMark slots lists a (A ∪ U)‖ ≤
        (2 : ℝ) ^ A.card * C * (Ideal.absNorm (∏ i ∈ U, P i) : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := prime_support_subsets_bound K ε hε
  refine ⟨C, hC, ?_⟩
  intro ι σ _ _ P hP _ hcop slots lists a hslots ha A U
  have hI : (∏ i ∈ U, P i) ≠ ⊥ := Finset.prod_ne_zero_iff.mpr (fun i _ => hP i)
  have hh := hb _ hI
  rw [finite_primeSupport_card P hP hcop U] at hh
  calc
    _ ≤ (2 : ℝ) ^ (A ∪ U).card := primeMark_norm_le_divisor_count _ _ _ _ hslots ha
    _ ≤ (2 : ℝ) ^ (A.card + U.card) := pow_le_pow_right₀ (by norm_num) (Finset.card_union_le _ _)
    _ = (2 : ℝ) ^ A.card * (2 : ℝ) ^ U.card := pow_add _ _ _
    _ ≤ (2 : ℝ) ^ A.card * (C * (Ideal.absNorm (∏ i ∈ U, P i) : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end HeckePort.Moments

end
