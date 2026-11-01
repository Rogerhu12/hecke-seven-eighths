import ExpansionDetector.EulerDeletionNegative

/-! The deletion estimates on the project's actual height-one-spectrum
prime indices. Membership is only required to mean divisibility of the
complete row ideal; no ramification simplification is made. -/
noncomputable section
namespace ExpansionDetector.EulerDeletion
open ExpansionDetector.IdealCutoff IsDedekindDomain UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
variable {K : Type*} [Field K] [NumberField K]

lemma spectrum_image_subset_primeSupport (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ p ∈ T, p.asIdeal ∣ I) :
    T.image HeightOneSpectrum.asIdeal ⊆ primeSupport I := by
  intro P hP
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
  change p.asIdeal ∈ (normalizedFactors I).toFinset
  rw [Multiset.mem_toFinset, mem_normalizedFactors_iff hI]
  exact ⟨p.prime, hT p hp⟩

lemma spectrum_card_le_primeSupport (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ p ∈ T, p.asIdeal ∣ I) : T.card ≤ (primeSupport I).card := by
  have hc := Finset.card_le_card (spectrum_image_subset_primeSupport I hI T hT)
  rwa [Finset.card_image_of_injective _ HeightOneSpectrum.asIdeal_injective] at hc

theorem spectrum_card_power_le_norm (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ p ∈ T, p.asIdeal ∣ I) : (2 : ℝ) ^ T.card ≤ (Ideal.absNorm I : ℝ) := by
  calc
    _ ≤ (2 : ℝ) ^ (primeSupport I).card := pow_le_pow_right₀ (by norm_num)
      (spectrum_card_le_primeSupport I hI T hT)
    _ ≤ _ := by exact_mod_cast support_card_pow_le_norm I hI

lemma spectrum_norm_prod_le (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ p ∈ T, p.asIdeal ∣ I) :
    (∏ p ∈ T, (Ideal.absNorm p.asIdeal : ℝ)) ≤ (Ideal.absNorm I : ℝ) := by
  have hprod : (∏ P ∈ T.image HeightOneSpectrum.asIdeal, P) = ∏ p ∈ T, p.asIdeal := by
    exact Finset.prod_image (fun p _ q _ hpq => HeightOneSpectrum.asIdeal_injective hpq)
  have hn := divisor_norm_le hI (spectrum_image_subset_primeSupport I hI T hT)
  rw [hprod, map_prod] at hn
  exact_mod_cast hn

theorem spectrum_localMajorant_subpower (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ 0 →
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), (∀ p ∈ T, p.asIdeal ∣ I) →
      (∏ p ∈ T, localMajorant δ (Ideal.absNorm p.asIdeal : ℝ)) ≤
        C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := primeSupport_localMajorant_subpower (K := K) δ ε hδ hε
  refine ⟨C, hC, ?_⟩
  intro I hI T hT
  have he : (∏ P ∈ T.image HeightOneSpectrum.asIdeal, localMajorant δ (Ideal.absNorm P : ℝ)) =
      ∏ p ∈ T, localMajorant δ (Ideal.absNorm p.asIdeal : ℝ) :=
    Finset.prod_image (fun p _ q _ hpq => HeightOneSpectrum.asIdeal_injective hpq)
  rw [← he]
  have hmajor (P : Ideal (𝓞 K)) (hP : P ∈ primeSupport I) :
      1 ≤ localMajorant δ (Ideal.absNorm P : ℝ) := by
    apply one_le_localMajorant hδ
    have hn : (2 : ℝ) ≤ Ideal.absNorm P := by
      exact_mod_cast two_le_norm_of_prime (support_prime hP)
    linarith
  have hsub := spectrum_image_subset_primeSupport I hI T hT
  exact (Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    (fun P hP => zero_le_one.trans (hmajor P (hsub hP)))
    (fun P hP _ => hmajor P hP)).trans (hb I hI)

theorem spectrum_euler_positive_subpower (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ 0 →
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), (∀ p ∈ T, p.asIdeal ∣ I) →
      ∀ a : HeightOneSpectrum (𝓞 K) → ℂ, (∀ p ∈ T, ‖a p‖ ≤ 1) →
      ∀ s : ℂ, δ ≤ s.re →
      ‖∏ p ∈ T, (1 - a p * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))‖ ≤
        C * (Ideal.absNorm I : ℝ) ^ ε ∧
      ‖(∏ p ∈ T, (1 - a p * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹‖ ≤
        C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := spectrum_localMajorant_subpower (K := K) δ ε hδ hε
  refine ⟨C, hC, ?_⟩
  intro I hI T hT a ha s hs
  have hl (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ T) :=
    localEuler_norm_and_inverse_bound δ (Ideal.absNorm p.asIdeal : ℝ) hδ
      (by have hn := two_le_norm_of_prime p.prime; exact_mod_cast (by omega : 1 < Ideal.absNorm p.asIdeal))
      (a p) s (ha p hp) hs
  constructor
  · rw [norm_prod]
    apply (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) ?_).trans (hb I hI T hT)
    intro p hp
    simpa only [Complex.ofReal_natCast] using (hl p hp).1
  · rw [← Finset.prod_inv_distrib, norm_prod]
    apply (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) ?_).trans (hb I hI T hT)
    intro p hp
    simpa only [Complex.ofReal_natCast] using (hl p hp).2

theorem spectrum_euler_negative_subpower (η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ 0 →
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), (∀ p ∈ T, p.asIdeal ∣ I) →
      ∀ a : HeightOneSpectrum (𝓞 K) → ℂ, (∀ p ∈ T, ‖a p‖ ≤ 1) →
      ∀ s : ℂ, -η ≤ s.re →
      ‖∏ p ∈ T, (1 - a p * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))‖ ≤
        C * (Ideal.absNorm I : ℝ) ^ (η + ε) := by
  obtain ⟨C, hC, hcard⟩ := primeSupport_card_subpower (K := K) ε hε
  refine ⟨C, hC, ?_⟩
  intro I hI T hT a ha s hs
  have hNI : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hcardT : (2 : ℝ) ^ T.card ≤ C * (Ideal.absNorm I : ℝ) ^ ε :=
    (pow_le_pow_right₀ (by norm_num) (spectrum_card_le_primeSupport I hI T hT)).trans (hcard I hI)
  rw [norm_prod]
  calc
    _ ≤ ∏ p ∈ T, 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ η := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro p hp
      have hn : (1 : ℝ) ≤ Ideal.absNorm p.asIdeal := by
        have hh := two_le_norm_of_prime p.prime
        exact_mod_cast (by omega : 1 ≤ Ideal.absNorm p.asIdeal)
      simpa only [Complex.ofReal_natCast] using localEuler_negative_norm_bound η
        (Ideal.absNorm p.asIdeal : ℝ) hη hn (a p) s (ha p hp) hs
    _ = (2 : ℝ) ^ T.card * (∏ p ∈ T, (Ideal.absNorm p.asIdeal : ℝ)) ^ η := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg _) η]
    _ ≤ (C * (Ideal.absNorm I : ℝ) ^ ε) * (Ideal.absNorm I : ℝ) ^ η :=
      mul_le_mul hcardT
        (Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _))
          (spectrum_norm_prod_le I hI T hT) hη)
        (Real.rpow_nonneg (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _)) _) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hNI]
      congr 2
      ring

end ExpansionDetector.EulerDeletion
