import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePoissonSource
import HeckePort.Moments.Descent.IdealMasks

/-!
# Uniform counting of the actual localized Poisson masks

Ordinary support primes inject into their ideal prime support. Localization
does not increase cardinality, and the complementary principal mask is
counted from the original four source ideals. Constants are chosen before
all source ideals and external punctures.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.MaskCounting

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open ActualFiniteSource PrimitivePoissonSource ConductorMasks LocalizedMasks
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

theorem support_card_le (P : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hP : ∀ p ∈ P, p.asIdeal ∣ I) :
    P.card ≤ (primeSupport I).card := by
  let f : P → primeSupport I := fun p =>
    ⟨p.val.asIdeal, (prime_mem_support_iff_dvd p.val.asIdeal I p.val.prime hI).mpr
      (hP p.val p.property)⟩
  have hf : Function.Injective f := by
    intro p q he
    exact Subtype.ext (HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val he))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

theorem localized_support_card_le (P : Finset (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ p ∈ P, p ∉ Sset) :
    (localizeSupportedMask K Sset P hP).card ≤ P.card := by
  unfold localizeSupportedMask
  exact (Finset.card_image_le).trans_eq Finset.card_attach

theorem principalMask_card_le (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    (principalMask K S B t).card ≤ B.support.card := by
  exact (localized_support_card_le K S _ _).trans (Finset.card_filter_le _ _)

/-- The external support is the literal localized support of I; the
principal support is derived from the actual block and is bounded by J. -/
theorem exists_localized_union_mask_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : Finset (HeightOneSpectrum (𝓞 K))) (hP : ∀ p ∈ P, p ∉ Sset)
      (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
      (I J : Ideal (𝓞 K)),
      I ≠ 0 → J ≠ 0 →
      (∀ p ∈ P, p.asIdeal ∣ I) →
      (∀ p ∈ B.support, p.asIdeal ∣ J) →
      (2 : ℝ) ^ (localizeSupportedMask K Sset P hP ∪ principalMask K S B t).card ≤
        C * ((I.absNorm : ℝ) * (J.absNorm : ℝ)) ^ ε := by
  obtain ⟨A₀, hA₀, hbound⟩ := prime_support_subsets_bound K ε hε
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hb (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
      (2 : ℝ) ^ (primeSupport I).card ≤ A * (I.absNorm : ℝ) ^ ε :=
    (hbound I hI).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  refine ⟨A * A, one_le_mul_of_one_le_of_one_le hA hA, ?_⟩
  intro P hP B t I J hI hJ hPI hBJ
  have hc : (localizeSupportedMask K Sset P hP ∪ principalMask K S B t).card ≤
      (primeSupport I).card + (primeSupport J).card :=
    (Finset.card_union_le _ _).trans
      (add_le_add
        ((localized_support_card_le K S P hP).trans (support_card_le K P I hI hPI))
        ((principalMask_card_le K S B t).trans (support_card_le K B.support J hJ hBJ)))
  calc
    _ ≤ (2 : ℝ) ^ ((primeSupport I).card + (primeSupport J).card) :=
      pow_le_pow_right₀ (by norm_num) hc
    _ = (2 : ℝ) ^ (primeSupport I).card * (2 : ℝ) ^ (primeSupport J).card := pow_add _ _ _
    _ ≤ (A * (I.absNorm : ℝ) ^ ε) * (A * (J.absNorm : ℝ) ^ ε) :=
      mul_le_mul (hb I hI) (hb J hJ) (by positivity) (by positivity)
    _ = (A * A) * ((I.absNorm : ℝ) * (J.absNorm : ℝ)) ^ ε := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

theorem pairSupport_dvd_product (n₁ n₂ b₁ b₂ : Ext)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (pairSupport K S D n₁ n₂ b₁ b₂).support) :
    p.asIdeal ∣ b₁.val.val * b₂.val.val * n₁.val.val * n₂.val.val := by
  rcases (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mp hp with h | h | h | h
  · exact (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _) _)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
  · exact dvd_mul_of_dvd_right h _

/-- The complete real Poisson mask of the original pair is counted
without an assumed mask-size estimate. -/
theorem exists_actual_pair_mask_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : Finset (HeightOneSpectrum (𝓞 K))) (hP : ∀ p ∈ P, p ∉ Sset)
      (Q : Ideal (𝓞 K)), Q ≠ 0 →
      (∀ p ∈ P, p.asIdeal ∣ Q) →
      ∀ n₁ n₂ b₁ b₂ : Ext,
      (2 : ℝ) ^ (localizeSupportedMask K Sset P hP ∪
        principalMask K S (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂)).card ≤
        C * ((Q.absNorm : ℝ) *
          ((b₁.val.val * b₂.val.val * n₁.val.val * n₂.val.val).absNorm : ℝ)) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := exists_localized_union_mask_bound K S ε hε
  refine ⟨C, hC, ?_⟩
  intro P hP Q hQ hPQ n₁ n₂ b₁ b₂
  apply hbound P hP (pairSupport K S D n₁ n₂ b₁ b₂)
    (pairExponent K S n₁ n₂ b₁ b₂) Q
    (b₁.val.val * b₂.val.val * n₁.val.val * n₂.val.val) hQ
  · exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (nonZeroDivisors.coe_ne_zero b₁.val)
        (nonZeroDivisors.coe_ne_zero b₂.val)) (nonZeroDivisors.coe_ne_zero n₁.val))
      (nonZeroDivisors.coe_ne_zero n₂.val)
  · exact hPQ
  · exact pairSupport_dvd_product K S D n₁ n₂ b₁ b₂

end HeckeSkeleton.Moments.MOM_INV_STEP.MaskCounting

end
