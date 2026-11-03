import HeckePort.Moments.Descent.IdealMasks
import HeckePort.Moments.Descent.DivisorSum

/-!
# Actual common radicals and the old-mask density

The common radical retains each common prime exactly once.  The old
squarefree mask divides that actual radical.  Counting and harmonic sums
of divisible ideals are proved by their genuine ideal quotients, so the
factor `1 / N(s)` is paid once and survives uniformly in the mask.

The radical facts follow the general ideal argument in openai/math
`Moments/RankinRadical.lean`; counting uses this repository's number-field
constant `idealCountConstant K`.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep.CommonSupportMass

open NumberField UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

def commonRadical (I J : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ∏ P ∈ primeSupport I ∩ primeSupport J, P

theorem commonRadical_ne_zero (I J : Ideal (𝓞 K)) : commonRadical I J ≠ 0 :=
  support_product_ne_zero Finset.inter_subset_left

theorem commonRadical_squarefree (I J : Ideal (𝓞 K)) : Squarefree (commonRadical I J) :=
  squarefree_support_product Finset.inter_subset_left

theorem commonRadical_support (I J : Ideal (𝓞 K)) :
    primeSupport (commonRadical I J) = primeSupport I ∩ primeSupport J := by
  unfold primeSupport commonRadical
  rw [factors_support_product Finset.inter_subset_left]
  simp [primeSupport]

theorem commonRadical_dvd (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    commonRadical I J ∣ I ∧ commonRadical I J ∣ J :=
  ⟨support_product_dvd hI Finset.inter_subset_left,
    support_product_dvd hJ Finset.inter_subset_right⟩

theorem commonRadical_norm_le (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (Ideal.absNorm (commonRadical I J) : ℝ) ≤
      min (Ideal.absNorm I : ℝ) (Ideal.absNorm J : ℝ) :=
  le_min (norm_le_of_dvd hI (commonRadical_dvd I J hI hJ).1)
    (norm_le_of_dvd hJ (commonRadical_dvd I J hI hJ).2)

theorem old_mask_dvd_commonRadical (s I J : Ideal (𝓞 K)) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J := by
  have hsub : primeSupport s ⊆ primeSupport I ∩ primeSupport J := by
    intro P hP
    exact Finset.mem_inter.mpr
      ⟨squarefree_divisor_support hI hs hsI hP, squarefree_divisor_support hJ hs hsJ hP⟩
  rw [← squarefree_support_product_self hs]
  exact Finset.prod_dvd_prod_of_subset _ _ id hsub

theorem divisor_quotient_norm_mul {s I : Ideal (𝓞 K)} (h : s ∣ I) :
    (Ideal.absNorm s : ℝ) * (Ideal.absNorm (idealQuotient s I) : ℝ) =
      (Ideal.absNorm I : ℝ) := by
  simpa only [map_mul, Nat.cast_mul] using
    congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ)) (idealQuotient_mul h)

theorem divisor_quotient_ne_zero {s I : Ideal (𝓞 K)} (hI : I ≠ 0) (h : s ∣ I) :
    idealQuotient s I ≠ 0 := by
  intro hz
  have he := idealQuotient_mul h
  rw [hz, mul_zero] at he
  exact hI he.symm

theorem divisor_quotient_injOn (S : Finset (Ideal (𝓞 K))) (s : Ideal (𝓞 K))
    (hdiv : ∀ I ∈ S, s ∣ I) : Set.InjOn (idealQuotient s) (S : Set (Ideal (𝓞 K))) := by
  intro I hI J hJ he
  calc
    I = s * idealQuotient s I := (idealQuotient_mul (hdiv I hI)).symm
    _ = s * idealQuotient s J := congrArg (fun Q => s * Q) he
    _ = J := idealQuotient_mul (hdiv J hJ)

/-- Actual divisible ideals have density `1 / N(s)`, including an empty
subunit range.  The constant is uniform in the divisor `s`. -/
theorem divisible_ideal_card (S : Finset (Ideal (𝓞 K))) (s : Ideal (𝓞 K))
    (hs : s ≠ 0) (hS : ∀ I ∈ S, I ≠ 0) (hdiv : ∀ I ∈ S, s ∣ I)
    (Y : ℝ) (hY : 0 ≤ Y) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ idealCountConstant K * Y / (Ideal.absNorm s : ℝ) := by
  have hsn : 0 < (Ideal.absNorm s : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs)
  let Q := S.image (idealQuotient s)
  have hcard : Q.card = S.card :=
    Finset.card_image_of_injOn (divisor_quotient_injOn S s hdiv)
  have hbound (J : Ideal (𝓞 K)) (hJ : J ∈ Q) :
      (Ideal.absNorm J : ℝ) ≤ Y / (Ideal.absNorm s : ℝ) := by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    apply (le_div_iff₀ hsn).mpr
    rw [mul_comm, divisor_quotient_norm_mul (hdiv I hI)]
    exact hN I hI
  by_cases hne : S.Nonempty
  · obtain ⟨I, hI⟩ := hne
    have hone : (1 : ℝ) ≤ Ideal.absNorm (idealQuotient s I) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (divisor_quotient_ne_zero (hS I hI) (hdiv I hI)))
    have hcutoff : 1 ≤ Y / (Ideal.absNorm s : ℝ) :=
      hone.trans (hbound _ (Finset.mem_image_of_mem _ hI))
    have hb := card_le_idealCountConstant K Q _ hcutoff hbound
    rw [hcard] at hb
    simpa only [mul_div_assoc] using hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg
      (mul_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) hY) hsn.le

/-- The genuine quotient map preserves the old-mask factor in harmonic
mass; the logarithm is the existing finite ideal inverse-norm sum. -/
theorem divisible_inverse_norm_sum (S : Finset (Ideal (𝓞 K))) (s : Ideal (𝓞 K))
    (hs : s ≠ 0) (hS : ∀ I ∈ S, I ≠ 0) (hdiv : ∀ I ∈ S, s ∣ I)
    (Y : ℝ) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (∑ I ∈ S, 1 / (Ideal.absNorm I : ℝ)) ≤
      2 * idealCountConstant K * (columnDyadicLength Y + 1 : ℝ) /
        (Ideal.absNorm s : ℝ) := by
  have hsn : (1 : ℝ) ≤ Ideal.absNorm s := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hs)
  let Q := S.image (idealQuotient s)
  have hQ0 (J : Ideal (𝓞 K)) (hJ : J ∈ Q) : J ≠ 0 := by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    exact divisor_quotient_ne_zero (hS I hI) (hdiv I hI)
  have hQN (J : Ideal (𝓞 K)) (hJ : J ∈ Q) : (Ideal.absNorm J : ℝ) ≤ Y := by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    calc
      _ ≤ (Ideal.absNorm s : ℝ) * Ideal.absNorm (idealQuotient s I) :=
        le_mul_of_one_le_left (Nat.cast_nonneg _) hsn
      _ = (Ideal.absNorm I : ℝ) := divisor_quotient_norm_mul (hdiv I hI)
      _ ≤ Y := hN I hI
  calc
    _ = ∑ I ∈ S, (1 / (Ideal.absNorm s : ℝ)) *
        (1 / (Ideal.absNorm (idealQuotient s I) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [one_div_mul_one_div, divisor_quotient_norm_mul (hdiv I hI)]
    _ = (1 / (Ideal.absNorm s : ℝ)) *
        ∑ I ∈ S, 1 / (Ideal.absNorm (idealQuotient s I) : ℝ) := by rw [Finset.mul_sum]
    _ = (1 / (Ideal.absNorm s : ℝ)) * ∑ J ∈ Q, 1 / (Ideal.absNorm J : ℝ) := by
      congr 1
      exact (Finset.sum_image
        (f := fun J : Ideal (𝓞 K) => 1 / (Ideal.absNorm J : ℝ))
        (divisor_quotient_injOn S s hdiv)).symm
    _ ≤ (1 / (Ideal.absNorm s : ℝ)) *
        (2 * idealCountConstant K * (columnDyadicLength Y + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_inverse_norm_sum Q Y hQ0 hQN)
        (one_div_nonneg.mpr (zero_le_one.trans hsn))
    _ = _ := by ring

theorem old_mask_radical_count {α : Type*} (S : Finset α) (I J : α → Ideal (𝓞 K))
    (s : Ideal (𝓞 K)) (hs : Squarefree s) (hs0 : s ≠ 0)
    (hI : ∀ a ∈ S, I a ≠ 0) (hJ : ∀ a ∈ S, J a ≠ 0)
    (hsi : ∀ a ∈ S, s ∣ I a) (hsj : ∀ a ∈ S, s ∣ J a)
    (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ a ∈ S, (Ideal.absNorm (commonRadical (I a) (J a)) : ℝ) ≤ Y) :
    ((S.image (fun a => commonRadical (I a) (J a))).card : ℝ) ≤
      idealCountConstant K * Y / (Ideal.absNorm s : ℝ) := by
  apply divisible_ideal_card _ s hs0
  · intro R hR
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hR
    exact commonRadical_ne_zero _ _
  · intro R hR
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hR
    exact old_mask_dvd_commonRadical s _ _ hs (hI a ha) (hJ a ha) (hsi a ha) (hsj a ha)
  · exact hY
  · intro R hR
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hR
    exact hN a ha

end HeckeSkeleton.Moments.EngineStep.CommonSupportMass

end

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.divisible_ideal_card
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.divisible_inverse_norm_sum
