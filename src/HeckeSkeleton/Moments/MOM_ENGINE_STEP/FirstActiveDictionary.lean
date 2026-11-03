import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonSupportSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass

/-!
# The actual active ideal and the normalized common mass

The active quotient in the first finite transform and the active radical
in the common-support mass are defined independently. This file identifies
them from the exact prime-power products.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments.Active

variable {K : Type} [Field K] [NumberField K]

private theorem ideal_powerProduct_count {ι : Type*}
    (P : ι → Ideal (𝓞 K)) (hP : ∀ i, Prime (P i)) (n : ι → ℕ)
    (S : Finset ι) (Q : Ideal (𝓞 K)) :
    (normalizedFactors (∏ i ∈ S, P i ^ n i)).count Q =
      ∑ i ∈ S, if P i = Q then n i else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    change (normalizedFactors (1 : Ideal (𝓞 K))).count Q = 0
    rw [normalizedFactors_one]
    rfl
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      normalizedFactors_mul (pow_ne_zero _ (hP a).ne_zero)
        (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hP i).ne_zero)),
      Multiset.count_add, ih, (hP a).irreducible.normalizedFactors_pow]
    simp only [normalize_eq, Multiset.count_replicate]

variable {A : SArithmeticData K}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primePowerProduct_prime_injective (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) : Function.Injective (fun i => (p i).val.asIdeal) := by
  intro i j hij
  apply hp
  exact Subtype.ext (HeightOneSpectrum.ext hij)

theorem primePowerProduct_count (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (n : ι → ℕ) (i : ι) :
    (normalizedFactors (primePowerProduct p n).val).count (p i).val.asIdeal = n i := by
  change (normalizedFactors (∏ j, (p j).val.asIdeal ^ n j)).count (p i).val.asIdeal = n i
  rw [ideal_powerProduct_count _ (fun j => (p j).val.prime)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun he => hji (primePowerProduct_prime_injective p hp he))
  · simp

theorem primePowerProduct_support (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (n : ι → ℕ) (hn : ∀ i, 0 < n i) :
    primeSupport (primePowerProduct p n).val =
      Finset.univ.image (fun i => (p i).val.asIdeal) := by
  ext Q
  change Q ∈ (normalizedFactors (primePowerProduct p n).val).toFinset ↔ _
  rw [Multiset.mem_toFinset, ← Multiset.count_pos]
  constructor
  · intro hQ
    by_contra hmem
    have hne (i : ι) : (p i).val.asIdeal ≠ Q := by
      intro he
      exact hmem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he⟩)
    change 0 < (normalizedFactors (∏ i, (p i).val.asIdeal ^ n i)).count Q at hQ
    rw [ideal_powerProduct_count _ (fun i => (p i).val.prime)] at hQ
    simp only [hne, if_false, Finset.sum_const_zero, lt_self_iff_false] at hQ
  · intro hQ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
    rw [primePowerProduct_count p hp n i]
    exact hn i

theorem netExponent_eq_zero_iff_mod_six (m n : ℕ) :
    netExponent m n = 0 ↔ m % 6 = n % 6 := by
  unfold netExponent
  omega

theorem firstActiveIdeal_eq_firstActiveRadical (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ) (hm : ∀ i, 0 < m i) :
    (firstActiveIdeal p m n).val =
      firstActiveRadical (primePowerProduct p m).val (primePowerProduct p n).val := by
  rw [firstActiveRadical, primePowerProduct_support p hp m hm,
    Finset.filter_image, Finset.prod_image (primePowerProduct_prime_injective p hp).injOn]
  simp_rw [primePowerProduct_count p hp m, primePowerProduct_count p hp n]
  change (∏ i : activeSupport Finset.univ m n, (p i.val).val.asIdeal ^ 1) = _
  simp only [pow_one]
  rw [Finset.prod_coe_sort (activeSupport Finset.univ m n)
    (fun i : ι => (p i).val.asIdeal)]
  apply Finset.prod_congr
  · ext i
    simp only [activeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      ne_eq, netExponent_eq_zero_iff_mod_six]
  · intro i _
    rfl

section Blocks

variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

theorem FirstCommonCharacterBlock.activeIdeal_eq
    (b : FirstCommonCharacterBlock fullI fullJ DE) :
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val =
      firstActiveRadical DE.1 DE.2 := by
  rw [firstActiveIdeal_eq_firstActiveRadical b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity b.left_positive, b.common_left, b.common_right]

theorem FirstCommonCharacterBlock.activeNorm_eq
    (b : FirstCommonCharacterBlock fullI fullJ DE) :
    A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) =
      (Ideal.absNorm (firstActiveRadical DE.1 DE.2) : ℝ) := by
  change (Ideal.absNorm (firstActiveIdeal b.primes b.leftMultiplicity
    b.rightMultiplicity).val : ℝ) = _
  rw [b.activeIdeal_eq]

theorem FirstCommonCharacterBlock.common_support_eq
    (b : FirstCommonCharacterBlock fullI fullJ DE) :
    primeSupport DE.1 = primeSupport DE.2 := by
  rw [← b.common_left, ← b.common_right,
    primePowerProduct_support b.primes b.primes_injective
      b.leftMultiplicity b.left_positive,
    primePowerProduct_support b.primes b.primes_injective
      b.rightMultiplicity b.right_positive]

theorem FirstCommonCharacterBlock.commonWeight_sqrt_formula
    (b : FirstCommonCharacterBlock fullI fullJ DE) (Z : ℝ) (hZ : 1 < Z) :
    firstCommonWeight Z DE.1 DE.2 =
      Real.sqrt (A.exteriorNorm
        (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) *
        Z ^ ((firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
            (idealLogLength Z
              (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val) +
          firstAllowance (idealLogLength Z DE.2) (idealLogLength Z DE.1)
            (idealLogLength Z
              (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val)) / 2) /
        (Real.sqrt (Ideal.absNorm DE.1 : ℝ) * Real.sqrt (Ideal.absNorm DE.2 : ℝ)) := by
  have hD : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hE : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  simpa only [Real.sqrt_eq_rpow, b.activeNorm_eq, b.activeIdeal_eq] using
    firstCommonWeight_norm_formula Z hZ DE.1 DE.2 hD hE

end Blocks

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstActiveIdeal_eq_firstActiveRadical
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.commonWeight_sqrt_formula

