import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMaskCardinality
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonSupportSource

/-!
# The actual first-block mask has a uniform small-power cardinality

The first transformed mask is the union of the original mask with the
principal common primes. It need not be a subset of the original mask.
The new primes inject into the original complete common ideal, so their
Boolean subsets cost its divisor count. This proof keeps the full union
and chooses the small-power constant before the source block.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments.Active UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {ι κ : Type*}
variable {I : ι → A.Exterior} {J : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock I J DE)

/-- The individual original common primes identify an actual divisor
of the complete common ideal. No support cardinality is assumed. -/
def originalCommonPrimeData :
    OriginalMaskPrimeData (Finset.univ : Finset (Fin b.primeCount)) DE.1 where
  prime i := (b.primes i).val
  injective := by
    intro i _ j _ hij
    exact b.primes_injective (Subtype.ext hij)
  divides i _ := by
    have hD : DE.1 ≠ 0 := by
      rw [← b.common_left]
      exact (primePowerProduct b.primes b.leftMultiplicity).property.1
    apply (prime_mem_support_iff_dvd _ DE.1 (b.primes i).val.prime hD).mp
    rw [← b.common_left,
      primePowerProduct_support b.primes b.primes_injective b.leftMultiplicity b.left_positive]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

theorem principalMask_card_le :
    (firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity).card ≤
      b.primeCount := by
  apply Finset.card_image_le.trans
  simpa only [Fintype.card_fin] using
    (Finset.card_le_univ (principalSupport Finset.univ b.leftMultiplicity b.rightMultiplicity))

theorem mask_card_le (M : Finset (HeightOneSpectrum A.R)) :
    (b.mask M).card ≤ M.card + b.primeCount := by
  exact (Finset.card_union_le M _).trans (Nat.add_le_add_left b.principalMask_card_le _)

/-- Every actual first-mask divisor is paid by the two original ideal
divisor counts. This includes overlapping masks and empty supports. -/
theorem mask_powerset_card_le
    (M : Finset (HeightOneSpectrum A.R)) (R : Ideal (𝓞 K)) (hR : R ≠ 0)
    (W : OriginalMaskPrimeData M R) :
    (b.mask M).powerset.card ≤ idealDivisorCount R * idealDivisorCount DE.1 := by
  have hD : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hcommon : 2 ^ b.primeCount ≤ idealDivisorCount DE.1 := by
    simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] using
      b.originalCommonPrimeData.powerset_card_le_divisorCount hD
  have hold : 2 ^ M.card ≤ idealDivisorCount R := by
    simpa only [Finset.card_powerset] using W.powerset_card_le_divisorCount hR
  rw [Finset.card_powerset]
  calc
    _ ≤ 2 ^ (M.card + b.primeCount) :=
      Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (b.mask_card_le M)
    _ = 2 ^ M.card * 2 ^ b.primeCount := pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul hold hcommon

end FirstCommonCharacterBlock

/-- The same fixed constant works for every original block, all of its
actual mask divisors, and both the direct and amplified entrances. -/
theorem first_block_mask_labels_subpower (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
    ∀ {A : SArithmeticData K} {ι κ : Type*}
      {I : ι → A.Exterior} {J : κ → A.Exterior}
      {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
      (b : FirstCommonCharacterBlock I J DE),
    ∀ (M : Finset (HeightOneSpectrum A.R)) (R : Ideal (𝓞 K)), R ≠ 0 →
      (Ideal.absNorm R : ℝ) ≤ Z ^ B → (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B →
      OriginalMaskPrimeData M R → ((b.mask M).powerset.card : ℝ) ≤ C * Z ^ ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨C, hC, hb⟩ := support_tuple_multiplicity_subpower (K := K) 1 B (ε / 2) hB hhalf
  refine ⟨C * C, mul_pos hC hC, ?_⟩
  intro Z hZ A ι κ I J DE b M R hR hNR hND W
  have hRbound : (idealDivisorCount R : ℝ) ≤ C * Z ^ (ε / 2) := by
    simpa only [pow_one] using hb Z hZ R hNR
  have hDbound : (idealDivisorCount DE.1 : ℝ) ≤ C * Z ^ (ε / 2) := by
    simpa only [pow_one] using hb Z hZ DE.1 hND
  have hcard : ((b.mask M).powerset.card : ℝ) ≤
      (idealDivisorCount R : ℝ) * (idealDivisorCount DE.1 : ℝ) := by
    exact_mod_cast b.mask_powerset_card_le M R hR W
  calc
    _ ≤ (idealDivisorCount R : ℝ) * (idealDivisorCount DE.1 : ℝ) := hcard
    _ ≤ (C * Z ^ (ε / 2)) * (C * Z ^ (ε / 2)) :=
      mul_le_mul hRbound hDbound (Nat.cast_nonneg _) (by positivity)
    _ = (C * C) * (Z ^ (ε / 2) * Z ^ (ε / 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hZ), show ε / 2 + ε / 2 = ε by ring]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.mask_powerset_card_le
#print axioms HeckeSkeleton.Moments.EngineStep.first_block_mask_labels_subpower
