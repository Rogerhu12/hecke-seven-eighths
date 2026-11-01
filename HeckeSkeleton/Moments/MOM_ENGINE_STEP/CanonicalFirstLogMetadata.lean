import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSharpFirstFrequencies
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstResidualProfileCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary

/-!
# Original ideal lengths in the actual first Poisson weight

The mask generator and active Gauss column already have arithmetic
norm identities. These lemmas turn those identities into powers of
the original ideal lengths. The resulting first weight formula uses
the actual selected physical divisor and active common radical.
-/

noncomputable section
open scoped Classical NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} [IsPrincipalIdealRing A.R]

namespace CanonicalFirstLog

/-- The actual Poisson mask generator has the norm of its original
physical divisor, expressed in logarithmic coordinates. -/
theorem maskNorm_eq_original_length
    (D : Finset (HeightOneSpectrum A.R)) (Z : ℝ) (hZ : 1 < Z) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val =
      Z ^ idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val := by
  rw [rpow_idealLogLength Z hZ _
    (firstPhysicalDivisorIdeal (A := A) D).property.1]
  exact (firstPhysicalDivisorIdeal_norm (A := A) D).symm

end CanonicalFirstLog

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces} {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock fullI fullJ DE)

/-- The actual active column uses a generator of the active ideal.
Its norm is independent of the chosen generator. -/
theorem activeColumn_norm_eq
    (C : A.GeneralArithmeticContext σ η hS) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity).modulus,
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity).nonzero⟩).val =
      (Ideal.absNorm (firstActiveRadical DE.1 DE.2) : ℝ) := by
  have hN := generates_sIntegerElementNorm
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity)
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    ⟨(actualActiveColumn hΓ C b.primes b.primes_injective
        b.leftMultiplicity b.rightMultiplicity).modulus,
      (actualActiveColumn hΓ C b.primes b.primes_injective
        b.leftMultiplicity b.rightMultiplicity).nonzero⟩).val =
      A.exteriorNorm
        (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) at hN
  exact hN.trans b.activeNorm_eq

/-- The active length is the length of the actual active common
radical, with no transformed norm identity supplied as an input. -/
theorem activeColumn_norm_eq_original_length
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 < Z) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity).modulus,
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity).nonzero⟩).val =
      Z ^ idealLogLength Z (firstActiveRadical DE.1 DE.2) := by
  rw [rpow_idealLogLength Z hZ _ (firstActiveRadical_ne_zero _ _)]
  exact b.activeColumn_norm_eq hΓ C

variable [Γ.FiniteIndex]

/-- The first row weight in the original ideal coordinates. Only the
original radius coordinate remains an input; both arithmetic norm
coordinates are computed internally. -/
theorem rowWeightBound_eq_original_ideal_lengths
    (C : A.GeneralArithmeticContext σ η hS)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (Z m δ : ℝ) (hZ : 1 < Z) (hradius : radius.val = Z ^ (-m)) :
    CanonicalFirstLog.rowWeightBound
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) radius D δ =
      orbitalFieldFactor K *
        Z ^ (m - idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val -
          idealLogLength Z (firstActiveRadical DE.1 DE.2) +
          δ * (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val +
            idealLogLength Z (firstActiveRadical DE.1 DE.2) - m)) := by
  exact CanonicalFirstLog.rowWeightBound_eq_original_lengths
    (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity) radius D Z m
    (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val)
    (idealLogLength Z (firstActiveRadical DE.1 DE.2)) δ
    (zero_lt_one.trans hZ) hradius
    (CanonicalFirstLog.maskNorm_eq_original_length (A := A) D Z hZ)
    (b.activeColumn_norm_eq_original_length hΓ C Z hZ)

end FirstCommonCharacterBlock
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstLog.maskNorm_eq_original_length
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.activeColumn_norm_eq
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.activeColumn_norm_eq_original_length
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.rowWeightBound_eq_original_ideal_lengths
