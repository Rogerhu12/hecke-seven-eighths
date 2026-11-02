import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstRowWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

set_option linter.unusedSectionVars false

/-!
# Actual first-mask and modulus windows from the original full columns

An empty initial parent mask still leaves the actual principal-prime
mask of the common block.  Every divisor of that mask divides the
original common-left generator.  Its norm is therefore at most the
norm of the same common-left ideal.

The original first periodic modulus is the product of the two residual
generators and the active generator.  The latter ideal divides the
common-left ideal.  The reconstruction identities then bound this
actual modulus by the product of the two original full-column norms.
These bounds are used only for the uniform pool and physical-cutoff
windows, and do not change any sharp allowance exponent.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

/-- Divisibility of the original nonzero S-integers bounds their actual
norms.  The quotient has norm at least one; no choice of associate is
needed. -/
theorem sIntegerElementNorm_dvd_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (a b : NonzeroRingElements (S.integer K)) (hab : a.val ∣ b.val) :
    (sIntegerElementNorm K S a).val ≤ (sIntegerElementNorm K S b).val := by
  sorry

section CommonBlock

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η hS)

theorem FirstCommonCharacterBlock.prime_dvd_commonLeft (i : Fin b.primeCount) :
    (b.primes i).val.asIdeal ∣ b.commonLeftIdeal.val := by
  sorry

theorem FirstCommonCharacterBlock.common_generator_mem_actualSPrime
    (i : Fin b.primeCount) :
    engineAllowedGenerator C b.commonLeftIdeal ∈ (actualExteriorSPrime (b.primes i)).asIdeal := by
  sorry

variable [IsPrincipalIdealRing A.R]

/-- The block's actual principal mask remains even when the original
parent mask is empty.  Each of its squarefree divisors divides the
same common-left generator. -/
theorem FirstCommonCharacterBlock.maskGenerator_dvd_common
    (D : Finset (HeightOneSpectrum A.R)) (hD : D ⊆ b.mask ∅) :
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val ∣
      engineAllowedGenerator C b.commonLeftIdeal := by
  sorry

include C in
theorem FirstCommonCharacterBlock.maskGenerator_norm_le_common
    (D : Finset (HeightOneSpectrum A.R)) (hD : D ⊆ b.mask ∅) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
        A.exteriorNorm b.commonLeftIdeal := by
  sorry

include C in
theorem FirstCommonCharacterBlock.maskGenerator_norm_le_label
    (D : Finset (HeightOneSpectrum A.R)) (hD : D ⊆ b.mask ∅) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
        (Ideal.absNorm DE.1 : ℝ) := by
  sorry

theorem FirstCommonCharacterBlock.firstActive_norm_le_common :
    A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤
      A.exteriorNorm b.commonLeftIdeal := by
  sorry

theorem FirstCommonCharacterBlock.firstActive_norm_le_label :
    A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤
      (Ideal.absNorm DE.1 : ℝ) := by
  sorry

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem FirstCommonCharacterBlock.first_modulus_norm_product
    (profiles : ι → κ → SchwartzMap V ℂ) (i : ι) (j : κ) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus, (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val =
      A.exteriorNorm (b.leftResidual i) *
        (A.exteriorNorm (b.rightResidual j) *
          A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) := by
  sorry

theorem FirstCommonCharacterBlock.first_modulus_norm_le_full_columns
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus, (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val ≤
      A.exteriorNorm (fullI i) * A.exteriorNorm (fullJ j) := by
  sorry

/-- The mask and modulus windows follow from the original full-column
windows and membership in the genuine common-support pool. -/
theorem FirstCommonCharacterBlock.original_mask_modulus_windows
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (hDE : DE ∈ commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (Z B : ℝ) (hZ : 0 < Z)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ B)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ B) :
    (∀ D ∈ (b.mask ∅).powerset,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤ Z ^ B) ∧
    (∀ i ∈ b.leftColumns left, ∀ j ∈ b.rightColumns right,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(b.pair hΓ C profiles i j).modulus, (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val ≤
          Z ^ (2 * B)) := by
  sorry

/-- The actual first source therefore has the uniform physical row
exponent `η - (m + q) + 3B`.  Only the original dilation radius and
original full-column windows are inputs. -/
theorem FirstCommonCharacterBlock.physicalCutoff_le_full_columns
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (hDE : DE ∈ commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X)
    (p : RealParameters) (Z cutoffExponent B : ℝ) (hZ : 0 < Z)
    (hcutoff : X ≤ Z ^ cutoffExponent) (hradius : radius.val ≤ Z ^ (-(p.m + p.q)))
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ B)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ B) :
    (b.finiteSource hΓ C left right profiles ∅ radius X hX).physicalCutoff ≤
      Z ^ (cutoffExponent - (p.m + p.q) + 3 * B) := by
  sorry

end CommonBlock
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sIntegerElementNorm_dvd_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.maskGenerator_dvd_common
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.first_modulus_norm_le_full_columns
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.original_mask_modulus_windows
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.physicalCutoff_le_full_columns
