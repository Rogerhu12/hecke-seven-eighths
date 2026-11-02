import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalJointFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

set_option linter.unusedSectionVars false

/-!
# Actual first mask and modulus windows

The principal common-prime mask divides an actual generator of the
complete left common ideal. The original first modulus consists of the
two residual generators and the active common generator; its ideal
divides the original product of the two full column ideals. These are
divisibility statements about the existing source, so its whole-carrier
norm windows follow from the individual original column windows.

The empty original row mask uses the genuine contraction of S-integer
primes for its original-prime dictionary. No auxiliary prime or pool is
chosen, including when the source has zero slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.Active

variable {K : Type} [Field K] [NumberField K]

/-- Element divisibility gives norm monotonicity because the quotient
is a nonzero S-integer and has norm at least one. -/
theorem sIntegerElementNorm_le_of_dvd
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (d c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)
    (hd : d ≠ 0) (hc : c ≠ 0) (h : d ∣ c) :
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨d, hd⟩).val ≤
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val := by
  sorry

private theorem physical_ideal_norm_le_of_dvd
    (D I : Ideal (𝓞 K)) (hI : I ≠ 0) (h : D ∣ I) :
    (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  sorry

variable {A : SArithmeticData K}

/-- The canonical dictionary on the empty mask is a total, genuine
prime contraction. Its empty domain imposes no prime-existence choice. -/
def emptyOriginalSIntegerMask :
    OriginalMaskPrimeData (∅ : Finset (HeightOneSpectrum A.R)) (1 : Ideal (𝓞 K)) where
  prime p :=
    { asIdeal := p.asIdeal.under (𝓞 K)
      isPrime := inferInstance
      ne_bot := SIntegerLocalization.under_ne_zero A.Sf p.asIdeal p.ne_bot }
  injective := by
    intro p hp
    exact False.elim (Finset.notMem_empty p hp)
  divides := by
    intro p hp
    exact False.elim (Finset.notMem_empty p hp)

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock fullI fullJ DE)

/-- The complete principal first mask divides a generator of the
original common ideal, independent of its unit normalization. -/
theorem principal_mask_generator_dvd_common
    (g : A.R) (hg : A.Generates (primePowerProduct b.primes b.leftMultiplicity) g) :
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).val ∣ g := by
  sorry

/-- The physical mask norm is bounded by the actual complete left
common ideal, rather than by a supplied mask estimate. -/
theorem principal_mask_norm_le_common
    (C : A.GeneralArithmeticContext σ η hS) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅))).val ≤
        (Ideal.absNorm DE.1 : ℝ) := by
  sorry

theorem principal_mask_norm_le_original_column
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (i : ι) (hi : i ∈ b.leftColumns left) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅))).val ≤
        (Ideal.absNorm (fullI i).val : ℝ) := by
  sorry

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- Gating does not change the modulus. Its norm is exactly that of
the two original residual ideals times the actual active radical. -/
theorem first_modulus_norm
    (C : A.GeneralArithmeticContext σ η hS)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (i : ι) (j : κ) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus,
        (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val =
      (Ideal.absNorm ((b.leftResidual i).val * ((b.rightResidual j).val *
        (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val)) : ℝ) := by
  sorry

/-- The actual first modulus ideal divides the full original pair.
Only existing common and residual factors occur in the quotient. -/
theorem first_modulus_norm_le_original_product
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus,
        (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val ≤
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) := by
  sorry

end FirstCommonCharacterBlock

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- Both physical windows for every genuine common-support label
follow from the same original individual column norm windows. -/
theorem first_original_physical_windows
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (Z B : ℝ) (hZ : 0 < Z)
    (hleft : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Z ^ B)
    (hright : ∀ j ∈ right, (Ideal.absNorm (fullJ j).val : ℝ) ≤ Z ^ B)
    (v : FirstZeroLabel left right fullI fullJ × (ι × κ))
    (hv : v ∈ firstZeroPairs left right fullI fullJ) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ((blocks v.1).mask ∅))).val ≤ Z ^ B ∧
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).modulus,
        ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).modulus_ne_zero⟩).val ≤ Z ^ (2 * B) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sIntegerElementNorm_le_of_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.principal_mask_norm_le_original_column
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.first_modulus_norm_le_original_product
#print axioms HeckeSkeleton.Moments.EngineStep.first_original_physical_windows
