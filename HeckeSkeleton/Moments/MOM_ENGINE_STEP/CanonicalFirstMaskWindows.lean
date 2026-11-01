import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstRowWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

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
  obtain ⟨c, hc⟩ := hab
  have hc0 : c ≠ 0 := by
    intro h
    apply b.property
    rw [hc, h, mul_zero]
  have he : b = sIntegerNonzeroMul K S a ⟨c, hc0⟩ := Subtype.ext hc
  rw [he, sIntegerElementNorm_nonzeroMul]
  exact le_mul_of_one_le_right (sIntegerElementNorm K S a).property.le
    (one_le_sIntegerElementNorm K S ⟨c, hc0⟩)

section CommonBlock

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η hS)

theorem FirstCommonCharacterBlock.prime_dvd_commonLeft (i : Fin b.primeCount) :
    (b.primes i).val.asIdeal ∣ b.commonLeftIdeal.val := by
  have hp : (b.primes i).val.asIdeal ∣
      (b.primes i).val.asIdeal ^ b.leftMultiplicity i := by
    simpa only [pow_one] using
      pow_dvd_pow ((b.primes i).val.asIdeal) (Nat.succ_le_iff.mpr (b.left_positive i))
  apply hp.trans
  change (b.primes i).val.asIdeal ^ b.leftMultiplicity i ∣
    ∏ j, (b.primes j).val.asIdeal ^ b.leftMultiplicity j
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem FirstCommonCharacterBlock.common_generator_mem_actualSPrime
    (i : Fin b.primeCount) :
    engineAllowedGenerator C b.commonLeftIdeal ∈ (actualExteriorSPrime (b.primes i)).asIdeal := by
  have hle : A.extendIdeal b.commonLeftIdeal ≤ A.extendIdeal (primeIdeal (b.primes i)) :=
    Ideal.map_mono (Ideal.dvd_iff_le.mp (b.prime_dvd_commonLeft i))
  apply hle
  rw [← (engineAllowedGenerator_generates C b.commonLeftIdeal).2]
  exact Ideal.subset_span (Set.mem_singleton _)

variable [IsPrincipalIdealRing A.R]

/-- The block's actual principal mask remains even when the original
parent mask is empty.  Each of its squarefree divisors divides the
same common-left generator. -/
theorem FirstCommonCharacterBlock.maskGenerator_dvd_common
    (D : Finset (HeightOneSpectrum A.R)) (hD : D ⊆ b.mask ∅) :
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val ∣
      engineAllowedGenerator C b.commonLeftIdeal := by
  letI : IsDedekindDomain A.R :=
    sIntegerOrbitMask_isDedekindDomain K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  apply (IdealMobiusMask.maskGenerator_dvd_iff D _).mpr
  apply (IdealMobiusMask.mem_primeProduct D _).mpr
  intro q hq
  have hq' : q ∈ firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity := by
    simpa only [FirstCommonCharacterBlock.mask, Finset.empty_union] using hD hq
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq'
  exact b.common_generator_mem_actualSPrime C i

include C in
theorem FirstCommonCharacterBlock.maskGenerator_norm_le_common
    (D : Finset (HeightOneSpectrum A.R)) (hD : D ⊆ b.mask ∅) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
        A.exteriorNorm b.commonLeftIdeal := by
  have h := sIntegerElementNorm_dvd_le (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)
    ⟨engineAllowedGenerator C b.commonLeftIdeal,
      (engineAllowedGenerator_generates C b.commonLeftIdeal).1⟩
    (b.maskGenerator_dvd_common C D hD)
  rw [generates_sIntegerElementNorm b.commonLeftIdeal _
    (engineAllowedGenerator_generates C b.commonLeftIdeal)] at h
  exact h

include C in
theorem FirstCommonCharacterBlock.maskGenerator_norm_le_label
    (D : Finset (HeightOneSpectrum A.R)) (hD : D ⊆ b.mask ∅) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
        (Ideal.absNorm DE.1 : ℝ) := by
  have h := b.maskGenerator_norm_le_common C D hD
  change _ ≤ (Ideal.absNorm (primePowerProduct b.primes b.leftMultiplicity).val : ℝ) at h
  rwa [b.common_left] at h

theorem FirstCommonCharacterBlock.firstActive_norm_le_common :
    A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤
      A.exteriorNorm b.commonLeftIdeal :=
  norm_le_of_dvd b.commonLeftIdeal.property.1
    (firstActiveIdeal_dvd_common b.primes _ _ b.left_positive)

theorem FirstCommonCharacterBlock.firstActive_norm_le_label :
    A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤
      (Ideal.absNorm DE.1 : ℝ) := by
  have h := b.firstActive_norm_le_common
  change _ ≤ (Ideal.absNorm (primePowerProduct b.primes b.leftMultiplicity).val : ℝ) at h
  rwa [b.common_left] at h

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
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨b.leftGenerator i, (b.left_generates i).1⟩
      (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨b.rightGenerator j, (b.right_generates j).1⟩
        ⟨firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity,
          (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity).1⟩))).val = _
  rw [sIntegerElementNorm_nonzeroMul, sIntegerElementNorm_nonzeroMul,
    generates_sIntegerElementNorm (b.leftResidual i) _ (b.left_generates i),
    generates_sIntegerElementNorm (b.rightResidual j) _ (b.right_generates j),
    generates_sIntegerElementNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
      _ (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity)]

theorem FirstCommonCharacterBlock.first_modulus_norm_le_full_columns
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus, (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val ≤
      A.exteriorNorm (fullI i) * A.exteriorNorm (fullJ j) := by
  have hleft : A.exteriorNorm (fullI i) =
      A.exteriorNorm b.commonLeftIdeal * A.exteriorNorm (b.leftResidual i) := by
    change (Ideal.absNorm (fullI i).val : ℝ) = _
    rw [b.left_reconstruct left i hi, map_mul, Nat.cast_mul]
  have hright : A.exteriorNorm (fullJ j) =
      A.exteriorNorm b.commonRightIdeal * A.exteriorNorm (b.rightResidual j) := by
    change (Ideal.absNorm (fullJ j).val : ℝ) = _
    rw [b.right_reconstruct right j hj, map_mul, Nat.cast_mul]
  have hrightOne : 1 ≤ A.exteriorNorm b.commonRightIdeal := by
    simpa only [map_one, Nat.cast_one] using
      norm_le_of_dvd b.commonRightIdeal.property.1 (one_dvd b.commonRightIdeal.val)
  rw [b.first_modulus_norm_product C hΓ profiles i j, hleft, hright]
  calc
    _ = (A.exteriorNorm (b.leftResidual i) * A.exteriorNorm (b.rightResidual j)) *
        A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) := by ring
    _ ≤ (A.exteriorNorm (b.leftResidual i) * A.exteriorNorm (b.rightResidual j)) *
        A.exteriorNorm b.commonLeftIdeal :=
      mul_le_mul_of_nonneg_left b.firstActive_norm_le_common
        (mul_nonneg (A.exteriorNorm_pos _).le (A.exteriorNorm_pos _).le)
    _ ≤ ((A.exteriorNorm (b.leftResidual i) * A.exteriorNorm (b.rightResidual j)) *
        A.exteriorNorm b.commonLeftIdeal) * A.exteriorNorm b.commonRightIdeal :=
      le_mul_of_one_le_right (by positivity) hrightOne
    _ = _ := by ring

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
  have hcommon := (actual_common_pair_norm left right
    (fun i => (fullI i).val) (fun j => (fullJ j).val) (Z ^ B)
    (fun i _ => (fullI i).property.1) (fun j _ => (fullJ j).property.1)
    hleft hright ⟨DE, hDE⟩).1
  constructor
  · intro D hD
    exact (b.maskGenerator_norm_le_label C D (Finset.mem_powerset.mp hD)).trans hcommon
  · intro i hi j hj
    apply (b.first_modulus_norm_le_full_columns C hΓ left right profiles i hi j hj).trans
    calc
      _ ≤ Z ^ B * Z ^ B :=
        mul_le_mul (hleft i (Finset.mem_filter.mp hi).1)
          (hright j (Finset.mem_filter.mp hj).1) (A.exteriorNorm_pos _).le
          (Real.rpow_nonneg hZ.le _)
      _ = Z ^ (2 * B) := by rw [← Real.rpow_add hZ]; congr 1; ring

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
  obtain ⟨hmask, hmodulus⟩ :=
    b.original_mask_modulus_windows C hΓ left right profiles hDE Z B hZ hleft hright
  have h := (b.finiteSource hΓ C left right profiles ∅ radius X hX).physicalCutoff_le_original_windows Z cutoffExponent (-(p.m + p.q)) B (2 * B)
      hZ hcutoff hradius hmask hmodulus
  convert h using 1 <;> congr 1 <;> ring

end CommonBlock
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sIntegerElementNorm_dvd_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.maskGenerator_dvd_common
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.first_modulus_norm_le_full_columns
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.original_mask_modulus_windows
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.physicalCutoff_le_full_columns
