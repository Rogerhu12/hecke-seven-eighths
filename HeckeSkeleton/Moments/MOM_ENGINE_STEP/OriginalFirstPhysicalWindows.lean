import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalJointFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

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
  obtain ⟨x, hx⟩ := h
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hc
    rw [hx, hzero, mul_zero]
  have he : (⟨c, hc⟩ : NonzeroRingElements
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) =
      sIntegerNonzeroMul K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨d, hd⟩ ⟨x, hx0⟩ :=
    Subtype.ext hx
  rw [he, sIntegerElementNorm_nonzeroMul]
  exact le_mul_of_one_le_right
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨d, hd⟩).property.le
    (one_le_sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨x, hx0⟩)

private theorem physical_ideal_norm_le_of_dvd
    (D I : Ideal (𝓞 K)) (hI : I ≠ 0) (h : D ∣ I) :
    (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have hpos : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (by simpa only [Ideal.absNorm_eq_zero_iff] using hI)
  exact_mod_cast Nat.le_of_dvd hpos
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h))

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
  change IdealMobiusMask.maskGenerator (b.mask ∅) ∣ g
  rw [IdealMobiusMask.maskGenerator_dvd_iff, IdealMobiusMask.mem_primeProduct]
  intro p hp
  have hp' : p ∈ firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity := by
    simpa only [FirstCommonCharacterBlock.mask, Finset.empty_union] using hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp'
  have hd : (primeIdeal (b.primes i)).val ∣
      (primePowerProduct b.primes b.leftMultiplicity).val := by
    rw [b.common_left]
    exact b.originalCommonPrimeData.divides i (Finset.mem_univ i)
  have hle : A.extendIdeal (primePowerProduct b.primes b.leftMultiplicity) ≤
      A.extendIdeal (primeIdeal (b.primes i)) :=
    Ideal.map_mono (Ideal.le_of_dvd hd)
  apply hle
  rw [← hg.2]
  exact Ideal.mem_span_singleton_self g

/-- The physical mask norm is bounded by the actual complete left
common ideal, rather than by a supplied mask estimate. -/
theorem principal_mask_norm_le_common
    (C : A.GeneralArithmeticContext σ η hS) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅))).val ≤
        (Ideal.absNorm DE.1 : ℝ) := by
  obtain ⟨g, u, hg, hu, hallowed⟩ :=
    C.allowed_integral (primePowerProduct b.primes b.leftMultiplicity)
  have hnorm := sIntegerElementNorm_le_of_dvd A.Sf
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).val
    g (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).property
    hg.1 (b.principal_mask_generator_dvd_common g hg)
  rw [generates_sIntegerElementNorm _ _ hg, b.common_left] at hnorm
  exact hnorm

theorem principal_mask_norm_le_original_column
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (i : ι) (hi : i ∈ b.leftColumns left) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅))).val ≤
        (Ideal.absNorm (fullI i).val : ℝ) := by
  apply (b.principal_mask_norm_le_common C).trans
  apply physical_ideal_norm_le_of_dvd DE.1 (fullI i).val (fullI i).property.1
  rw [← b.common_left]
  exact ⟨(b.leftResidual i).val, b.left_reconstruct left i hi⟩

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
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨b.leftGenerator i, (b.left_generates i).1⟩
      (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨b.rightGenerator j, (b.right_generates j).1⟩
        ⟨firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity,
          (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity).1⟩))).val = _
  rw [sIntegerElementNorm_nonzeroMul, sIntegerElementNorm_nonzeroMul,
    generates_sIntegerElementNorm _ _ (b.left_generates i),
    generates_sIntegerElementNorm _ _ (b.right_generates j),
    generates_sIntegerElementNorm _ _
      (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity)]
  simp only [map_mul, Nat.cast_mul]

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
  rw [b.first_modulus_norm hΓ C profiles i j]
  apply physical_ideal_norm_le_of_dvd _ _
    (mul_ne_zero (fullI i).property.1 (fullJ j).property.1)
  obtain ⟨T, hT⟩ := firstActiveIdeal_dvd_common b.primes
    b.leftMultiplicity b.rightMultiplicity b.left_positive
  refine ⟨T * (primePowerProduct b.primes b.rightMultiplicity).val, ?_⟩
  rw [b.left_reconstruct left i hi, b.right_reconstruct right j hj, hT]
  ac_rfl

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
  have hm := (mem_firstZeroPairs left right fullI fullJ v).mp hv
  have hb := ((blocks v.1).mem_iff_label left right
    (commonSupportPool_support_eq left right (fun i => (fullI i).val)
      (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr hm
  refine ⟨((blocks v.1).principal_mask_norm_le_original_column C left v.2.1 hb.1).trans
    (hleft v.2.1 hm.1), ?_⟩
  apply ((blocks v.1).first_modulus_norm_le_original_product hΓ C
    left right profiles v.2.1 hb.1 v.2.2 hb.2.1).trans
  rw [map_mul, Nat.cast_mul]
  calc
    _ ≤ Z ^ B * Z ^ B := mul_le_mul (hleft v.2.1 hm.1)
      (hright v.2.2 hm.2.1) (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _ = Z ^ (2 * B) := by rw [← Real.rpow_add hZ, show B + B = 2 * B by ring]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sIntegerElementNorm_le_of_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.principal_mask_norm_le_original_column
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.first_modulus_norm_le_original_product
#print axioms HeckeSkeleton.Moments.EngineStep.first_original_physical_windows
