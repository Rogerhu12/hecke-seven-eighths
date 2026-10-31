import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePoissonSource
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition
import HeckeGeneral.Analysis.GlobalThetaData

/-!
# Actual support geometry of first Poisson mask divisors

The external mask is the localization of the prime support of its exterior
ideal.  Every actual inclusion-exclusion divisor and the primitive
conductor divide the literal product of the original five ideals.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstMaskGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open PrimitivePoissonSource ConductorMasks LocalizedMasks FirstSourceDecomposition
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

local instance : IsDedekindDomain OS := sIntegerOrbitMask_isDedekindDomain K Sset

def externalMask (Q : Ext) : Finset (HeightOneSpectrum OS) :=
  localizeSupportedMask K Sset (primeSupport Q.val)
    (fun p hp => Q.property p ((mem_primeSupport Q.val p).mp hp))

def sourceIdeal (Q n₁ n₂ b₁ b₂ : Ext) : Ideal (𝓞 K) :=
  Q.val.val * b₁.val.val * b₂.val.val * n₁.val.val * n₂.val.val

theorem sourceIdeal_ne_zero (Q n₁ n₂ b₁ b₂ : Ext) :
    sourceIdeal K S Q n₁ n₂ b₁ b₂ ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero Q.val) (nonZeroDivisors.coe_ne_zero b₁.val))
    (nonZeroDivisors.coe_ne_zero b₂.val)) (nonZeroDivisors.coe_ne_zero n₁.val))
    (nonZeroDivisors.coe_ne_zero n₂.val)

theorem sourceIdeal_outside (Q n₁ n₂ b₁ b₂ : Ext)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ sourceIdeal K S Q n₁ n₂ b₁ b₂) : p ∉ Sset := by
  simp only [sourceIdeal, p.prime.dvd_mul] at hp
  rcases hp with (((hQ | hb₁) | hb₂) | hn₁) | hn₂
  · exact Q.property p hQ
  · exact b₁.property p hb₁
  · exact b₂.property p hb₂
  · exact n₁.property p hn₁
  · exact n₂.property p hn₂

theorem external_prime_dvd_source (Q n₁ n₂ b₁ b₂ : Ext)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ primeSupport Q.val) :
    p.asIdeal ∣ sourceIdeal K S Q n₁ n₂ b₁ b₂ := by
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left ((mem_primeSupport Q.val p).mp hp) _) _) _) _

theorem pair_prime_dvd_source (Q n₁ n₂ b₁ b₂ : Ext)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (pairSupport K S D n₁ n₂ b₁ b₂).support) :
    p.asIdeal ∣ sourceIdeal K S Q n₁ n₂ b₁ b₂ := by
  apply p.prime.dvd_mul.mpr
  rcases (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mp hp with hb₁ | hb₂ | hn₁ | hn₂
  · exact Or.inl (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right hb₁ _) _) _)
  · exact Or.inl (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb₂ _) _)
  · exact Or.inl (dvd_mul_of_dvd_right hn₁ _)
  · exact Or.inr hn₂

theorem primeProduct_dvd_of_forall {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Finset (HeightOneSpectrum R)) (I : Ideal R)
    (hP : ∀ p ∈ P, p.asIdeal ∣ I) : IdealMobiusMask.primeProduct P ∣ I := by
  apply Ideal.dvd_iff_le.mpr
  rw [IdealMobiusMask.primeProduct_eq_iInf]
  exact le_iInf (fun p => le_iInf (fun hp => Ideal.dvd_iff_le.mp (hP p hp)))

theorem primitiveIdeal_dvd_source (Q n₁ n₂ b₁ b₂ : Ext) :
    primitiveIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) ∣ sourceIdeal K S Q n₁ n₂ b₁ b₂ := by
  apply primeProduct_dvd_of_forall
  intro p hp
  exact pair_prime_dvd_source K S D Q n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1

/-- The literal mask appearing in the first primitive Poisson block. -/
def actualMask (Q n₁ n₂ b₁ b₂ : Ext) : Finset (HeightOneSpectrum OS) :=
  externalMask K S Q ∪
    principalMask K S (pairSupport K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂)

theorem actualMask_prime_le_source_map (Q n₁ n₂ b₁ b₂ : Ext)
    (P : HeightOneSpectrum OS) (hP : P ∈ actualMask K S D Q n₁ n₂ b₁ b₂) :
    (sourceIdeal K S Q n₁ n₂ b₁ b₂).map (algebraMap (𝓞 K) OS) ≤ P.asIdeal := by
  rcases Finset.mem_union.mp hP with hP | hP
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    change (sourceIdeal K S Q n₁ n₂ b₁ b₂).map (algebraMap (𝓞 K) OS) ≤
      p.val.asIdeal.map (algebraMap (𝓞 K) OS)
    exact Ideal.map_mono (Ideal.dvd_iff_le.mp
      (external_prime_dvd_source K S Q n₁ n₂ b₁ b₂ p.val p.property))
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    change (sourceIdeal K S Q n₁ n₂ b₁ b₂).map (algebraMap (𝓞 K) OS) ≤
      p.val.asIdeal.map (algebraMap (𝓞 K) OS)
    exact Ideal.map_mono (Ideal.dvd_iff_le.mp
      (pair_prime_dvd_source K S D Q n₁ n₂ b₁ b₂ p.val
        (Finset.mem_filter.mp p.property).1))

variable [IsPrincipalIdealRing OS]

def maskIdeal (δ : Finset (HeightOneSpectrum OS)) : Ideal (𝓞 K) :=
  sIntegerModulusContraction K Sset (sIntegerMaskGenerator K Sset δ).val

theorem maskIdeal_eq_under (δ : Finset (HeightOneSpectrum OS)) :
    maskIdeal K S δ = (IdealMobiusMask.primeProduct δ).under (𝓞 K) := by
  unfold maskIdeal sIntegerModulusContraction
  congr 1
  exact Ideal.span_singleton_generator _

theorem maskIdeal_dvd_source (Q n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ actualMask K S D Q n₁ n₂ b₁ b₂) :
    maskIdeal K S δ ∣ sourceIdeal K S Q n₁ n₂ b₁ b₂ := by
  apply Ideal.dvd_iff_le.mpr
  rw [maskIdeal_eq_under]
  intro a ha
  change algebraMap (𝓞 K) OS a ∈ IdealMobiusMask.primeProduct δ
  rw [IdealMobiusMask.mem_primeProduct]
  intro P hP
  exact actualMask_prime_le_source_map K S D Q n₁ n₂ b₁ b₂ P (hδ hP)
    (Ideal.mem_map_of_mem _ ha)

theorem maskIdeal_dvd_source_of_mem_powerset (Q n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ∈ (actualMask K S D Q n₁ n₂ b₁ b₂).powerset) :
    maskIdeal K S δ ∣ sourceIdeal K S Q n₁ n₂ b₁ b₂ :=
  maskIdeal_dvd_source K S D Q n₁ n₂ b₁ b₂ δ (Finset.mem_powerset.mp hδ)

theorem maskIdeal_norm (δ : Finset (HeightOneSpectrum OS)) :
    ((maskIdeal K S δ).absNorm : ℝ) =
      (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val := by
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K Sset
    (sIntegerMaskGenerator K Sset δ).val (sIntegerMaskGenerator K Sset δ).property,
    natCard_sIntegerPrincipalResidue K Sset
      (sIntegerMaskGenerator K Sset δ).val (sIntegerMaskGenerator K Sset δ).property]
  rfl

theorem absNorm_le_of_dvd (I J : Ideal (𝓞 K)) (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (I.absNorm : ℝ) ≤ (J.absNorm : ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr hJ))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hIJ))

theorem maskNorm_le_source (Q n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ actualMask K S D Q n₁ n₂ b₁ b₂) :
    (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤
      ((sourceIdeal K S Q n₁ n₂ b₁ b₂).absNorm : ℝ) := by
  rw [← maskIdeal_norm]
  exact absNorm_le_of_dvd K _ _ (sourceIdeal_ne_zero K S Q n₁ n₂ b₁ b₂)
    (maskIdeal_dvd_source K S D Q n₁ n₂ b₁ b₂ δ hδ)

theorem primitiveNorm_le_source (Q n₁ n₂ b₁ b₂ : Ext) :
    ((primitiveIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂)).absNorm : ℝ) ≤
      ((sourceIdeal K S Q n₁ n₂ b₁ b₂).absNorm : ℝ) :=
  absNorm_le_of_dvd K _ _ (sourceIdeal_ne_zero K S Q n₁ n₂ b₁ b₂)
    (primitiveIdeal_dvd_source K S D Q n₁ n₂ b₁ b₂)

theorem sourceIdeal_norm (Q n₁ n₂ b₁ b₂ : Ext) :
    ((sourceIdeal K S Q n₁ n₂ b₁ b₂).absNorm : ℝ) =
      (Q.val.val.absNorm : ℝ) * (b₁.val.val.absNorm : ℝ) * (b₂.val.val.absNorm : ℝ) *
        (n₁.val.val.absNorm : ℝ) * (n₂.val.val.absNorm : ℝ) := by
  simp only [sourceIdeal, Ideal.absNorm_mul, Nat.cast_mul]

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstMaskGeometry

end

