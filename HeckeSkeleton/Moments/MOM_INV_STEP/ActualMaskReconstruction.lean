import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourcePartition
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMaskGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceMasks
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualDivisorSectors

/-!
# Actual Poisson divisors determine their reconstruction ideals and sectors

The first M-empty mask divisor divides C times the original cube radical.
Its localization contraction is injective on divisor subsets. Moreover,
the actual selected mask generator is recovered from that ideal alone,
so the two genuine sector translations define the ideal-indexed
transport used by the fixed-triple fiber count, for every original Γ.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualMaskReconstruction

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open PrimitivePoissonSource ConductorMasks FirstSourceDecomposition CanonicalConductor
  FirstMaskGeometry ActualDivisorSectors
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local instance : IsDedekindDomain OS := sIntegerOrbitMask_isDedekindDomain K Sset
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

theorem maskIdeal_map (δ : Finset (HeightOneSpectrum OS)) :
    (maskIdeal K S δ).map (algebraMap (𝓞 K) OS) = IdealMobiusMask.primeProduct δ := by
  rw [maskIdeal, map_sIntegerModulusContraction]
  exact Ideal.span_singleton_generator _

theorem maskIdeal_injective : Function.Injective (maskIdeal K S) := by
  intro δ ε h
  have hm := congrArg (fun I : Ideal (𝓞 K) => I.map (algebraMap (𝓞 K) OS)) h
  rw [maskIdeal_map, maskIdeal_map] at hm
  have hf := congrArg normalizedFactors hm
  rw [IdealMobiusMask.normalizedFactors_primeProduct,
    IdealMobiusMask.normalizedFactors_primeProduct] at hf
  exact Finset.val_injective (Multiset.map_injective HeightOneSpectrum.asIdeal_injective hf)

theorem first_divisor_dvd_principal (n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ FirstSourcePartition.actualMask K S D ∅ n₁ n₂ b₁ b₂) :
    maskIdeal K S δ ∣ principalIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) := by
  have hδ' : δ ⊆ principalMask K S (pairSupport K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) := by
    simpa only [FirstSourcePartition.actualMask, Finset.empty_union] using hδ
  apply Ideal.dvd_iff_le.mpr
  rw [maskIdeal_eq_under]
  intro a ha
  change algebraMap (𝓞 K) OS a ∈ IdealMobiusMask.primeProduct δ
  rw [IdealMobiusMask.mem_primeProduct]
  intro P hP
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hδ' hP)
  have hle : principalIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) ≤ p.val.asIdeal := by
    rw [principalIdeal, IdealMobiusMask.primeProduct_eq_iInf]
    exact iInf_le_of_le p.val (iInf_le _ p.property)
  change algebraMap (𝓞 K) OS a ∈ p.val.asIdeal.map (algebraMap (𝓞 K) OS)
  exact Ideal.mem_map_of_mem _ (hle ha)

/-- This is the precise old-divisor divisibility required by the
reconstruction fiber, derived from the actual principal Poisson mask. -/
theorem first_divisor_dvd_common_cube (n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ FirstSourcePartition.actualMask K S D ∅ n₁ n₂ b₁ b₂) :
    maskIdeal K S δ ∣ FirstSourceDecomposition.C n₁.val n₂.val b₁.val b₂.val *
      (b₁.val.val * b₂.val.val).radical := by
  have hd := first_divisor_dvd_principal K S D n₁ n₂ b₁ b₂ δ hδ
  rw [principalIdeal_eq_common_mul_cube, commonResidualIdeal_eq_C] at hd
  apply hd.trans
  apply mul_dvd_mul_left
  rw [radical_eq_primeProduct (b₁.val * b₂.val)]
  exact Finset.prod_dvd_prod_of_subset _ _
    (fun p : HeightOneSpectrum (𝓞 K) => p.asIdeal) Finset.filter_subset

/-- The principal local generator is a deterministic function of the
ordinary ideal, including for the actual mask divisors. -/
def localGenerator (I : Ideal (𝓞 K)) : OS :=
  (I.map (algebraMap (𝓞 K) OS)).generator

theorem localGenerator_actual (δ : Finset (HeightOneSpectrum OS)) :
    localGenerator K S (maskIdeal K S δ) = (sIntegerMaskGenerator K Sset δ).val := by
  unfold localGenerator
  rw [maskIdeal_map]
  rfl

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

/-- This is the genuine ideal-indexed sector transport required by the
fiber relation. The harmless zero branches are never used by a source. -/
def sectorTransport (I J : Ideal (𝓞 K)) : Sector ≃ Sector :=
  if hi : localGenerator K S I ≠ 0 then
    if hj : localGenerator K S J ≠ 0 then
      (directDivisorTransport K S Γ D ⟨localGenerator K S I, hi⟩).trans
        (divisorTransport K S Γ D ⟨localGenerator K S J, hj⟩)
    else Equiv.refl _
  else Equiv.refl _

theorem sectorTransport_actual (δ₁ δ₂ : Finset (HeightOneSpectrum OS)) (ξ : Sector) :
    sectorTransport K S D Γ (maskIdeal K S δ₁) (maskIdeal K S δ₂) ξ =
      SecondSourceColumns.newSector K S Γ D
        (sIntegerMaskGenerator K Sset δ₁) (sIntegerMaskGenerator K Sset δ₂) ξ := by
  unfold sectorTransport
  rw [localGenerator_actual, localGenerator_actual,
    dif_pos (sIntegerMaskGenerator K Sset δ₁).property,
    dif_pos (sIntegerMaskGenerator K Sset δ₂).property]
  rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualMaskReconstruction

end
