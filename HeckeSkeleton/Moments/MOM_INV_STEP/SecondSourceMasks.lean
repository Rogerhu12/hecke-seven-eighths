import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceReindexing
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceGauss
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourcePartition
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMaskGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualDivisorSectors

/-!
# The actual second mask is frozen with the original common ideal

The principal local factors are computed from the fresh original pair.
All their inclusion-exclusion divisors are retained in each fixed-common
slice, before mutual coprimality is extended.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceMasks

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstSourceDecomposition FirstSourceReindexing ConductorMasks PrimitivePoissonSource
  FirstInversePoisson SecondSourceGauss ActualInverseFactors ActualDivisorSectors
  CanonicalNormPools SecondSourceReindexing
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "e" => unitIdeal K S

local instance : IsDedekindDomain OS := sIntegerOrbitMask_isDedekindDomain K Sset

def commonMask (g : Ext) : Finset (HeightOneSpectrum OS) :=
  principalMask K S (pairSupport K S D g g e e) (pairExponent K S g g e e)

theorem common_self (g : Ext) (hg : Squarefree g.val.val) : common K Sset g g = g := by
  apply Subtype.ext
  apply Subtype.ext
  rw [common_eq_gcd K Sset g g hg hg, Ideal.gcd_eq_sup, sup_idem]

theorem principalMask_congr_of_common (x₁ x₂ y₁ y₂ : Ext)
    (hc : common K Sset x₁ x₂ = common K Sset y₁ y₂) :
    principalMask K S (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e) =
      principalMask K S (pairSupport K S D y₁ y₂ e e) (pairExponent K S y₁ y₂ e e) := by
  have he : principalIdeal (pairSupport K S D x₁ x₂ e e).support
      (pairExponent K S x₁ x₂ e e) =
      principalIdeal (pairSupport K S D y₁ y₂ e e).support
        (pairExponent K S y₁ y₂ e e) := by
    rw [principal_mask, principal_mask, hc]
  have hn : nonzeroProduct (principalSupport (pairSupport K S D x₁ x₂ e e).support
      (pairExponent K S x₁ x₂ e e)) =
      nonzeroProduct (principalSupport (pairSupport K S D y₁ y₂ e e).support
        (pairExponent K S y₁ y₂ e e)) := Subtype.ext he
  have hs := congrArg primeSupport hn
  simp only [primeSupport_nonzeroProduct] at hs
  unfold principalMask
  congr 1
  exact hs

theorem actualMask_eq_commonMask (x₁ x₂ : Ext) :
    FirstSourcePartition.actualMask K S D ∅ x₁ x₂ e e =
      commonMask K S D (common K Sset x₁ x₂) := by
  rw [FirstSourcePartition.actualMask, Finset.empty_union]
  apply principalMask_congr_of_common K S D
  exact (common_self K S (common K Sset x₁ x₂) (common_squarefree K Sset x₁ x₂)).symm

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Every divisor is a divisor of the frozen original common ideal,
not of the subsequently extended residual gcd. -/
theorem actual_divisor_dvd (g : Ext) (hg : Squarefree g.val.val)
    (δ : Finset (HeightOneSpectrum OS)) (hδ : δ ⊆ commonMask K S D g) :
    (divisorIdeal K S (sIntegerMaskGenerator K Sset δ)).val.val ∣ g.val.val := by
  apply Ideal.dvd_iff_le.mpr
  change g.val.val ≤ FirstMaskGeometry.maskIdeal K S δ
  rw [FirstMaskGeometry.maskIdeal_eq_under]
  intro a ha
  change algebraMap (𝓞 K) OS a ∈ IdealMobiusMask.primeProduct δ
  rw [IdealMobiusMask.mem_primeProduct]
  intro P hP
  have hp := hδ hP
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp
  have hpg : g.val.val ≤ p.val.asIdeal := by
    have he := principal_mask K S D g g
    rw [common_self K S g hg] at he
    rw [← he, principalIdeal, IdealMobiusMask.primeProduct_eq_iInf]
    exact iInf_le_of_le p.val (iInf_le _ p.property)
  change algebraMap (𝓞 K) OS a ∈ p.val.asIdeal.map (algebraMap (𝓞 K) OS)
  exact Ideal.mem_map_of_mem _ (hpg ha)

/-- All actual masks and all members of the same bare frequency pool
are reordered exactly with the fresh original common-factor slices. -/
theorem sum_masks_frequencies_by_common {κ : Type*}
    (N : ℝ) (hN : 0 ≤ N) (A : Finset κ)
    (F : Ext → Ext → Finset (HeightOneSpectrum OS) → κ → ℂ) :
    (∑ x₁ ∈ squarefreePool K Sset N, ∑ x₂ ∈ squarefreePool K Sset N,
      ∑ δ ∈ (FirstSourcePartition.actualMask K S D ∅ x₁ x₂ e e).powerset,
        ∑ k ∈ A, F x₁ x₂ δ k) =
      ∑ g ∈ squarefreePool K Sset N, ∑ δ ∈ (commonMask K S D g).powerset,
        ∑ k ∈ A, ∑ z₁ ∈ squarefreePool K Sset (N / height K Sset g),
          ∑ z₂ ∈ squarefreePool K Sset (N / height K Sset g),
            if IsCoprime g.val.val z₁.val.val ∧ IsCoprime g.val.val z₂.val.val ∧
                IsCoprime z₁.val.val z₂.val.val then
              F (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) δ k else 0 := by
  rw [sum_pairs_by_common K Sset N hN]
  apply Finset.sum_congr rfl
  intro g hg
  have hgs := squarefreePool_squarefree K Sset hg
  have hp (z₁ : Ext) (hz₁ : z₁ ∈ squarefreePool K Sset (N / height K Sset g))
      (z₂ : Ext) (hz₂ : z₂ ∈ squarefreePool K Sset (N / height K Sset g)) :
      (if compatible K Sset g z₁ z₂ then
        ∑ δ ∈ (FirstSourcePartition.actualMask K S D ∅
          (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) e e).powerset,
          ∑ k ∈ A, F (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) δ k else 0) =
        ∑ δ ∈ (commonMask K S D g).powerset, ∑ k ∈ A,
          if compatible K Sset g z₁ z₂ then
            F (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) δ k else 0 := by
    by_cases hc : compatible K Sset g z₁ z₂
    · have hf := common_of_products K Sset g z₁ z₂ hgs
        (squarefreePool_squarefree K Sset hz₁) (squarefreePool_squarefree K Sset hz₂)
        hc.1 hc.2.1 hc.2.2
      rw [if_pos hc, actualMask_eq_commonMask, hf]
      simp only [if_pos hc]
    · simp only [if_neg hc, Finset.sum_const_zero]
  calc
    _ = ∑ z₁ ∈ squarefreePool K Sset (N / height K Sset g),
        ∑ z₂ ∈ squarefreePool K Sset (N / height K Sset g),
          ∑ δ ∈ (commonMask K S D g).powerset, ∑ k ∈ A,
            if compatible K Sset g z₁ z₂ then
              F (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) δ k else 0 := by
      apply Finset.sum_congr rfl
      intro z₁ hz₁
      apply Finset.sum_congr rfl
      intro z₂ hz₂
      exact hp z₁ hz₁ z₂ hz₂
    _ = _ := by
      simp_rw [Finset.sum_comm
        (s := squarefreePool K Sset (N / height K Sset g))
        (t := (commonMask K S D g).powerset)]
      simp_rw [Finset.sum_comm
        (s := squarefreePool K Sset (N / height K Sset g)) (t := A)]
      rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceMasks

end
