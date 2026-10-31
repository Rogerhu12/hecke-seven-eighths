import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalZero
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds

/-!
# Exact splitting of the literal canonical parent
The full empty-conductor physical source is retained. Its nonzero
Fourier frequencies are distinct from the two additive zero terms.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSplit

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open CanonicalBlock PrimitivePoissonSource ConductorMasks PrincipalZero PrincipalSource
  CoefficientBounds
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {σ : Type*}

def pairWeight (C : ColumnData K S σ) (f : Ext) (p : (Ext × Ext) × (Ext × Ext)) : ℂ :=
  canonicalColumn K S D C f p.1.1 p.1.2 *
    conj (canonicalColumn K S D C f p.2.1 p.2.2)

def nonzeroDual (b : ActualMaskedPoissonBlock K S Γ) : ℂ :=
  ∑ d ∈ b.mask.powerset, b.divisorCoefficient d *
    (b.prefactor d * b.dual μv D.different_outside d)

def pairPrincipal (x y : Ext × Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) : ℂ :=
  principalContribution K S D Γ hΓ μv
    (pairSupport K S D x.2 y.2 x.1 y.1) (pairExponent K S x.2 y.2 x.1 y.1)
    φ h hlc hcs M R

def canonicalDual (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) : ℂ :=
  ∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N), pairWeight K S D C f p *
    nonzeroDual K S D Γ μv (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R)

def canonicalPrincipal (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) : ℂ :=
  ∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N), pairWeight K S D C f p *
    pairPrincipal K S D Γ hΓ μv p.1 p.2 φ h hlc hcs M R

theorem pair_transformed_split (x y : Ext × Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) :
    (primitivePairBlock K S D Γ hΓ x y φ h hlc hcs M R).transformed
        μv D.different_outside =
      nonzeroDual K S D Γ μv (primitivePairBlock K S D Γ hΓ x y φ h hlc hcs M R) +
        pairPrincipal K S D Γ hΓ μv x y φ h hlc hcs M R := by
  simp only [ActualMaskedPoissonBlock.transformed, nonzeroDual, pairPrincipal,
    principalContribution, primitivePairBlock, mul_add, Finset.sum_add_distrib]

theorem pairPrincipal_eq_zero (x y : Ext × Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r})
    (hactive : activeSupport (pairSupport K S D x.2 y.2 x.1 y.1).support
      (pairExponent K S x.2 y.2 x.1 y.1) ≠ ∅) :
    pairPrincipal K S D Γ hΓ μv x y φ h hlc hcs M R = 0 := by
  unfold pairPrincipal principalContribution
  simp only [zeroContribution_eq, if_neg hactive, mul_zero, Finset.sum_const_zero]

theorem canonicalPrincipal_eq_principalPairs (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) :
    canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs M R =
      ∑ p ∈ principalPairs K S D B N, pairWeight K S D C f p *
        pairPrincipal K S D Γ hΓ μv p.1 p.2 φ h hlc hcs M R := by
  unfold canonicalPrincipal principalPairs
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hactive : activeSupport (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
      (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1) ≠ ∅ := by
    intro he
    exact hnot (Finset.mem_filter.mpr ⟨hp, he⟩)
  rw [pairPrincipal_eq_zero K S D Γ hΓ μv p.1 p.2 φ h hlc hcs M R hactive, mul_zero]

/-- The whole principal source, including its nonzero Fourier part. -/
def canonicalPrincipalSource (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) : ℂ :=
  ∑ p ∈ principalPairs K S D B N, pairWeight K S D C f p *
    (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R).physical

def canonicalNonprincipalDual (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) : ℂ :=
  ∑ p ∈ ((B ×ˢ N) ×ˢ (B ×ˢ N)).filter (fun p =>
      activeSupport (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
        (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1) ≠ ∅),
    pairWeight K S D C f p * nonzeroDual K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R)

theorem principal_physical_norm_le_profile_mass (B : ActualFiniteSource.PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hempty : activeSupport B.support t = ∅) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) :
    ‖(block K S D Γ hΓ B t φ h hlc hcs M R).physical‖ ≤
      ∑' q : SIntegerOrbits K Sset Γ,
        ‖sUnitOrbitalProfile K Sset
          (sLocalTensorTestFunction K Sset φ (sIntegerFiniteTestFunction K S h))
          ⟨R.val * (sIntegerOrbitNorm K Sset Γ q).val,
            mul_pos R.property (sIntegerOrbitNorm K Sset Γ q).property⟩‖ := by
  let b := block K S D Γ hΓ B t φ h hlc hcs M R
  have hw (q : SIntegerOrbits K Sset Γ) :
      sIntegerPeriodicOrbitWeight K Sset Γ b.modulus b.coefficient b.invariant q = 1 := by
    refine Quotient.inductionOn q ?_
    intro a
    rw [sIntegerPeriodicOrbitWeight_mk]
    exact PrincipalLocus.primitiveCoefficient_eq_one_of_empty K S D B t hempty _
  have hs := summable_norm_sIntegerOrbitalProfile K Sset Γ φ
    (sIntegerFiniteTestFunction K S h)
    (continuous_sIntegerFiniteTestFunction K S h hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) R
  have hp (q : SIntegerOrbits K Sset Γ) :
      ‖b.orbitalTerm q‖ ≤
        ‖sUnitOrbitalProfile K Sset
          (sLocalTensorTestFunction K Sset φ (sIntegerFiniteTestFunction K S h))
          ⟨R.val * (sIntegerOrbitNorm K Sset Γ q).val,
            mul_pos R.property (sIntegerOrbitNorm K Sset Γ q).property⟩‖ := by
    unfold ActualMaskedPoissonBlock.orbitalTerm
    rw [hw, mul_one, norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norm_sIntegerOrbitAvoidanceMask_le_one K Sset Γ b.mask q) (norm_nonneg _)
  change ‖b.physical‖ ≤ _
  rw [b.physical_eq_tsum]
  exact (norm_tsum_le_tsum_norm b.summable_norm_orbitalTerm).trans
    (b.summable_norm_orbitalTerm.tsum_le_tsum hp hs)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem canonicalCubeEnergy_eq_dual_add_principal (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (hN : ∀ n ∈ N, Squarefree n.val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) :
    canonicalCubeEnergy K S D Γ C f B N φ h M R =
      canonicalDual K S D Γ hΓ μv C f B N φ h hlc hcs M R +
        canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs M R := by
  rw [canonicalCubeEnergy_primitive_poisson K S D Γ hΓ μv ν μ
    C f B N hN φ h hlc hcs M R]
  unfold canonicalDual canonicalPrincipal pairWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [pair_transformed_split K S D Γ hΓ μv p.1 p.2 φ h hlc hcs M R, mul_add]

include ν μ in
theorem canonicalCubeEnergy_norm_le (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (hN : ∀ n ∈ N, Squarefree n.val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) :
    ‖canonicalCubeEnergy K S D Γ C f B N φ h M R‖ ≤
      ‖canonicalDual K S D Γ hΓ μv C f B N φ h hlc hcs M R‖ +
        ‖canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs M R‖ := by
  rw [canonicalCubeEnergy_eq_dual_add_principal K S D Γ hΓ μv ν μ
    C f B N hN φ h hlc hcs M R]
  exact norm_add_le _ _

include ν μ in
theorem canonicalCubeEnergy_eq_nonprincipal_add_principalSource
    (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (hN : ∀ n ∈ N, Squarefree n.val.val) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) :
    canonicalCubeEnergy K S D Γ C f B N φ h M R =
      canonicalNonprincipalDual K S D Γ hΓ μv C f B N φ h hlc hcs M R +
        canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs M R := by
  rw [canonicalCubeEnergy_primitive_poisson K S D Γ hΓ μv ν μ
    C f B N hN φ h hlc hcs M R]
  change (∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N), pairWeight K S D C f p *
    (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R).transformed
      μv D.different_outside) = _
  unfold canonicalNonprincipalDual canonicalPrincipalSource principalPairs
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases he : activeSupport (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
      (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1) = ∅
  · rw [if_neg (not_not_intro he), if_pos he, zero_add]
    rw [ActualMaskedPoissonBlock.physical_eq_transformed μv D.different_outside ν μ]
  · rw [if_pos he, if_neg he, add_zero,
      pair_transformed_split K S D Γ hΓ μv p.1 p.2 φ h hlc hcs M R,
      pairPrincipal_eq_zero K S D Γ hΓ μv p.1 p.2 φ h hlc hcs M R he, add_zero]

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSplit

end

