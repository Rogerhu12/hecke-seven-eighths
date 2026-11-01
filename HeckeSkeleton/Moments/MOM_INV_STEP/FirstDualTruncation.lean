import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSplit
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectors
import HeckeGeneral.Analysis.SIntegerPeriodicTruncation

/-!
# Exact bare-frequency truncation of the genuine first Poisson source

Every original unit sector is retained.  The cutoff is on the norm of the
frequency ideal, before multiplication by the moving dual radius.  Both
the retained sum and the tail use the literal divisor Fourier coefficient.
The empty-conductor source is split only in the outer pair sum.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstDualTruncation

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open CanonicalBlock PrimitivePoissonSource ConductorMasks CanonicalPoissonSplit
  PrincipalSource
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
local notation "Orbit" => SIntegerOrbits K Sset Γ

/-- A finite ball in the original orbit space, using the bare ideal norm. -/
def orbitCutoff (H : ℝ) : Finset Orbit :=
  (finite_setOf_sIntegerOrbitNorm_le K Sset Γ H).toFinset

omit [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] in
@[simp] theorem mem_orbitCutoff (H : ℝ) (q : Orbit) :
    q ∈ orbitCutoff K S Γ H ↔ (sIntegerOrbitNorm K Sset Γ q).val ≤ H := by
  simp only [orbitCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- The same ball in full exterior-ideal and original-unit-sector coordinates. -/
def sectorCutoff (H : ℝ) : Finset (Ext × CanonicalSectors.UnitClasses K Sset Γ) :=
  (orbitCutoff K S Γ H).preimage (CanonicalSectors.rowOrbit K Sset Γ D)
    (CanonicalSectors.rowOrbit_injective K Sset Γ D).injOn

omit [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] in
@[simp] theorem mem_sectorCutoff (H : ℝ)
    (x : Ext × CanonicalSectors.UnitClasses K Sset Γ) :
    x ∈ sectorCutoff K S D Γ H ↔ (x.1.val.val.absNorm : ℝ) ≤ H := by
  simp only [sectorCutoff, Finset.mem_preimage, mem_orbitCutoff,
    CanonicalSectors.rowOrbit_norm]

/-- One actual Fourier-side orbital summand at the divisor's actual radius. -/
def dualTerm (b : ActualMaskedPoissonBlock K S Γ)
    (δ : Finset (HeightOneSpectrum OS)) (q : Orbit) : ℂ :=
  sIntegerPeriodicFourierProfileTerm K S Γ μv D.different_outside
    b.localTest b.profile b.modulus b.modulus_ne_zero b.coefficient b.invariant
    (sIntegerMaskGenerator K Sset δ).val
    (sIntegerMaskDualRadius K S b.modulus b.modulus_ne_zero b.radius
      (sIntegerMaskGenerator K Sset δ)) q

theorem dual_eq_tsum (b : ActualMaskedPoissonBlock K S Γ)
    (δ : Finset (HeightOneSpectrum OS)) :
    b.dual μv D.different_outside δ = ∑' q, dualTerm K S D Γ μv b δ q := rfl

def primitiveRetained (b : ActualMaskedPoissonBlock K S Γ)
    (δ : Finset (HeightOneSpectrum OS)) (H : ℝ) : ℂ :=
  ∑ q ∈ orbitCutoff K S Γ H, dualTerm K S D Γ μv b δ q

/-- A genuine high-frequency series, not a name for an unproved error bound. -/
def primitiveTail (b : ActualMaskedPoissonBlock K S Γ)
    (δ : Finset (HeightOneSpectrum OS)) (H : ℝ) : ℂ :=
  ∑' q : {q : Orbit // H < (sIntegerOrbitNorm K Sset Γ q).val},
    dualTerm K S D Γ μv b δ q.val

def retainedDual (b : ActualMaskedPoissonBlock K S Γ) (H : ℝ) : ℂ :=
  ∑ δ ∈ b.mask.powerset, b.divisorCoefficient δ *
    (b.prefactor δ * primitiveRetained K S D Γ μv b δ H)

def dualTail (b : ActualMaskedPoissonBlock K S Γ) (H : ℝ) : ℂ :=
  ∑ δ ∈ b.mask.powerset, b.divisorCoefficient δ *
    (b.prefactor δ * primitiveTail K S D Γ μv b δ H)

theorem primitiveRetained_eq_sectors (b : ActualMaskedPoissonBlock K S Γ)
    (δ : Finset (HeightOneSpectrum OS)) (H : ℝ) :
    primitiveRetained K S D Γ μv b δ H =
      ∑ x ∈ sectorCutoff K S D Γ H,
        dualTerm K S D Γ μv b δ (CanonicalSectors.rowOrbit K Sset Γ D x) := by
  symm
  apply Finset.sum_bij (fun x _ => CanonicalSectors.rowOrbit K Sset Γ D x)
  · intro x hx
    simpa only [mem_orbitCutoff, CanonicalSectors.rowOrbit_norm] using
      (mem_sectorCutoff K S D Γ H x).mp hx
  · intro x hx y hy hxy
    exact CanonicalSectors.rowOrbit_injective K Sset Γ D hxy
  · intro q hq
    obtain ⟨x, rfl⟩ := CanonicalSectors.rowOrbit_surjective K Sset Γ D q
    exact ⟨x, by simpa only [mem_sectorCutoff, mem_orbitCutoff,
      CanonicalSectors.rowOrbit_norm] using hq, rfl⟩
  · intro x hx
    rfl

variable {σ : Type*}

def canonicalRetained (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N), pairWeight K S D C f p *
    retainedDual K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) H

def canonicalTail (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N), pairWeight K S D C f p *
    dualTail K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) H

def canonicalPrincipalRetained (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ principalPairs K S D B N, pairWeight K S D C f p *
    retainedDual K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) H

def canonicalPrincipalTail (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ principalPairs K S D B N, pairWeight K S D C f p *
    dualTail K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) H

def nonprincipalPairs (B N : Finset Ext) : Finset ((Ext × Ext) × (Ext × Ext)) :=
  ((B ×ˢ N) ×ˢ (B ×ˢ N)).filter (fun p =>
    activeSupport (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
      (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1) ≠ ∅)

def canonicalNonprincipalRetained (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ nonprincipalPairs K S D B N, pairWeight K S D C f p *
    retainedDual K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) H

def canonicalNonprincipalTail (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ nonprincipalPairs K S D B N, pairWeight K S D C f p *
    dualTail K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) H

/-- The coupled empty-conductor indicator is subtracted outside the separated columns. -/
theorem canonicalNonprincipalRetained_eq_sub (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    canonicalNonprincipalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H =
      canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H -
        canonicalPrincipalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H := by
  apply eq_sub_iff_add_eq.mpr
  unfold canonicalNonprincipalRetained canonicalRetained canonicalPrincipalRetained
    nonprincipalPairs principalPairs
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases he : activeSupport (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
      (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1) = ∅
  · simp [he]
  · simp [he]

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem summable_norm_dualTerm (b : ActualMaskedPoissonBlock K S Γ)
    (δ : Finset (HeightOneSpectrum OS)) :
    Summable (fun q => ‖dualTerm K S D Γ μv b δ q‖) := by
  have hclosure := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv b.localTest b.localTest_locallyConstant b.localTest_compactSupport
  exact summable_norm_sIntegerWeightedOrbitalProfile K S Γ
    (traceSchwartzFourier K b.profile) (sIntegerFiniteFourierTestFunction K S μv b.localTest)
    hclosure.1.continuous hclosure.2
    (sIntegerMaskDualRadius K S b.modulus b.modulus_ne_zero b.radius
      (sIntegerMaskGenerator K Sset δ))
    (sIntegerPeriodicFourierOrbitWeight K Sset D.different_outside Γ b.modulus
      b.modulus_ne_zero b.coefficient b.invariant (sIntegerMaskGenerator K Sset δ).val)
    (sIntegerPeriodicResidueL1 K Sset b.modulus b.modulus_ne_zero
      (fun a => b.coefficient
        (Ideal.Quotient.mk _ (sIntegerMaskGenerator K Sset δ).val * a)))
    (norm_sIntegerPeriodicFourierOrbitWeight_le_pullback_L1 K Sset D.different_outside Γ
      b.modulus b.modulus_ne_zero b.coefficient b.invariant
      (sIntegerMaskGenerator K Sset δ).val)

include ν in
theorem dual_eq_retained_add_tail (b : ActualMaskedPoissonBlock K S Γ)
    (δ : Finset (HeightOneSpectrum OS)) (H : ℝ) :
    b.dual μv D.different_outside δ =
      primitiveRetained K S D Γ μv b δ H + primitiveTail K S D Γ μv b δ H := by
  rw [dual_eq_tsum]
  have hs := (summable_norm_dualTerm K S D Γ μv ν b δ).of_norm
  have he := hs.sum_add_tsum_subtype_compl (orbitCutoff K S Γ H)
  have ht : (∑' q : {q : Orbit // q ∉ orbitCutoff K S Γ H},
      dualTerm K S D Γ μv b δ q.val) =
      ∑' q : {q : Orbit // H < (sIntegerOrbitNorm K Sset Γ q).val},
        dualTerm K S D Γ μv b δ q.val :=
    tsum_congr_subtype _ (fun q => by simp only [mem_orbitCutoff, not_le])
  rw [ht] at he
  exact he.symm

include ν in
theorem nonzeroDual_eq_retained_add_tail (b : ActualMaskedPoissonBlock K S Γ) (H : ℝ) :
    nonzeroDual K S D Γ μv b =
      retainedDual K S D Γ μv b H + dualTail K S D Γ μv b H := by
  unfold nonzeroDual retainedDual dualTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [dual_eq_retained_add_tail K S D Γ μv ν b δ H]
  ring

include ν in
theorem canonicalDual_eq_retained_add_tail (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    canonicalDual K S D Γ hΓ μv C f B N φ h hlc hcs M R =
      canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H +
        canonicalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H := by
  unfold canonicalDual canonicalRetained canonicalTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [nonzeroDual_eq_retained_add_tail K S D Γ μv ν]
  ring

include ν in
theorem nonprincipalDual_eq_retained_add_tail (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    canonicalNonprincipalDual K S D Γ hΓ μv C f B N φ h hlc hcs M R =
      canonicalNonprincipalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H +
        canonicalNonprincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H := by
  unfold canonicalNonprincipalDual canonicalNonprincipalRetained canonicalNonprincipalTail
    nonprincipalPairs
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [nonzeroDual_eq_retained_add_tail K S D Γ μv ν]
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstDualTruncation

end
