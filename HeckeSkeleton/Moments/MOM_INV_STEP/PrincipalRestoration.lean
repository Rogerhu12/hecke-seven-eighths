import HeckeSkeleton.Moments.MOM_INV_STEP.FirstDualTruncation

/-!
# Restore the complete principal Fourier slice

The principal retained slice is obtained from its own genuine Poisson
identity: physical principal source minus both additive zero terms minus
its genuine tail. Thus removing the coupled principal locus before
separating independent columns does not silently discard its nonzero
Fourier frequencies.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalRestoration

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open CanonicalBlock CanonicalPoissonSplit PrincipalSource
  PrimitivePoissonSource ConductorMasks FirstDualTruncation
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

def canonicalPrincipalTail (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ principalPairs K S D B N, pairWeight K S D C f p *
    dualTail K S D Γ μv (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) H

theorem canonicalTail_eq_nonprincipal_add_principal (C : ColumnData K S σ)
    (f : Ext) (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    canonicalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H =
      canonicalNonprincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H +
      canonicalPrincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H := by
  unfold canonicalTail canonicalNonprincipalTail canonicalPrincipalTail principalPairs nonprincipalPairs
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases he : activeSupport (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
      (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1) = ∅ <;> simp only [he, ite_true,
        not_true_eq_false, ite_false, zero_add, add_zero, ne_eq, not_false_eq_true]

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem principalSource_eq_retained_add_zeros_add_tail (C : ColumnData K S σ)
    (f : Ext) (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs M R =
      canonicalPrincipalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H +
      canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs M R +
      canonicalPrincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H := by
  rw [canonicalPrincipal_eq_principalPairs]
  unfold canonicalPrincipalSource canonicalPrincipalRetained canonicalPrincipalTail
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ActualMaskedPoissonBlock.physical_eq_transformed μv D.different_outside ν μ,
    pair_transformed_split K S D Γ hΓ μv p.1 p.2 φ h hlc hcs M R,
    nonzeroDual_eq_retained_add_tail K S D Γ μv ν _ H]
  ring

include ν μ in
theorem principalRetained_eq_physical_sub_zeros_sub_tail (C : ColumnData K S σ)
    (f : Ext) (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    canonicalPrincipalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H =
      canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs M R -
      canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs M R -
      canonicalPrincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H := by
  have he := principalSource_eq_retained_add_zeros_add_tail K S D Γ hΓ μv ν μ
    C f B N φ h hlc hcs M R H
  linear_combination -he

include ν μ in
theorem principalRetained_norm_le (C : ColumnData K S σ)
    (f : Ext) (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    ‖canonicalPrincipalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H‖ ≤
      ‖canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs M R‖ +
      ‖canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs M R‖ +
      ‖canonicalPrincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H‖ := by
  rw [principalRetained_eq_physical_sub_zeros_sub_tail K S D Γ hΓ μv ν μ
    C f B N φ h hlc hcs M R H]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)

include ν μ in
/-- The complete original parent is bounded by the independent full
retained source plus actual principal and tail errors. -/
theorem canonicalParent_norm_le_fullSource_and_principal (C : ColumnData K S σ)
    (f : Ext) (B N : Finset Ext) (hN : ∀ n ∈ N, Squarefree n.val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    ‖canonicalCubeEnergy K S D Γ C f B N φ h M R‖ ≤
      ‖canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H‖ +
      2 * ‖canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs M R‖ +
      ‖canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs M R‖ +
      ‖canonicalPrincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H‖ +
      ‖canonicalNonprincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H‖ := by
  rw [canonicalCubeEnergy_eq_nonprincipal_add_principalSource K S D Γ hΓ μv ν μ
    C f B N hN φ h hlc hcs M R,
    nonprincipalDual_eq_retained_add_tail K S D Γ hΓ μv ν C f B N φ h hlc hcs M R H,
    canonicalNonprincipalRetained_eq_sub K S D Γ hΓ μv C f B N φ h hlc hcs M R H]
  have hp := principalRetained_norm_le K S D Γ hΓ μv ν μ C f B N φ h hlc hcs M R H
  calc
    _ ≤ (‖canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H‖ +
          ‖canonicalPrincipalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H‖ +
          ‖canonicalNonprincipalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H‖) +
          ‖canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs M R‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalRestoration

end
