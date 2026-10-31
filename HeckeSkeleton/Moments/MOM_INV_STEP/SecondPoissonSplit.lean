import HeckeSkeleton.Moments.MOM_INV_STEP.DivisorInverseColumn
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstDualTruncation
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalOrbitalMass

/-!
# The actual second Poisson source and its principal part

The coefficient is the independently defined intermediate inverse
coefficient. The external row mask is empty; every genuine principal
mask divisor and every original unit-group orbit remains present.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonSplit

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalPoissonSplit
  PrincipalZero PrimitivePoissonSource ConductorMasks FirstDualTruncation
  PrincipalOrbitalMass FirstInversePoisson
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

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "e" => unitIdeal K S

def principalPairs (T : Finset Ext) : Finset (Ext × Ext) :=
  (T ×ˢ T).filter fun p =>
    activeSupport (pairSupport K S D p.1 p.2 e e).support
      (pairExponent K S p.1 p.2 e e) = ∅

def nonprincipalPairs (T : Finset Ext) : Finset (Ext × Ext) :=
  (T ×ˢ T) \ principalPairs K S D T

def sourceWeight (a : Ext → ℂ) (p : Ext × Ext) : ℂ := star (a p.1) * a p.2

abbrev pairBlock (p : Ext × Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :=
  primitivePairBlock K S D Γ hΓ (e, p.1) (e, p.2) φ h hlc hcs ∅ r

def physicalPrincipal (a : Ext → ℂ) (T : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) : ℂ :=
  ∑ p ∈ principalPairs K S D T,
    sourceWeight K S a p * (pairBlock K S D Γ hΓ p φ h hlc hcs r).physical

theorem principalPairs_subset (T : Finset Ext) :
    principalPairs K S D T ⊆ T ×ˢ T := Finset.filter_subset _ _

theorem principalPair_diagonal (T : Finset Ext)
    (hT : ∀ n ∈ T, Squarefree n.val.val) (p : Ext × Ext)
    (hp : p ∈ principalPairs K S D T) : p.1 = p.2 := by
  obtain ⟨hmem, hzero⟩ := Finset.mem_filter.mp hp
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hmem
  exact PrincipalDiagonal.columns_eq_of_principal K S D p.1 p.2 e e
    (hT p.1 h₁) (hT p.2 h₂) hzero

theorem principalPairs_card_le (T : Finset Ext)
    (hT : ∀ n ∈ T, Squarefree n.val.val) :
    (principalPairs K S D T).card ≤ T.card := by
  let f : principalPairs K S D T → T := fun p =>
    ⟨p.val.1, (Finset.mem_product.mp (principalPairs_subset K S D T p.property)).1⟩
  have hf : Function.Injective f := by
    intro p q he
    have hleft : p.val.1 = q.val.1 := congrArg Subtype.val he
    have hright : p.val.2 = q.val.2 :=
      (principalPair_diagonal K S D T hT p.val p.property).symm.trans
        (hleft.trans (principalPair_diagonal K S D T hT q.val q.property))
    exact Subtype.ext (Prod.ext hleft hright)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem physicalPrincipal_norm_le (a : Ext → ℂ) (T : Finset Ext)
    (hT : ∀ n ∈ T, Squarefree n.val.val) (L : ℝ) (hL : 0 ≤ L)
    (ha : ∀ n ∈ T, ‖a n‖ ≤ L) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :
    ‖physicalPrincipal K S D Γ hΓ a T φ h hlc hcs r‖ ≤
      (T.card : ℝ) * L ^ 2 *
        absoluteRowMass K Sset Γ φ (sIntegerFiniteTestFunction K S h) r := by
  letI : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K) :=
    fun v => borel (v.adicCompletion K)
  letI : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K) :=
    fun _ => ⟨rfl⟩
  let z := absoluteRowMass K Sset Γ φ (sIntegerFiniteTestFunction K S h) r
  have hz : 0 ≤ z := tsum_nonneg (fun _ => norm_nonneg _)
  have hp (p : Ext × Ext) (hmem : p ∈ principalPairs K S D T) :
      ‖sourceWeight K S a p * (pairBlock K S D Γ hΓ p φ h hlc hcs r).physical‖ ≤
      L ^ 2 * z := by
    obtain ⟨hprod, hzero⟩ := Finset.mem_filter.mp hmem
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hprod
    have hc : ‖sourceWeight K S a p‖ ≤ L ^ 2 := by
      rw [sourceWeight, norm_mul, norm_star, pow_two]
      exact mul_le_mul (ha p.1 h₁) (ha p.2 h₂) (norm_nonneg _) hL
    have hb : ‖(pairBlock K S D Γ hΓ p φ h hlc hcs r).physical‖ ≤ z :=
      principal_physical_norm_le_profile_mass K S D Γ hΓ
        (pairSupport K S D p.1 p.2 e e) (pairExponent K S p.1 p.2 e e)
        hzero φ h hlc hcs ∅ r
    rw [norm_mul]
    exact mul_le_mul hc hb (norm_nonneg _) (sq_nonneg _)
  unfold physicalPrincipal
  calc
    _ ≤ ∑ p ∈ principalPairs K S D T,
        ‖sourceWeight K S a p * (pairBlock K S D Γ hΓ p φ h hlc hcs r).physical‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ principalPairs K S D T, L ^ 2 * z := Finset.sum_le_sum hp
    _ = ((principalPairs K S D T).card : ℝ) * (L ^ 2 * z) := by simp
    _ ≤ (T.card : ℝ) * (L ^ 2 * z) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (sq_nonneg _) hz)
      exact_mod_cast principalPairs_card_le K S D T hT
    _ = _ := by dsimp only [z]; ring

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

def retainedSource (a : Ext → ℂ) (P : Finset (Ext × Ext)) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ P, sourceWeight K S a p *
    retainedDual K S D Γ μv (pairBlock K S D Γ hΓ p φ h hlc hcs r) H

def tailSource (a : Ext → ℂ) (P : Finset (Ext × Ext)) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ P, sourceWeight K S a p *
    dualTail K S D Γ μv (pairBlock K S D Γ hΓ p φ h hlc hcs r) H

def additiveZeros (a : Ext → ℂ) (T : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) : ℂ :=
  ∑ p ∈ T ×ˢ T, sourceWeight K S a p *
    pairPrincipal K S D Γ hΓ μv (e, p.1) (e, p.2) φ h hlc hcs ∅ r

theorem additiveZeros_eq_principalPairs (a : Ext → ℂ) (T : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :
    additiveZeros K S D Γ hΓ μv a T φ h hlc hcs r =
      ∑ p ∈ principalPairs K S D T, sourceWeight K S a p *
        pairPrincipal K S D Γ hΓ μv (e, p.1) (e, p.2) φ h hlc hcs ∅ r := by
  unfold additiveZeros
  symm
  apply Finset.sum_subset (principalPairs_subset K S D T)
  intro p hp hnot
  have hactive : activeSupport (pairSupport K S D p.1 p.2 e e).support
      (pairExponent K S p.1 p.2 e e) ≠ ∅ := by
    intro he
    exact hnot (Finset.mem_filter.mpr ⟨hp, he⟩)
  rw [pairPrincipal_eq_zero K S D Γ hΓ μv (e, p.1) (e, p.2) φ h hlc hcs ∅ r hactive,
    mul_zero]

theorem nonprincipalRetained_eq_sub (a : Ext → ℂ) (T : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) (H : ℝ) :
    retainedSource K S D Γ hΓ μv a (nonprincipalPairs K S D T) φ h hlc hcs r H =
      retainedSource K S D Γ hΓ μv a (T ×ˢ T) φ h hlc hcs r H -
        retainedSource K S D Γ hΓ μv a (principalPairs K S D T) φ h hlc hcs r H := by
  unfold retainedSource nonprincipalPairs
  exact Finset.sum_sdiff_eq_sub (principalPairs_subset K S D T)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem pair_transformed_head_tail (p : Ext × Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) (H : ℝ) :
    (pairBlock K S D Γ hΓ p φ h hlc hcs r).transformed μv D.different_outside =
      retainedDual K S D Γ μv (pairBlock K S D Γ hΓ p φ h hlc hcs r) H +
      pairPrincipal K S D Γ hΓ μv (e, p.1) (e, p.2) φ h hlc hcs ∅ r +
      dualTail K S D Γ μv (pairBlock K S D Γ hΓ p φ h hlc hcs r) H := by
  rw [pair_transformed_split K S D Γ hΓ μv (e, p.1) (e, p.2) φ h hlc hcs ∅ r,
    nonzeroDual_eq_retained_add_tail K S D Γ μv ν _ H]
  ring

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem physicalPrincipal_eq_retained_add_zeros_add_tail
    (a : Ext → ℂ) (T : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) (H : ℝ) :
    physicalPrincipal K S D Γ hΓ a T φ h hlc hcs r =
      retainedSource K S D Γ hΓ μv a (principalPairs K S D T) φ h hlc hcs r H +
      additiveZeros K S D Γ hΓ μv a T φ h hlc hcs r +
      tailSource K S D Γ hΓ μv a (principalPairs K S D T) φ h hlc hcs r H := by
  rw [additiveZeros_eq_principalPairs]
  unfold physicalPrincipal retainedSource tailSource
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ActualMaskedPoissonBlock.physical_eq_transformed μv D.different_outside ν μ,
    pair_transformed_head_tail K S D Γ hΓ μv ν p φ h hlc hcs r H]
  ring

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

include ν μ in
/-- Exact second Poisson, starting from the actual retained-divisor
inverse energy. There is no source-identity or energy hypothesis. -/
theorem genuine_second_split (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) (H : ℝ) :
    DivisorInverseColumn.weightedEnergy K S Γ D C γ j d φ h ∅ r =
      retainedSource K S D Γ hΓ μv (DivisorInverseColumn.coefficient K S D C γ j d)
        (C.columns γ ×ˢ C.columns γ) φ h hlc hcs r H +
      additiveZeros K S D Γ hΓ μv (DivisorInverseColumn.coefficient K S D C γ j d)
        (C.columns γ) φ h hlc hcs r +
      tailSource K S D Γ hΓ μv (DivisorInverseColumn.coefficient K S D C γ j d)
        (C.columns γ ×ˢ C.columns γ) φ h hlc hcs r H := by
  rw [DivisorInverseColumn.genuine_second_poisson K S Γ D hΓ μv ν μ
    C γ j d φ h hlc hcs ∅ r]
  unfold retainedSource additiveZeros tailSource sourceWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  change star (DivisorInverseColumn.coefficient K S D C γ j d p.1) *
    DivisorInverseColumn.coefficient K S D C γ j d p.2 *
    (pairBlock K S D Γ hΓ p φ h hlc hcs r).transformed μv D.different_outside = _
  rw [pair_transformed_head_tail K S D Γ hΓ μv ν p φ h hlc hcs r H]
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonSplit

end
