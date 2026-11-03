import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRetained
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalAdaptiveTail

/-!
# Literal first Poisson truncation at frozen arithmetic cutoffs

Every source pair uses the cutoff of its genuine extraction slice and
actual mask divisor. The complete original source is reindexed exactly;
no cutoff depends on an old label, residual column, or sector.
-/

noncomputable section
namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstAdaptiveTruncation
open NumberField IsDedekindDomain UniqueFactorizationMonoid HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open PrimitivePoissonSource FirstSourceColumns FirstSourceFrozen CanonicalFirstEnergy
  FirstPoissonNormalization FirstSourcePartition FirstDualTruncation CanonicalPoissonSplit
  FirstParentRetained CanonicalBlock
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
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ


private theorem sum_four_dependent_comm {α β γ ι : Type*}
    (A : Finset α) (B : Finset β) (C : Finset γ) (E : γ → Finset ι)
    (f : α → β → γ → ι → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ E c, f a b c d) =
      ∑ c ∈ C, ∑ d ∈ E c, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ E c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ E c, f a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      calc
        _ = ∑ a ∈ A, ∑ d ∈ E c, ∑ b ∈ B, f a b c d := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

variable {σ : Type*}

def canonicalRetained (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : Ext → Ext → Ext → Ext → Finset (HeightOneSpectrum OS) → ℝ) : ℂ :=
  ∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N), pairWeight K S D C f p *
    CanonicalAdaptiveTail.retainedDual K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) (H p.1.2 p.2.2 p.1.1 p.2.1)

def canonicalTail (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : Ext → Ext → Ext → Ext → Finset (HeightOneSpectrum OS) → ℝ) : ℂ :=
  ∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N), pairWeight K S D C f p *
    CanonicalAdaptiveTail.dualTail K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R) (H p.1.2 p.2.2 p.1.1 p.2.1)

include ν in
theorem canonicalDual_eq_retained_add_tail (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : Ext → Ext → Ext → Ext → Finset (HeightOneSpectrum OS) → ℝ) :
    canonicalDual K S D Γ hΓ μv C f B N φ h hlc hcs M R =
      canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M R H +
        canonicalTail K S D Γ hΓ μv C f B N φ h hlc hcs M R H := by
  unfold canonicalDual canonicalRetained canonicalTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [CanonicalAdaptiveTail.nonzeroDual_eq_retained_add_tail K S D Γ μv ν]
  ring

def sliceValue (C : CanonicalBlock.ColumnData K S σ) (f : Ext) (N₁ N₂ : Finset Ext)
    (r₁ r₂ b₁ b₂ : Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r})
    (H : Finset (HeightOneSpectrum OS) → ℝ) (X Y : {r : ℝ // 0 < r}) : ℂ :=
  ∑ δ ∈ (FirstParentRetained.actualMask K S D M r₁ r₂ b₁ b₂).powerset,
    ∑ z ∈ sectorCutoff K S D Γ (H δ),
      (moebius (IdealMobiusMask.primeProduct δ) : ℂ) *
        (outerFactor K S D r (sIntegerMaskGenerator K Sset δ) r₁ r₂ b₁ b₂ : ℂ) *
        originalSource K S D Γ C N₁ N₂ r₁ r₂ b₁ b₂
          (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S f)
          (CanonicalIdealRow.ofExterior K S z.1) (sIntegerMaskGenerator K Sset δ).val z.2
          (profile K S D μv ν φ h hlc hcs r (sIntegerMaskGenerator K Sset δ)
            r₁ r₂ b₁ b₂ z.1 X Y)

theorem retained_slice_eq (C : CanonicalBlock.ColumnData K S σ) (f : Ext)
    (N₁ N₂ : Finset Ext) (r₁ r₂ b₁ b₂ : Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r})
    (H : Ext → Ext → Ext → Ext → Finset (HeightOneSpectrum OS) → ℝ)
    (hH : ∀ n₁ n₂, SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ →
      H n₁ n₂ b₁ b₂ = H r₁ r₂ b₁ b₂) (X Y : {r : ℝ // 0 < r}) :
    (∑ n₁ ∈ N₁, ∑ n₂ ∈ N₂,
      if SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ then
        pairWeight K S D C f ((b₁,n₁),(b₂,n₂)) *
          CanonicalAdaptiveTail.retainedDual K S D Γ μv
            (primitivePairBlock K S D Γ hΓ (b₁,n₁) (b₂,n₂) φ h hlc hcs M r) (H n₁ n₂ b₁ b₂)
      else 0) =
      sliceValue K S D Γ μv ν C f N₁ N₂ r₁ r₂ b₁ b₂ φ h hlc hcs M r (H r₁ r₂ b₁ b₂) X Y := by
  let A := (FirstParentRetained.actualMask K S D M r₁ r₂ b₁ b₂).powerset
  let Z (δ : Finset (HeightOneSpectrum OS)) := sectorCutoff K S D Γ (H r₁ r₂ b₁ b₂ δ)
  let F (n₁ n₂ : Ext) (δ : Finset (HeightOneSpectrum OS)) (z : Ext × Sector) : ℂ :=
    (moebius (IdealMobiusMask.primeProduct δ) : ℂ) *
      (outerFactor K S D r (sIntegerMaskGenerator K Sset δ) r₁ r₂ b₁ b₂ : ℂ) *
      (if SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ then
        CanonicalBlock.canonicalColumn K S D C f b₁ n₁ *
          conj (CanonicalBlock.canonicalColumn K S D C f b₂ n₂) *
          pairFourier K S D n₁ n₂ b₁ b₂ (sIntegerMaskGenerator K Sset δ).val
            (CanonicalSectors.rowElement K Sset Γ D z).val *
          normWeight K (residualIdeal K S D n₁ n₂ b₁ b₂ false).val *
          conj (normWeight K (residualIdeal K S D n₁ n₂ b₁ b₂ true).val) *
          (profile K S D μv ν φ h hlc hcs r (sIntegerMaskGenerator K Sset δ)
            r₁ r₂ b₁ b₂ z.1 X Y).value K S
            (residualIdeal K S D n₁ n₂ b₁ b₂ false).val
            (residualIdeal K S D n₁ n₂ b₁ b₂ true).val else 0)
  have hpoint (n₁ n₂ : Ext) :
      (if SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ then
        pairWeight K S D C f ((b₁,n₁),(b₂,n₂)) *
          CanonicalAdaptiveTail.retainedDual K S D Γ μv
            (primitivePairBlock K S D Γ hΓ (b₁,n₁) (b₂,n₂) φ h hlc hcs M r) (H n₁ n₂ b₁ b₂)
        else 0) = ∑ δ ∈ A, ∑ z ∈ Z δ, F n₁ n₂ δ z := by
    by_cases hs : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂
    · rw [if_pos hs, hH n₁ n₂ hs]
      unfold CanonicalAdaptiveTail.retainedDual
      simp only [primitivePairBlock, block]
      rw [FirstSourcePartition.principalMask_eq K S D n₁ n₂ r₁ r₂ b₁ b₂ hs,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro δ hδ
      rw [primitiveRetained_eq_sectors]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      dsimp only [F]
      rw [if_pos hs]
      have he := pair_term_normalized K S D Γ hΓ μv ν C f n₁ n₂ r₁ r₂ b₁ b₂ z.1
        hs z.2 φ h hlc hcs M r δ X Y
      simp only [ActualMaskedPoissonBlock.divisorCoefficient]
      dsimp only [primitivePairBlock, PrimitivePoissonSource.block,
        ActualMaskedPoissonBlock.prefactor, dualTerm] at he ⊢
      linear_combination (moebius (IdealMobiusMask.primeProduct δ) : ℂ) * he
    · simp only [if_neg hs, F, mul_zero, Finset.sum_const_zero]
  simp_rw [hpoint]
  rw [sum_four_dependent_comm N₁ N₂ A Z F]
  unfold sliceValue originalSource
  simp only [Finset.mul_sum]
  rfl

theorem canonicalRetained_eq_slices (C : CanonicalBlock.ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : Ext → Ext → Ext → Ext → Finset (HeightOneSpectrum OS) → ℝ)
    (hH : ∀ n₁ n₂ r₁ r₂ b₁ b₂, SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ →
      H n₁ n₂ b₁ b₂ = H r₁ r₂ b₁ b₂)
    (X Y : Ext → Ext → Ext → Ext → {r : ℝ // 0 < r}) :
    canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M r H =
      ∑ b₁ ∈ B, ∑ b₂ ∈ B, ∑ κ : keys K S N N b₁ b₂,
        sliceValue K S D Γ μv ν C f N N
          (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂
          φ h hlc hcs M r
          (H (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂)
          (X (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂)
          (Y (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂) := by
  unfold canonicalRetained
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b₂ hb₂
  rw [sum_extraction_slices K S N N b₁ b₂]
  apply Finset.sum_congr rfl
  intro κ hκ
  exact retained_slice_eq K S D Γ hΓ μv ν C f N N
    (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂ φ h hlc hcs M r H
    (fun n₁ n₂ hs => hH n₁ n₂ _ _ b₁ b₂ hs)
    (X (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂)
    (Y (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstAdaptiveTruncation

end
