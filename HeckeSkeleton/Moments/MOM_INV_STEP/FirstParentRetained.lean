import HeckeSkeleton.Moments.MOM_INV_STEP.FirstDualTruncation
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstPoissonNormalization

/-!
# The entire retained parent is the sum of its actual first-source slices

This equality keeps every original cube pair, every computed extraction
key, every true mask divisor, and every original subgroup sector. The
principal-conductor subtraction is performed separately on this complete
source, never by a coupled restriction inside independent residual columns.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRetained

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open PrimitivePoissonSource FirstSourceColumns FirstSourceFrozen CanonicalFirstEnergy
  FirstPoissonNormalization FirstSourcePartition FirstDualTruncation CanonicalPoissonSplit
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

def actualMask (M : Finset (HeightOneSpectrum OS)) (r₁ r₂ b₁ b₂ : Ext) :
    Finset (HeightOneSpectrum OS) :=
  M ∪ principalMask K S (pairSupport K S D r₁ r₂ b₁ b₂) (pairExponent K S r₁ r₂ b₁ b₂)

def profile (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (r₁ r₂ b₁ b₂ z : Ext) (X Y : {r : ℝ // 0 < r}) : Profile K S where
  finiteTest := sIntegerFiniteFourierTestFunction K S μv h
  finiteTest_continuous :=
    (sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv h hlc hcs).1.continuous
  finiteTest_compact :=
    (sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv h hlc hcs).2
  archTest := φ
  radius := outerRadius K S D r d r₁ r₂ b₁ b₂ z X Y
  leftScale := X
  rightScale := Y

theorem dualTerm_sector (n₁ n₂ r₁ r₂ b₁ b₂ z : Ext)
    (hslice : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂)
    (ξ : Sector) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r})
    (δ : Finset (HeightOneSpectrum OS)) (X Y : {r : ℝ // 0 < r}) :
    dualTerm K S D Γ μv
      (primitivePairBlock K S D Γ hΓ (b₁, n₁) (b₂, n₂) φ h hlc hcs M r) δ
      (CanonicalSectors.rowOrbit K Sset Γ D (z, ξ)) =
    sIntegerPeriodicDivisorFourier K Sset D.different_outside
      (primitiveModulus K S D (pairSupport K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂))
      (primitiveModulus_ne_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂))
      (primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂))
      (sIntegerMaskGenerator K Sset δ).val
      (Ideal.Quotient.mk _ (CanonicalSectors.rowElement K Sset Γ D (z, ξ)).val) *
      (profile K S D μv ν φ h hlc hcs r (sIntegerMaskGenerator K Sset δ)
        r₁ r₂ b₁ b₂ z X Y).value K S
        (residualIdeal K S D n₁ n₂ b₁ b₂ false).val
        (residualIdeal K S D n₁ n₂ b₁ b₂ true).val := by
  unfold dualTerm sIntegerPeriodicFourierProfileTerm
  rw [show CanonicalSectors.rowOrbit K Sset Γ D (z, ξ) =
    Quotient.mk _ (CanonicalSectors.rowElement K Sset Γ D (z, ξ)) from rfl,
    sIntegerPeriodicFourierOrbitWeight_mk]
  congr 1
  apply congrArg (sUnitOrbitalProfile K Sset
    (sLocalTensorTestFunction K Sset (traceSchwartzFourier K φ)
      (sIntegerFiniteFourierTestFunction K S μv h)))
  apply Subtype.ext
  change (sIntegerMaskDualRadius K S
    (primitiveModulus K S D (pairSupport K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂))
    (primitiveModulus_ne_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂)) r (sIntegerMaskGenerator K Sset δ)).val *
      (sIntegerOrbitNorm K Sset Γ (CanonicalSectors.rowOrbit K Sset Γ D (z, ξ))).val = _
  rw [CanonicalSectors.rowOrbit_norm]
  exact dualRadius_normalized K S D n₁ n₂ r₁ r₂ b₁ b₂ z hslice r
    (sIntegerMaskGenerator K Sset δ) X Y

/-- The actual prefactor times one Fourier orbital term, before any norm. -/
def pairTerm (n₁ n₂ b₁ b₂ : Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r})
    (δ : Finset (HeightOneSpectrum OS)) (k : Ext × Sector) : ℂ :=
  (primitivePairBlock K S D Γ hΓ (b₁,n₁) (b₂,n₂) φ h hlc hcs M r).prefactor δ *
    dualTerm K S D Γ μv
      (primitivePairBlock K S D Γ hΓ (b₁,n₁) (b₂,n₂) φ h hlc hcs M r) δ
      (CanonicalSectors.rowOrbit K Sset Γ D k)

variable {σ : Type*}

theorem pair_term_normalized (C : CanonicalBlock.ColumnData K S σ) (f : Ext)
    (n₁ n₂ r₁ r₂ b₁ b₂ z : Ext)
    (hslice : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂)
    (ξ : Sector) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r})
    (δ : Finset (HeightOneSpectrum OS)) (X Y : {r : ℝ // 0 < r}) :
    pairWeight K S D C f ((b₁,n₁),(b₂,n₂)) *
      ((primitivePairBlock K S D Γ hΓ (b₁,n₁) (b₂,n₂) φ h hlc hcs M r).prefactor δ *
        dualTerm K S D Γ μv
          (primitivePairBlock K S D Γ hΓ (b₁,n₁) (b₂,n₂) φ h hlc hcs M r) δ
          (CanonicalSectors.rowOrbit K Sset Γ D (z,ξ))) =
      (outerFactor K S D r (sIntegerMaskGenerator K Sset δ) r₁ r₂ b₁ b₂ : ℂ) *
        (CanonicalBlock.canonicalColumn K S D C f b₁ n₁ *
          conj (CanonicalBlock.canonicalColumn K S D C f b₂ n₂) *
          pairFourier K S D n₁ n₂ b₁ b₂ (sIntegerMaskGenerator K Sset δ).val
            (CanonicalSectors.rowElement K Sset Γ D (z,ξ)).val *
          normWeight K (residualIdeal K S D n₁ n₂ b₁ b₂ false).val *
          conj (normWeight K (residualIdeal K S D n₁ n₂ b₁ b₂ true).val) *
          (profile K S D μv ν φ h hlc hcs r (sIntegerMaskGenerator K Sset δ)
            r₁ r₂ b₁ b₂ z X Y).value K S
            (residualIdeal K S D n₁ n₂ b₁ b₂ false).val
            (residualIdeal K S D n₁ n₂ b₁ b₂ true).val) := by
  rw [dualTerm_sector K S D Γ hΓ μv ν n₁ n₂ r₁ r₂ b₁ b₂ z hslice ξ
    φ h hlc hcs M r δ X Y]
  have hfac := prefactor_fourier K S D n₁ n₂ b₁ b₂ r
    (sIntegerMaskGenerator K Sset δ) (CanonicalSectors.rowElement K Sset Γ D (z,ξ)).val
  have hfrozen : outerFactor K S D r (sIntegerMaskGenerator K Sset δ) n₁ n₂ b₁ b₂ =
      outerFactor K S D r (sIntegerMaskGenerator K Sset δ) r₁ r₂ b₁ b₂ := by
    unfold outerFactor
    rw [cubeNorm_eq K S D n₁ n₂ r₁ r₂ b₁ b₂ hslice]
  rw [hfrozen] at hfac
  change pairWeight K S D C f ((b₁,n₁),(b₂,n₂)) *
    (_ * (_ * _)) = _
  rw [← mul_assoc
    (sIntegerMaskPoissonFactor K S
      (primitiveModulus K S D (pairSupport K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂))
      (primitiveModulus_ne_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂)) r (sIntegerMaskGenerator K Sset δ))]
  rw [hfac]
  unfold pairWeight
  ring

private theorem sum_four_comm {α β γ ι : Type*}
    (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset ι)
    (f : α → β → γ → ι → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d) =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc
    _ = ∑ p ∈ A ×ˢ B, ∑ q ∈ C ×ˢ D, f p.1 p.2 q.1 q.2 := by
      simp only [Finset.sum_product]
    _ = ∑ q ∈ C ×ˢ D, ∑ p ∈ A ×ˢ B, f p.1 p.2 q.1 q.2 := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_product]

def sliceValue (C : CanonicalBlock.ColumnData K S σ) (f : Ext) (N₁ N₂ : Finset Ext)
    (r₁ r₂ b₁ b₂ : Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r})
    (H : ℝ) (X Y : {r : ℝ // 0 < r}) : ℂ :=
  ∑ δ ∈ (actualMask K S D M r₁ r₂ b₁ b₂).powerset,
    ∑ z ∈ sectorCutoff K S D Γ H,
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
    (H : ℝ) (X Y : {r : ℝ // 0 < r}) :
    (∑ n₁ ∈ N₁, ∑ n₂ ∈ N₂,
      if SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ then
        pairWeight K S D C f ((b₁,n₁),(b₂,n₂)) *
          retainedDual K S D Γ μv
            (primitivePairBlock K S D Γ hΓ (b₁,n₁) (b₂,n₂) φ h hlc hcs M r) H
      else 0) =
      sliceValue K S D Γ μv ν C f N₁ N₂ r₁ r₂ b₁ b₂ φ h hlc hcs M r H X Y := by
  let A := (actualMask K S D M r₁ r₂ b₁ b₂).powerset
  let Z := sectorCutoff K S D Γ H
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
          retainedDual K S D Γ μv
            (primitivePairBlock K S D Γ hΓ (b₁,n₁) (b₂,n₂) φ h hlc hcs M r) H
        else 0) = ∑ δ ∈ A, ∑ z ∈ Z, F n₁ n₂ δ z := by
    by_cases hs : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂
    · rw [if_pos hs]
      unfold retainedDual
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
      change _ = _
      simp only [ActualMaskedPoissonBlock.divisorCoefficient]
      linear_combination (moebius (IdealMobiusMask.primeProduct δ) : ℂ) * he
    · simp only [if_neg hs, F, mul_zero, Finset.sum_const_zero]
  simp_rw [hpoint]
  rw [sum_four_comm N₁ N₂ A Z F]
  unfold sliceValue originalSource
  simp only [Finset.mul_sum]
  rfl

theorem canonicalRetained_eq_slices (C : CanonicalBlock.ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : ℝ)
    (X Y : Ext → Ext → Ext → Ext → {r : ℝ // 0 < r}) :
    canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs M r H =
      ∑ b₁ ∈ B, ∑ b₂ ∈ B, ∑ κ : keys K S N N b₁ b₂,
        sliceValue K S D Γ μv ν C f N N
          (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂
          φ h hlc hcs M r H
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
    (X (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂)
    (Y (anchor K S N N b₁ b₂ κ).1 (anchor K S N N b₁ b₂ κ).2 b₁ b₂)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRetained

end

