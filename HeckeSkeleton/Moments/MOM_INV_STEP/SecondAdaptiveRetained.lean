import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveCutoff
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRows

/-!
# Exact retained second source with common/divisor-local frequencies

The frequency pool is frozen after the actual common ideal and actual
mask divisor have been selected. It is identical for both residual
columns in that slice. The reindexing below keeps the signed coefficient
and all original unit sectors, including every principal contribution.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRetained

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CanonicalFirstEnergy
  CanonicalBlock FirstInversePoisson FirstDualTruncation PrimitivePoissonSource
  SecondSourceColumns SecondMarkedSource SecondSourceAssembly SecondSourceMasks
  SecondSourceReindexing SecondCanonicalEnergy ActualDivisorSectors ActualInverseFactors
  SecondParentRetained SecondAdaptiveCutoff
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "e" => unitIdeal K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The frequency pool may depend on the actual common ideal and its
mask divisor; it never depends on either residual column. -/
theorem sum_masks_frequencies_by_commonAt {κ : Type*}
    (N : ℝ) (hN : 0 ≤ N)
    (A : Ext → Finset (HeightOneSpectrum OS) → Finset κ)
    (F : Ext → Ext → Finset (HeightOneSpectrum OS) → κ → ℂ) :
    (∑ x₁ ∈ squarefreePool K Sset N, ∑ x₂ ∈ squarefreePool K Sset N,
      ∑ δ ∈ (FirstSourcePartition.actualMask K S D ∅ x₁ x₂ e e).powerset,
        ∑ k ∈ A (common K Sset x₁ x₂) δ, F x₁ x₂ δ k) =
      ∑ g ∈ squarefreePool K Sset N, ∑ δ ∈ (commonMask K S D g).powerset,
        ∑ k ∈ A g δ, ∑ z₁ ∈ squarefreePool K Sset (N / height K Sset g),
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
          ∑ k ∈ A (common K Sset (exteriorMul K Sset g z₁)
            (exteriorMul K Sset g z₂)) δ,
            F (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) δ k else 0) =
        ∑ δ ∈ (commonMask K S D g).powerset, ∑ k ∈ A g δ,
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
          ∑ δ ∈ (commonMask K S D g).powerset, ∑ k ∈ A g δ,
            if compatible K Sset g z₁ z₂ then
              F (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) δ k else 0 := by
      apply Finset.sum_congr rfl
      intro z₁ hz₁
      apply Finset.sum_congr rfl
      intro z₂ hz₂
      exact hp z₁ hz₁ z₂ hz₂
    _ = ∑ δ ∈ (commonMask K S D g).powerset,
        ∑ z₁ ∈ squarefreePool K Sset (N / height K Sset g),
          ∑ z₂ ∈ squarefreePool K Sset (N / height K Sset g),
            ∑ k ∈ A g δ,
              if compatible K Sset g z₁ z₂ then
                F (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) δ k else 0 := by
      simp_rw [Finset.sum_comm
        (s := squarefreePool K Sset (N / height K Sset g))
        (t := (commonMask K S D g).powerset)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro δ hδ
      simp_rw [Finset.sum_comm
        (s := squarefreePool K Sset (N / height K Sset g)) (t := A g δ)]
      rfl

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- The complete finite production index with the actual local cutoff. -/
abbrev IndexAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) :=
  Σ g : squarefreePool K Sset (2 * SecondParentProduction.scale K S T),
    Σ δ : (commonMask K S D g.val).powerset, sectorCutoff K S D Γ (H g.val δ.val)

abbrev FineIndex (T : SecondParentProduction.Data K S σ Θ ψ) (Z tau : ℝ) :=
  IndexAt K S D Γ T
    (fineCutoff K S T.radius (SecondParentProduction.scale K S T) Z tau)

def selectedDivisorAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) :
    NonzeroRingElements OS := sIntegerMaskGenerator K Sset i.2.1.val

def selectedRowAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) : Ext :=
  newRowIdeal K S i.2.2.val.1 T.divisor (selectedDivisorAt K S D Γ T H i)

def selectedSectorAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) : Sector :=
  newSector K S Γ D T.divisor (selectedDivisorAt K S D Γ T H i) i.2.2.val.2

/-- Reuse of all already-defined positive column energies at one
selected source index changes only the irrelevant global cutoff field. -/
def dataAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) :
    SecondParentProduction.Data K S σ Θ ψ :=
  { T with frequencyBound := H i.1.val i.2.1.val }

def oldIndexAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) :
    SecondParentProduction.Index K S D Γ (dataAt K S D Γ T H i) :=
  ⟨i.1, i.2.1, i.2.2⟩

@[simp] theorem oldIndexAt_selectedRow (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) :
    SecondParentProduction.selectedRow K S D Γ (dataAt K S D Γ T H i)
      (oldIndexAt K S D Γ T H i) = selectedRowAt K S D Γ T H i := rfl

@[simp] theorem oldIndexAt_selectedSector (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) :
    SecondParentProduction.selectedSector K S D Γ (dataAt K S D Γ T H i)
      (oldIndexAt K S D Γ T H i) = selectedSectorAt K S D Γ T H i := rfl

theorem selectedRowAt_norm_le (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) :
    height K Sset (selectedRowAt K S D Γ T H i) ≤
      (sIntegerElementNorm K Sset T.divisor).val *
        (sIntegerElementNorm K Sset (selectedDivisorAt K S D Γ T H i)).val *
          H i.1.val i.2.1.val :=
  SecondParentRows.selectedRow_norm_le_cutoff K S D Γ
    (dataAt K S D Γ T H i) (oldIndexAt K S D Γ T H i)

theorem selectedOrbitAt_norm_le (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) :
    (sIntegerOrbitNorm K Sset Γ (CanonicalSectors.rowOrbit K Sset Γ D
      (selectedRowAt K S D Γ T H i, selectedSectorAt K S D Γ T H i))).val ≤
      (sIntegerElementNorm K Sset T.divisor).val *
        (sIntegerElementNorm K Sset (selectedDivisorAt K S D Γ T H i)).val *
          H i.1.val i.2.1.val :=
  SecondParentRows.selectedOrbit_norm_le_cutoff K S D Γ
    (dataAt K S D Γ T H i) (oldIndexAt K S D Γ T H i)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

theorem retained_pair_at (a : Ext → ℂ) (x₁ x₂ : Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) :
    (star (a x₁) * a x₂) * CanonicalAdaptiveTail.retainedDual K S D Γ μv
        (primitivePairBlock K S D Γ hΓ (e, x₁) (e, x₂) φ h hlc hcs ∅ r)
        (H (common K Sset x₁ x₂)) =
      ∑ δ ∈ (FirstSourcePartition.actualMask K S D ∅ x₁ x₂ e e).powerset,
        ∑ k ∈ sectorCutoff K S D Γ (H (common K Sset x₁ x₂) δ),
          (UniqueFactorizationMonoid.moebius (IdealMobiusMask.primeProduct δ) : ℂ) * (star (a x₁) * a x₂) *
            FirstParentRetained.pairTerm K S D Γ hΓ μv x₁ x₂ e e φ h hlc hcs ∅ r δ k := by
  unfold CanonicalAdaptiveTail.retainedDual
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [primitiveRetained_eq_sectors K S D Γ μv]
  simp only [Finset.mul_sum, ActualMaskedPoissonBlock.divisorCoefficient,
    FirstParentRetained.pairTerm]
  apply Finset.sum_congr rfl
  intro k hk
  ring

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hΓ hallowed in
/-- Every actual nonzero-frequency term is present. The only remaining
pair condition in each independent residual pool is mutual coprimality.
The original common ideal is fixed in its whole outer slice. -/
theorem retainedSourceAt_eq_fixed_common
    (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K (C.background γ) p)
    (hX : 0 < C.base ^ C.columnLength γ)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (j : Ext) (dk : NonzeroRingElements OS) (N : ℝ) (hN : 0 ≤ N)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) :
    retainedSourceAt K S D Γ hΓ μv
      (DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val)
      (squarefreePool K Sset N ×ˢ squarefreePool K Sset N) φ h hlc hcs r H =
      ∑ g ∈ squarefreePool K Sset N, ∑ δ ∈ (commonMask K S D g).powerset,
        ∑ k ∈ sectorCutoff K S D Γ (H g δ),
          (UniqueFactorizationMonoid.moebius (IdealMobiusMask.primeProduct δ) : ℂ) *
            sourceScalar K S C γ hX r δ g j dk *
            ∑ z₁ ∈ squarefreePool K Sset (N / height K Sset g),
              ∑ z₂ ∈ squarefreePool K Sset (N / height K Sset g),
                if IsCoprime z₁.val.val z₂.val.val then
                  star (forwardColumn K S D Γ C γ G g j k.1 k.2 dk
                    (sIntegerMaskGenerator K Sset δ) z₁) *
                    forwardColumn K S D Γ C γ G g j k.1 k.2 dk
                      (sIntegerMaskGenerator K Sset δ) z₂ *
                    (sourceProfile K S μv ν C γ hX φ h hlc hcs r δ k.1 g).value K S
                      z₁.val z₂.val else 0 := by
  unfold retainedSourceAt SecondPoissonSplit.sourceWeight
    SecondPoissonSplit.pairBlock
  rw [Finset.sum_product]
  simp_rw [retained_pair_at K S D Γ hΓ μv]
  rw [sum_masks_frequencies_by_commonAt K S D N hN]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro δ hδ
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z₁ hz₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z₂ hz₂
  have hgs := squarefreePool_squarefree K Sset hg
  have hz₁s := squarefreePool_squarefree K Sset hz₁
  have hz₂s := squarefreePool_squarefree K Sset hz₂
  by_cases hc₁ : IsCoprime g.val.val z₁.val.val
  · by_cases hc₂ : IsCoprime g.val.val z₂.val.val
    · by_cases hc : IsCoprime z₁.val.val z₂.val.val
      · rw [if_pos ⟨hc₁, hc₂, hc⟩, if_pos hc]
        have hf := SecondDyadicReindexing.factors_of_products K Sset g z₁ z₂
          hgs hz₁s hz₂s hc₁ hc₂ hc
        have hp := weighted_pairTerm_eq K S D Γ hΓ μv ν hallowed C γ G hcal hbg hX hW
          (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂) j
          (SecondSourceReindexing.squarefree_exteriorMul K Sset g z₁ hgs hz₁s hc₁)
          (SecondSourceReindexing.squarefree_exteriorMul K Sset g z₂ hgs hz₂s hc₂)
          dk φ h hlc hcs r δ k
        rw [hf.1, hf.2.1, hf.2.2] at hp
        calc
          _ = (UniqueFactorizationMonoid.moebius (IdealMobiusMask.primeProduct δ) : ℂ) *
              ((star (DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val
                  (exteriorMul K Sset g z₁)) *
                DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val
                  (exteriorMul K Sset g z₂)) *
                FirstParentRetained.pairTerm K S D Γ hΓ μv
                  (exteriorMul K Sset g z₁) (exteriorMul K Sset g z₂)
                  e e φ h hlc hcs ∅ r δ k) := by ring
          _ = _ := by rw [hp]; ring
      · simp only [hc, and_false, if_false, mul_zero]
    · have hz := forwardColumn_zero K S D Γ C γ G g j k.1 k.2 dk
        (sIntegerMaskGenerator K Sset δ) z₂ hc₂
      simp only [hc₂, false_and, and_false, if_false, hz, mul_zero, ite_self]
  · have hz := forwardColumn_zero K S D Γ C γ G g j k.1 k.2 dk
      (sIntegerMaskGenerator K Sset δ) z₁ hc₁
    simp only [hc₁, false_and, if_false, hz, star_zero, zero_mul, ite_self, mul_zero]


end HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRetained

end

