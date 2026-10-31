import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceMasks
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonNormalization
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonSplit

/-!
# The complete actual second retained source in fixed-common slices

The real Poisson prefactor, all actual divisor generators, the common
bare frequency cutoff and every original sector are kept. Each fresh
pair is reindexed by its computed common factor before extending the
mutual residual condition. The second conductor square roots enter an
actual Schwartz power test, with their exact scale factor outside.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRetained

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CanonicalFirstEnergy
  CanonicalBlock FirstInversePoisson FirstDualTruncation PrimitivePoissonSource
  SecondSourceColumns SecondMarkedSource SecondSourceAssembly SecondSourceMasks
  SecondCanonicalEnergy ActualDivisorSectors ActualInverseFactors
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "e" => unitIdeal K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def residualScale (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (hX : 0 < C.base ^ C.columnLength γ) (g : Ext) : {r : ℝ // 0 < r} :=
  ⟨C.base ^ C.columnLength γ / height K Sset g, div_pos hX (height_pos K Sset g)⟩

def poweredFamily (C : ColumnFamily K Sset σ Θ ψ) : ColumnFamily K Sset σ Θ ψ :=
  { C with cutoff := fun γ => WideMellinTests.powerTest (C.cutoff γ) (-(1 / 2 : ℝ)) }

def forwardColumn (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (G : HeckeCharacter K) (g j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements OS) (z : Ext) : ℂ :=
  slicedColumn K S Γ D (poweredFamily K S C) γ G g j I ξ dk d₂ z

theorem forwardColumn_zero (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (G : HeckeCharacter K) (g j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements OS) (z : Ext) (hc : ¬IsCoprime g.val.val z.val.val) :
    forwardColumn K S D Γ C γ G g j I ξ dk d₂ z = 0 :=
  slicedColumn_zero K S Γ D (poweredFamily K S C) γ G g j I ξ dk d₂ z hc

def sourceProfile (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (hX : 0 < C.base ^ C.columnLength γ)
    (φ : SchwartzMap V ℂ) (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (δ : Finset (HeightOneSpectrum OS)) (k g : Ext) : Profile K S :=
  SecondPoissonNormalization.profile K S μv ν φ h hlc hcs r
    (sIntegerMaskGenerator K Sset δ) k (residualScale K S C γ hX g) (residualScale K S C γ hX g)

def sourceScalar (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (hX : 0 < C.base ^ C.columnLength γ) (r : {r : ℝ // 0 < r})
    (δ : Finset (HeightOneSpectrum OS)) (g j : Ext) (dk : NonzeroRingElements OS) : ℂ :=
  ((SecondPoissonNormalization.outerFactor K S r (sIntegerMaskGenerator K Sset δ) /
    (residualScale K S C γ hX g).val : ℝ) : ℂ) * sliceScalar K S C γ g j dk

variable (hallowed : AllowedGeneratorInput K Sset D)

include hΓ hallowed in
theorem weighted_pairTerm_eq (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K (C.background γ) p)
    (hX : 0 < C.base ^ C.columnLength γ)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2))
    (x₁ x₂ j : Ext) (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val)
    (dk : NonzeroRingElements OS) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (δ : Finset (HeightOneSpectrum OS)) (k : Ext × Sector) :
    (star (DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val x₁) *
      DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val x₂) *
      FirstParentRetained.pairTerm K S D Γ hΓ μv x₁ x₂ e e φ h hlc hcs ∅ r δ k =
      sourceScalar K S C γ hX r δ (common K Sset x₁ x₂) j dk *
        star (forwardColumn K S D Γ C γ G (common K Sset x₁ x₂) j k.1 k.2 dk
          (sIntegerMaskGenerator K Sset δ) (ActualInverseFactors.residual K Sset x₁ x₂)) *
        forwardColumn K S D Γ C γ G (common K Sset x₁ x₂) j k.1 k.2 dk
          (sIntegerMaskGenerator K Sset δ) (ActualInverseFactors.residual K Sset x₂ x₁) *
        (sourceProfile K S μv ν C γ hX φ h hlc hcs r δ k.1 (common K Sset x₁ x₂)).value K S
          (ActualInverseFactors.residual K Sset x₁ x₂).val
          (ActualInverseFactors.residual K Sset x₂ x₁).val := by
  let g := common K Sset x₁ x₂
  let z₁ := ActualInverseFactors.residual K Sset x₁ x₂
  let z₂ := ActualInverseFactors.residual K Sset x₂ x₁
  let X := residualScale K S C γ hX g
  let d₂ := sIntegerMaskGenerator K Sset δ
  let A := fun z => slicedColumn K S Γ D C γ G g j k.1 k.2 dk d₂ z
  let B := fun z => forwardColumn K S D Γ C γ G g j k.1 k.2 dk d₂ z
  let α : ℝ := X.val ^ (-(1 / 2 : ℝ))
  have hw (z : Ext) : normWeight K z.val * A z = (α : ℂ) * B z :=
    SecondNormWeights.sourceTerm_normWeight K S D Γ C.lambda (C.background γ * G⁻¹)
      g j (divisorIdeal K S d₂) (newRowIdeal K S k.1 dk d₂)
      (newSector K S Γ D dk d₂ k.2) (childPuncture C.originalPuncture γ)
      (C.survivors γ) C.primeLists C.primeWeights (C.cutoff γ) hW X.val X.property z
  have hn (z : Ext) : star (normWeight K z.val) = normWeight K z.val := by
    simp [normWeight]
  have hα : star (α : ℂ) = (α : ℂ) := Complex.conj_ofReal α
  have hαsq : (α : ℂ) ^ 2 = ((X.val⁻¹ : ℝ) : ℂ) := by
    have hr : α ^ 2 = X.val⁻¹ := by
      dsimp only [α]
      rw [Real.rpow_neg X.property.le, inv_pow, ← Real.sqrt_eq_rpow,
        Real.sq_sqrt X.property.le]
    exact_mod_cast hr
  have hpair : star (A z₁) * A z₂ * normWeight K z₁.val * normWeight K z₂.val =
      ((X.val⁻¹ : ℝ) : ℂ) * star (B z₁) * B z₂ := by
    calc
      _ = star (normWeight K z₁.val * A z₁) * (normWeight K z₂.val * A z₂) := by
        rw [star_mul, hn]
        ring
      _ = ((α : ℂ) ^ 2) * star (B z₁) * B z₂ := by
        rw [hw, hw, star_mul, hα]
        ring
      _ = _ := by rw [hαsq]
  rw [SecondPoissonNormalization.actual_pairTerm_eq K S D Γ hΓ μv ν x₁ x₂
    φ h hlc hcs r δ k X X]
  have hm := actual_marked_second_pair K S Γ D hΓ hallowed C γ hcal hbg
    x₁ x₂ j k.1 hx₁ hx₂ k.2 dk d₂
  change _ = sliceScalar K S C γ g j dk * star (A z₁) * A z₂ at hm
  calc
    _ = (SecondPoissonNormalization.outerFactor K S r d₂ : ℂ) *
        (star (DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val x₁) *
          DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val x₂ *
          normalizedDivisorFourier K S D x₁ x₂ d₂.val
            (CanonicalSectors.rowElement K Sset Γ D k).val) *
        normWeight K z₁.val * normWeight K z₂.val *
        (sourceProfile K S μv ν C γ hX φ h hlc hcs r δ k.1 g).value K S z₁.val z₂.val := by
      ring
    _ = (SecondPoissonNormalization.outerFactor K S r d₂ : ℂ) * sliceScalar K S C γ g j dk *
        (star (A z₁) * A z₂ * normWeight K z₁.val * normWeight K z₂.val) *
        (sourceProfile K S μv ν C γ hX φ h hlc hcs r δ k.1 g).value K S z₁.val z₂.val := by
      rw [hm]
      ring
    _ = _ := by
      rw [hpair]
      simp only [sourceScalar, Complex.ofReal_div, div_eq_mul_inv]
      dsimp only [B, X, g, z₁, z₂, d₂]
      ring

theorem retained_pair_eq (a : Ext → ℂ) (x₁ x₂ : Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : ℝ) :
    (star (a x₁) * a x₂) * retainedDual K S D Γ μv
        (primitivePairBlock K S D Γ hΓ (e, x₁) (e, x₂) φ h hlc hcs ∅ r) H =
      ∑ δ ∈ (FirstSourcePartition.actualMask K S D ∅ x₁ x₂ e e).powerset,
        ∑ k ∈ sectorCutoff K S D Γ H,
          (moebius (IdealMobiusMask.primeProduct δ) : ℂ) * (star (a x₁) * a x₂) *
            FirstParentRetained.pairTerm K S D Γ hΓ μv x₁ x₂ e e φ h hlc hcs ∅ r δ k := by
  unfold retainedDual
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [primitiveRetained_eq_sectors K S D Γ μv]
  simp only [Finset.mul_sum, ActualMaskedPoissonBlock.divisorCoefficient,
    FirstParentRetained.pairTerm]
  apply Finset.sum_congr rfl
  intro k hk
  ring

include hΓ hallowed in
/-- Every actual nonzero-frequency term is present. The only remaining
pair condition in each independent residual pool is mutual coprimality.
The original common ideal is fixed in its whole outer slice. -/
theorem retainedSource_eq_fixed_common
    (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K (C.background γ) p)
    (hX : 0 < C.base ^ C.columnLength γ)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2))
    (j : Ext) (dk : NonzeroRingElements OS) (N : ℝ) (hN : 0 ≤ N)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : ℝ) :
    SecondPoissonSplit.retainedSource K S D Γ hΓ μv
      (DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val)
      (squarefreePool K Sset N ×ˢ squarefreePool K Sset N) φ h hlc hcs r H =
      ∑ g ∈ squarefreePool K Sset N, ∑ δ ∈ (commonMask K S D g).powerset,
        ∑ k ∈ sectorCutoff K S D Γ H,
          (moebius (IdealMobiusMask.primeProduct δ) : ℂ) *
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
  unfold SecondPoissonSplit.retainedSource SecondPoissonSplit.sourceWeight
    SecondPoissonSplit.pairBlock
  rw [Finset.sum_product]
  simp_rw [retained_pair_eq K S D Γ hΓ μv]
  rw [sum_masks_frequencies_by_common K S D N hN]
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
          _ = (moebius (IdealMobiusMask.primeProduct δ) : ℂ) *
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

theorem sourceScalar_norm_le (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (hX : 0 < C.base ^ C.columnLength γ) (r : {r : ℝ // 0 < r})
    (δ : Finset (HeightOneSpectrum OS)) (g j : Ext) (dk : NonzeroRingElements OS) :
    ‖sourceScalar K S C γ hX r δ g j dk‖ ≤
      SecondPoissonNormalization.outerFactor K S r (sIntegerMaskGenerator K Sset δ) /
        (residualScale K S C γ hX g).val := by
  have hA : 0 ≤ SecondPoissonNormalization.outerFactor K S r
      (sIntegerMaskGenerator K Sset δ) / (residualScale K S C γ hX g).val :=
    div_nonneg (SecondPoissonNormalization.outerFactor_nonneg K S r _)
      (residualScale K S C γ hX g).property.le
  have hmask : ‖sliceScalar K S C γ g j dk‖ ≤ 1 := by
    unfold sliceScalar SecondSourceCharacters.commonZero
    rw [norm_mul, norm_mul]
    calc
      _ ≤ 1 * 1 * 1 := by
        gcongr
        all_goals exact norm_idealCoprimeMask_le_one _ _
      _ = 1 := by norm_num
  rw [sourceScalar, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA]
  exact (mul_le_mul_of_nonneg_left hmask hA).trans_eq (mul_one _)

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRetained

end
