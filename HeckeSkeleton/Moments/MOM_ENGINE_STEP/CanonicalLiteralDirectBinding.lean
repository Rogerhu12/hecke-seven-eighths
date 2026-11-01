import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPreparedChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSupportedLeaves

/-!
# Literal rectangles and ordinary binding of each actual direct leaf

This is an actual source specialization. Both atom tables are computed
from the parent's original atlas and original single-occurrence data.
The original first-divisor gate is removed only after the same live
leaf proves that its common label is active. Its first divisor is the
original squarefree outer label. Both actual first-coordinate signs
are retained and the second chart's common row translations are
proved internally. The stored leaf, finite allocation, kernels and
outer weight remain the original ones.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "original" => (Q.arithmeticAtoms ξ).constantAtoms W a Z t
local notation "raw" => (original).raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => ((original).values Y₁ Y₂).coefficient centered

variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockDirectData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (retainedScale g : ℝ) (hscale : 0 < retainedScale)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)

section LiteralLeftDirectBinding

variable (hnorm : ∀ h ∈ p.leftData.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool p.leftData.columns p.leftData.columns
  (fun i => (p.leftData.ideal i).val) (fun i => (p.leftData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool p.leftData.columns p.leftData.columns
  (fun i => (p.leftData.ideal i).val) (fun i => (p.leftData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.leftSourceCover (raw).originalAtlas S χ)
local notation "firstPoint" => (fun i => -Real.log (A.exteriorNorm (b.leftResidual i)))

variable (v : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "leftAtoms" => literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1
local notation "rightAtoms" => literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1

include hroot hemb in
private theorem literalLeftDirect_leftCoefficient
    (hactive : v.1.val ∈ (p.leftData.directSource (p.leftDivisorCoefficient S χ)).activeCommon)
    (hdiv : S.val ∣ v.1.val.1)
    (i : AllocationColumn K ((cover).branch v.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.1).reindex.index i ∈ v.block.leftColumns p.leftData.columns) :
    v.chart.sourceLeftCoefficient (((cover).branch v.2.2.1).reindex.index i) =
      (leftAtoms).whole i := by
  have hSi := v.block.left_divisor_of_common p.leftData.columns S.val hdiv _ hc
  have he := literalLeftDirectAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ v.2.2.1 i hi hSi
  have hc₀ := ActualGaussStage.canonicalUnmasked_prepared_leftCoefficient
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
    cutoff₂ hcutoff₂ hnorm dimension width character dyad
    v.1 v.2.1 hactive _ hc
  apply hc₀.trans
  simpa only [DirectGaussData.directSource, p.left_ideal] using he.symm

include hroot hemb in
private theorem literalLeftDirect_rightCoefficient
    (hactive : v.1.val ∈ (p.leftData.directSource (p.leftDivisorCoefficient S χ)).activeCommon)
    (hdiv : S.val ∣ v.1.val.2)
    (i : AllocationColumn K ((cover).branch v.2.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns p.leftData.columns) :
    v.chart.sourceRightCoefficient (((cover).branch v.2.2.2.1).reindex.index i) =
      (rightAtoms).whole i := by
  have hSi := v.block.right_divisor_of_common p.leftData.columns S.val hdiv _ hc
  have he := literalLeftDirectAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ v.2.2.2.1 i hi hSi
  have hc₀ := ActualGaussStage.canonicalUnmasked_prepared_rightCoefficient
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
    cutoff₂ hcutoff₂ hnorm dimension width character dyad
    v.1 v.2.1 hactive _ hc
  apply hc₀.trans
  simpa only [DirectGaussData.directSource, p.left_ideal] using he.symm

/-- The genuine source support supplies the first-divisor inclusion
from the same live leaf, before any ordinary-row restriction or N. -/
private theorem literalLeftDirect_live_common
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    v.1.val ∈ (p.leftData.directSource (p.leftDivisorCoefficient S χ)).activeCommon ∧ S.val ∣ v.1.val.1 ∧ S.val ∣ v.1.val.2 := by
  have ha : v.1.val ∈ (p.leftData.directSource (p.leftDivisorCoefficient S χ)).activeCommon := by
    obtain ⟨q, hq, i, hi, hci⟩ := hlive.2.1
    exact (stage).supported_gated_leaf_active cover cover exceptional F firstPoint
      ⟨v, j⟩ q i hci
  refine ⟨ha, ?_⟩
  exact (p.leftData.directSource (p.leftDivisorCoefficient S χ)).activeCommon_old_mask S.val hS
    (fun i _ hci => FirstBlockDirectData.leftDivisorCoefficient_nonzero_dvd S χ i hci)
    v.1.val ha

/-- Actual full common extraction of this original direct leaf.
The first divisor's squarefreeness is inherited from its outer weight. -/
def literalLeftDirectExtraction
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    (v.leaf exceptional F firstPoint j).ConstantAtomExtraction := by
  have hs := literalLeftDirect_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  exact v.literalExtraction leftAtoms rightAtoms exceptional F firstPoint j
    (literalLeftDirect_leftCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1 hs.2.1)
    (literalLeftDirect_rightCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1 hs.2.2)

/-- The two rectangles use the actual allocated carrier of this leaf,
its computed atom tables and its original correlation-supported rows. -/
def literalLeftDirectRectangles
    (hlive : (v.leaf exceptional F firstPoint j).Live) :=
  v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j 1 hlive

/-- Complete ordinary binding for this original direct leaf. The two
kernels, original outer weight and every retained occurrence are kept. -/
def literalLeftDirectOrdinaryBinding
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    (literalLeftDirectExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v exceptional F firstFixed hfirst j
      hS hlive).leaf.OrdinaryBinding
      (literalLeftDirectRectangles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        hDiff δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂ dimension width
        hnorm character dyad v exceptional F firstFixed hfirst j hlive) := by
  have hs := literalLeftDirect_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  apply v.literalOrdinaryBinding leftAtoms rightAtoms exceptional F firstPoint j
    (literalLeftDirect_leftCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1 hs.2.1)
    (literalLeftDirect_rightCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1 hs.2.2)
    1 hlive
  · intro q _
    have hx : firstPoint = fun i => -(1 : ℝ) * Real.log
        (A.exteriorNorm (ExteriorIdealEuler.mul (unitExterior A) ((p.leftData.directSource (p.leftDivisorCoefficient S χ)).ideal i))) := by
      funext i
      change _ = -(1 : ℝ) * Real.log (Ideal.absNorm
        ((unitExterior A).val * (p.leftData.ideal i).val) : ℝ)
      rw [p.left_ideal]
      change _ = -(1 : ℝ) * Real.log (Ideal.absNorm (1 * (b.leftResidual i).val) : ℝ)
      simp only [one_mul, neg_neg, neg_one_mul]
    rw [hx]
    exact ActualGaussStage.canonicalUnmasked_prepared_leaf_leftPoint
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
      cutoff₂ hcutoff₂ hnorm dimension width character dyad cover cover v exceptional F
      (unitExterior A) 1 j q
  · intro q _
    have hx : firstPoint = fun i => -(1 : ℝ) * Real.log
        (A.exteriorNorm (ExteriorIdealEuler.mul (unitExterior A) ((p.leftData.directSource (p.leftDivisorCoefficient S χ)).ideal i))) := by
      funext i
      change _ = -(1 : ℝ) * Real.log (Ideal.absNorm
        ((unitExterior A).val * (p.leftData.ideal i).val) : ℝ)
      rw [p.left_ideal]
      change _ = -(1 : ℝ) * Real.log (Ideal.absNorm (1 * (b.leftResidual i).val) : ℝ)
      simp only [one_mul, neg_neg, neg_one_mul]
    rw [hx]
    exact ActualGaussStage.canonicalUnmasked_prepared_leaf_rightPoint
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
      cutoff₂ hcutoff₂ hnorm dimension width character dyad cover cover v exceptional F
      (unitExterior A) 1 j q

end LiteralLeftDirectBinding

section LiteralRightDirectBinding

variable (hnorm : ∀ h ∈ p.rightData.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool p.rightData.columns p.rightData.columns
  (fun i => (p.rightData.ideal i).val) (fun i => (p.rightData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool p.rightData.columns p.rightData.columns
  (fun i => (p.rightData.ideal i).val) (fun i => (p.rightData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.rightSourceCover (raw).originalAtlas S χ)
local notation "firstPoint" => (fun i => -(-Real.log (A.exteriorNorm (b.rightResidual i))))

variable (v : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "leftAtoms" => literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1
local notation "rightAtoms" => literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1

include hroot hemb in
private theorem literalRightDirect_leftCoefficient
    (hactive : v.1.val ∈ (p.rightData.directSource (p.rightDivisorCoefficient S χ)).activeCommon)
    (hdiv : S.val ∣ v.1.val.1)
    (i : AllocationColumn K ((cover).branch v.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.1).reindex.index i ∈ v.block.leftColumns p.rightData.columns) :
    v.chart.sourceLeftCoefficient (((cover).branch v.2.2.1).reindex.index i) =
      (leftAtoms).whole i := by
  have hSi := v.block.left_divisor_of_common p.rightData.columns S.val hdiv _ hc
  have he := literalRightDirectAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ v.2.2.1 i hi hSi
  have hc₀ := ActualGaussStage.canonicalUnmasked_prepared_leftCoefficient
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
    cutoff₂ hcutoff₂ hnorm dimension width character dyad
    v.1 v.2.1 hactive _ hc
  apply hc₀.trans
  simpa only [DirectGaussData.directSource, p.right_ideal] using he.symm

include hroot hemb in
private theorem literalRightDirect_rightCoefficient
    (hactive : v.1.val ∈ (p.rightData.directSource (p.rightDivisorCoefficient S χ)).activeCommon)
    (hdiv : S.val ∣ v.1.val.2)
    (i : AllocationColumn K ((cover).branch v.2.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns p.rightData.columns) :
    v.chart.sourceRightCoefficient (((cover).branch v.2.2.2.1).reindex.index i) =
      (rightAtoms).whole i := by
  have hSi := v.block.right_divisor_of_common p.rightData.columns S.val hdiv _ hc
  have he := literalRightDirectAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ v.2.2.2.1 i hi hSi
  have hc₀ := ActualGaussStage.canonicalUnmasked_prepared_rightCoefficient
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
    cutoff₂ hcutoff₂ hnorm dimension width character dyad
    v.1 v.2.1 hactive _ hc
  apply hc₀.trans
  simpa only [DirectGaussData.directSource, p.right_ideal] using he.symm

/-- The genuine source support supplies the first-divisor inclusion
from the same live leaf, before any ordinary-row restriction or N. -/
private theorem literalRightDirect_live_common
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    v.1.val ∈ (p.rightData.directSource (p.rightDivisorCoefficient S χ)).activeCommon ∧ S.val ∣ v.1.val.1 ∧ S.val ∣ v.1.val.2 := by
  have ha : v.1.val ∈ (p.rightData.directSource (p.rightDivisorCoefficient S χ)).activeCommon := by
    obtain ⟨q, hq, i, hi, hci⟩ := hlive.2.1
    exact (stage).supported_gated_leaf_active cover cover exceptional F firstPoint
      ⟨v, j⟩ q i hci
  refine ⟨ha, ?_⟩
  exact (p.rightData.directSource (p.rightDivisorCoefficient S χ)).activeCommon_old_mask S.val hS
    (fun i _ hci => FirstBlockDirectData.rightDivisorCoefficient_nonzero_dvd S χ i hci)
    v.1.val ha

/-- Actual full common extraction of this original direct leaf.
The first divisor's squarefreeness is inherited from its outer weight. -/
def literalRightDirectExtraction
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    (v.leaf exceptional F firstPoint j).ConstantAtomExtraction := by
  have hs := literalRightDirect_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  exact v.literalExtraction leftAtoms rightAtoms exceptional F firstPoint j
    (literalRightDirect_leftCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1 hs.2.1)
    (literalRightDirect_rightCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1 hs.2.2)

/-- The two rectangles use the actual allocated carrier of this leaf,
its computed atom tables and its original correlation-supported rows. -/
def literalRightDirectRectangles
    (hlive : (v.leaf exceptional F firstPoint j).Live) :=
  v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j (-1) hlive

/-- Complete ordinary binding for this original direct leaf. The two
kernels, original outer weight and every retained occurrence are kept. -/
def literalRightDirectOrdinaryBinding
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    (literalRightDirectExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v exceptional F firstFixed hfirst j
      hS hlive).leaf.OrdinaryBinding
      (literalRightDirectRectangles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        hDiff δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂ dimension width
        hnorm character dyad v exceptional F firstFixed hfirst j hlive) := by
  have hs := literalRightDirect_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  apply v.literalOrdinaryBinding leftAtoms rightAtoms exceptional F firstPoint j
    (literalRightDirect_leftCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1 hs.2.1)
    (literalRightDirect_rightCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1 hs.2.2)
    (-1) hlive
  · intro q _
    have hx : firstPoint = fun i => -((-1) : ℝ) * Real.log
        (A.exteriorNorm (ExteriorIdealEuler.mul (unitExterior A) ((p.rightData.directSource (p.rightDivisorCoefficient S χ)).ideal i))) := by
      funext i
      change _ = -((-1) : ℝ) * Real.log (Ideal.absNorm
        ((unitExterior A).val * (p.rightData.ideal i).val) : ℝ)
      rw [p.right_ideal]
      change _ = -((-1) : ℝ) * Real.log (Ideal.absNorm (1 * (b.rightResidual i).val) : ℝ)
      simp only [one_mul, neg_neg, neg_one_mul]
    rw [hx]
    exact ActualGaussStage.canonicalUnmasked_prepared_leaf_leftPoint
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
      cutoff₂ hcutoff₂ hnorm dimension width character dyad cover cover v exceptional F
      (unitExterior A) (-1) j q
  · intro q _
    have hx : firstPoint = fun i => -((-1) : ℝ) * Real.log
        (A.exteriorNorm (ExteriorIdealEuler.mul (unitExterior A) ((p.rightData.directSource (p.rightDivisorCoefficient S χ)).ideal i))) := by
      funext i
      change _ = -((-1) : ℝ) * Real.log (Ideal.absNorm
        ((unitExterior A).val * (p.rightData.ideal i).val) : ℝ)
      rw [p.right_ideal]
      change _ = -((-1) : ℝ) * Real.log (Ideal.absNorm (1 * (b.rightResidual i).val) : ℝ)
      simp only [one_mul, neg_neg, neg_one_mul]
    rw [hx]
    exact ActualGaussStage.canonicalUnmasked_prepared_leaf_rightPoint
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
      cutoff₂ hcutoff₂ hnorm dimension width character dyad cover cover v exceptional F
      (unitExterior A) (-1) j q

end LiteralRightDirectBinding

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectOrdinaryBinding
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectOrdinaryBinding
