import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPreparedBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LiveSourceConditions

/-!
# Literal normalization binding on the actual main pool leaves

The source cover, atom tables and both rectangles are computed from
original occurrences. The first divisor gate is recovered from the
same live leaf and its original coefficient. Both canonical second
chart fields and the common row translations are then proved inside
the constructor. No whole-column identity or replacement leaf is an
input. All slots, including the empty product, use the same argument.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
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
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) pool M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (retainedScale g : ℝ) (hscale : 0 < retainedScale)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)

section LiteralLeftMainBinding

variable (hnorm : ∀ h ∈ (p.divisorPools.leftData S).mainRows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool (p.divisorPools.leftData S).columns (p.divisorPools.leftData S).columns
  (fun i => ((p.divisorPools.leftData S).ideal i).val) (fun i => ((p.divisorPools.leftData S).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool (p.divisorPools.leftData S).columns (p.divisorPools.leftData S).columns
  (fun i => ((p.divisorPools.leftData S).ideal i).val) (fun i => ((p.divisorPools.leftData S).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.leftSourceCovers (raw).originalAtlas S χ).main
local notation "firstPoint" => (fun i => -Real.log (A.exteriorNorm (b.leftResidual i)))

variable (v : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey
  ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main) ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates
  ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main) ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "leftAtoms" => literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1
local notation "rightAtoms" => literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1

include hroot hemb in
private theorem literalLeftMain_leftAtoms_coefficient
    (hdiv : S.val ∣ v.1.val.1)
    (i : AllocationColumn K ((cover).branch v.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.1).reindex.index i ∈ v.block.leftColumns (p.divisorPools.leftData S).columns) :
    (leftAtoms).whole i =
      ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).coefficient (((cover).branch v.2.2.1).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.1).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          (((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.1).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  have hSi := v.block.left_divisor_of_common (p.divisorPools.leftData S).columns S.val hdiv _ hc
  rw [p.divisorPools.left_ideal S] at hSi
  exact literalLeftMainAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ v.2.2.1 i hi hSi

include hroot hemb in
private theorem literalLeftMain_rightAtoms_coefficient
    (hdiv : S.val ∣ v.1.val.2)
    (i : AllocationColumn K ((cover).branch v.2.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns (p.divisorPools.leftData S).columns) :
    (rightAtoms).whole i =
      ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).coefficient (((cover).branch v.2.2.2.1).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.2.1).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          (((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.2.1).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  have hSi := v.block.right_divisor_of_common (p.divisorPools.leftData S).columns S.val hdiv _ hc
  rw [p.divisorPools.left_ideal S] at hSi
  exact literalLeftMainAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ v.2.2.2.1 i hi hSi

private theorem literalLeftMain_live_common
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    S.val ∣ v.1.val.1 ∧ S.val ∣ v.1.val.2 := by
  have ha : v.1.val ∈ ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).activeCommon := by
    obtain ⟨q, hq, i, hi, hci⟩ := hlive.2.1
    exact (stage).supported_gated_leaf_active cover cover exceptional F firstPoint
      ⟨v, j⟩ q i hci
  exact ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).activeCommon_old_mask S.val hS
    (fun i _ hci => p.leftDivisorCoefficient_nonzero_dvd S χ i hci)
    v.1.val ha

/-- The actual main leaf, with its two original common scalar factors. -/
def literalLeftMainExtraction
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    (v.leaf exceptional F firstPoint j).ConstantAtomExtraction := by
  have hs := literalLeftMain_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  exact ActualGaussStage.preparedLiteralExtraction
    (v := v) (exceptional := exceptional) (F := F) (x := firstPoint) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (hcoeffL := literalLeftMain_leftAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1)
    (hcoeffR := literalLeftMain_rightAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.2) hlive

/-- The actual allocation was selected before the Fourier variables. -/
def literalLeftMainRectangles
    (hlive : (v.leaf exceptional F firstPoint j).Live) :=
  v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j 1 hlive

/-- The computed original first point has exactly the main source's
full ideal norm. No pointwise location identity is a new input. -/
private theorem literalLeftMain_firstPoint :
    ∀ i, firstPoint i = -(1 : ℝ) * Real.log
      (A.exteriorNorm (ExteriorIdealEuler.mul (unitExterior A) (((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).ideal i))) := by
  intro i
  change _ = -(1 : ℝ) * Real.log
    (Ideal.absNorm ((unitExterior A).val * ((p.divisorPools.leftData S).ideal i).val) : ℝ)
  rw [p.divisorPools.left_ideal S, p.left_ideal]
  change _ = -(1 : ℝ) * Real.log (Ideal.absNorm (1 * (b.leftResidual i).val) : ℝ)
  simp only [one_mul, neg_neg, neg_one_mul, one_mul]

/-- Same two Fourier kernels, same original leaf and exact two
rectangles; the generic adapter's two column proofs are discharged
from the original source here. -/
def literalLeftMainOrdinaryBinding
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    (literalLeftMainExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v exceptional F firstFixed hfirst j hS hlive).leaf.OrdinaryBinding
      (literalLeftMainRectangles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        hDiff δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
        dimension width hnorm character dyad v exceptional F firstFixed hfirst j hlive) := by
  have hs := literalLeftMain_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  exact ActualGaussStage.preparedLiteralOrdinaryBinding
    (v := v) (exceptional := exceptional) (F := F) (x := firstPoint) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (hcoeffL := literalLeftMain_leftAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1)
    (hcoeffR := literalLeftMain_rightAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.2)
    (power := unitExterior A) (firstSign := 1)
    (literalLeftMain_firstPoint (p := p) (S := S) (χ := χ)) hlive

end LiteralLeftMainBinding

section LiteralRightMainBinding

variable (hnorm : ∀ h ∈ (p.divisorPools.rightData S).mainRows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool (p.divisorPools.rightData S).columns (p.divisorPools.rightData S).columns
  (fun i => ((p.divisorPools.rightData S).ideal i).val) (fun i => ((p.divisorPools.rightData S).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool (p.divisorPools.rightData S).columns (p.divisorPools.rightData S).columns
  (fun i => ((p.divisorPools.rightData S).ideal i).val) (fun i => ((p.divisorPools.rightData S).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.rightSourceCovers (raw).originalAtlas S χ).main
local notation "firstPoint" => (fun i => Real.log (A.exteriorNorm (b.rightResidual i)))

variable (v : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey
  ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main) ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates
  ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main) ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "leftAtoms" => literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1
local notation "rightAtoms" => literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1

include hroot hemb in
private theorem literalRightMain_leftAtoms_coefficient
    (hdiv : S.val ∣ v.1.val.1)
    (i : AllocationColumn K ((cover).branch v.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.1).reindex.index i ∈ v.block.leftColumns (p.divisorPools.rightData S).columns) :
    (leftAtoms).whole i =
      ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).coefficient (((cover).branch v.2.2.1).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.1).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          (((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.1).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  have hSi := v.block.left_divisor_of_common (p.divisorPools.rightData S).columns S.val hdiv _ hc
  rw [p.divisorPools.right_ideal S] at hSi
  exact literalRightMainAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ v.2.2.1 i hi hSi

include hroot hemb in
private theorem literalRightMain_rightAtoms_coefficient
    (hdiv : S.val ∣ v.1.val.2)
    (i : AllocationColumn K ((cover).branch v.2.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns (p.divisorPools.rightData S).columns) :
    (rightAtoms).whole i =
      ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).coefficient (((cover).branch v.2.2.2.1).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.2.1).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          (((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.2.1).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  have hSi := v.block.right_divisor_of_common (p.divisorPools.rightData S).columns S.val hdiv _ hc
  rw [p.divisorPools.right_ideal S] at hSi
  exact literalRightMainAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ v.2.2.2.1 i hi hSi

private theorem literalRightMain_live_common
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    S.val ∣ v.1.val.1 ∧ S.val ∣ v.1.val.2 := by
  have ha : v.1.val ∈ ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).activeCommon := by
    obtain ⟨q, hq, i, hi, hci⟩ := hlive.2.1
    exact (stage).supported_gated_leaf_active cover cover exceptional F firstPoint
      ⟨v, j⟩ q i hci
  exact ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).activeCommon_old_mask S.val hS
    (fun i _ hci => p.rightDivisorCoefficient_nonzero_dvd S χ i hci)
    v.1.val ha

/-- The actual main leaf, with its two original common scalar factors. -/
def literalRightMainExtraction
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    (v.leaf exceptional F firstPoint j).ConstantAtomExtraction := by
  have hs := literalRightMain_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  exact ActualGaussStage.preparedLiteralExtraction
    (v := v) (exceptional := exceptional) (F := F) (x := firstPoint) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (hcoeffL := literalRightMain_leftAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1)
    (hcoeffR := literalRightMain_rightAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.2) hlive

/-- The actual allocation was selected before the Fourier variables. -/
def literalRightMainRectangles
    (hlive : (v.leaf exceptional F firstPoint j).Live) :=
  v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j (-1) hlive

/-- The computed original first point has exactly the main source's
full ideal norm. No pointwise location identity is a new input. -/
private theorem literalRightMain_firstPoint :
    ∀ i, firstPoint i = -((-1) : ℝ) * Real.log
      (A.exteriorNorm (ExteriorIdealEuler.mul (unitExterior A) (((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).ideal i))) := by
  intro i
  change _ = -((-1) : ℝ) * Real.log
    (Ideal.absNorm ((unitExterior A).val * ((p.divisorPools.rightData S).ideal i).val) : ℝ)
  rw [p.divisorPools.right_ideal S, p.right_ideal]
  change _ = -((-1) : ℝ) * Real.log (Ideal.absNorm (1 * (b.rightResidual i).val) : ℝ)
  simp only [one_mul, neg_neg, neg_one_mul, one_mul]

/-- Same two Fourier kernels, same original leaf and exact two
rectangles; the generic adapter's two column proofs are discharged
from the original source here. -/
def literalRightMainOrdinaryBinding
    (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live) :
    (literalRightMainExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v exceptional F firstFixed hfirst j hS hlive).leaf.OrdinaryBinding
      (literalRightMainRectangles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        hDiff δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
        dimension width hnorm character dyad v exceptional F firstFixed hfirst j hlive) := by
  have hs := literalRightMain_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  exact ActualGaussStage.preparedLiteralOrdinaryBinding
    (v := v) (exceptional := exceptional) (F := F) (x := firstPoint) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (hcoeffL := literalRightMain_leftAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.1)
    (hcoeffR := literalRightMain_rightAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width hnorm character dyad v firstFixed hfirst hs.2)
    (power := unitExterior A) (firstSign := (-1))
    (literalRightMain_firstPoint (p := p) (S := S) (χ := χ)) hlive

end LiteralRightMainBinding

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainOrdinaryBinding
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainOrdinaryBinding
