import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSourceBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormalizedLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectComputedProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredComputedProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStripExistingBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralQuotientScales

import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectFactorFreeComputed
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRedistributedBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralComparisonProduct

/-!
# The original direct sources enter their passive family

Both source constructors are exactly those used by the corresponding
passive normalization family. The original scalar extraction and
single-coefficient ordinary binding are constructed internally.
The returned inequality keeps the original leaf cost, both Fourier
kernels, and the old frozen allocation cost once in the outer weight.
No completed source or child inequality is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open MeasureTheory HeckePort.IdealMobiusDivisorSum

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
local notation "raw" => original.raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => (original.values Y₁ Y₂).coefficient centered

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


variable (hδsum : δ₁ + δ₂ ≤ 1 / 2)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain : Set ℝ}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
variable (orders : Finset (ℕ × ℕ)) (originalBound : ℝ) (horiginalBound : 0 ≤ originalBound)
variable (originalWindow : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi)
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) originalBound)
variable (hreference : reference ∈ rowDomain) (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (originalWindow.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (step error mesh : ℝ) (hstep : 0 < step) (herror : 0 ≤ error) (hmesh : 0 ≤ mesh)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)

section LiteralLeftDirectPassiveSourceBound

variable (hnorm : ∀ h ∈ p.leftData.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool p.leftData.columns p.leftData.columns
  (fun i => (p.leftData.ideal i).val) (fun i => (p.leftData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool p.leftData.columns p.leftData.columns
  (fun i => (p.leftData.ideal i).val) (fun i => (p.leftData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.leftSourceCover raw.originalAtlas S χ)
local notation "firstPoint" => (fun i => -Real.log (A.exteriorNorm (b.leftResidual i)))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "oldLeftScalar" => literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "oldRightScalar" => literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
local notation "leftAtoms" => oldLeftAtoms.redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => oldRightAtoms.redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "fixedPhases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
local notation "extra" => literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
local notation "source" => p.leftData.directSource (p.leftDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live)
variable (profileBound : ℝ) (hprofileBound : 0 ≤ profileBound)
variable (hprofile : ∀ h ∈ (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).rows,
  ‖v.chart.weight h‖ ≤ profileBound)
variable (geometry : OriginalNominalGeometry (K := K) a Z step)
variable (hretained : geometry.retainedScale = retainedScale)
variable (henlargement : geometry.enlargement = g)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct v.block.primes v.block.leftMultiplicity).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct v.block.primes v.block.rightMultiplicity).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)).val)
variable (hnonunit : geometry.ideals.nonunitPart.val =
  (secondPatternNonunitIdeal v.block.primes
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)).val)
variable (direct : geometry.tag = .direct → (data ξ).geometry.slotCount = 0)
variable (columnLoss cutoffExponent : ℝ)
variable (hcolumnLoss : 0 ≤ columnLoss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (hsmall : 2 * (2 * columnLoss + cutoffExponent) ≤ step)
variable (hcutoffPower : cutoff₂ ≤ Z ^ cutoffExponent)
variable (hactiveColumns : ∀ i ∈ (p.leftData.directSource (p.leftDivisorCoefficient S χ)).columns,
  (p.leftData.directSource (p.leftDivisorCoefficient S χ)).coefficient i ≠ 0 →
  A.exteriorNorm ((p.leftData.directSource (p.leftDivisorCoefficient S χ)).ideal i) ≤
    Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss))
variable (oldSupport : A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) ≤ Z ^ a.q)
variable (firstIdeal : geometry.ideals.first.val = DE.1)
variable (oppositeIdeal : geometry.ideals.opposite.val = DE.2)
variable (physicalDivisor : geometry.ideals.complementary.val =
  (firstPhysicalDivisorIdeal (A := A) D).val)
variable (branchTag : geometry.tag = .direct)
variable (hexceptional : (v.leaf exceptional F firstPoint j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).literalCharacter C P R
    (CanonicalLiteralActualCharacters.unamplifiedPhases firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst)
    Q.moving Q.correction
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
    (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) h ∈ (data ξ).theta)

/-- The original left direct source reaches the actual passive source integrals
under the original Fourier measure. Applying the returned function supplies only the individual
analytic certificates for the computed original characters. -/
def literalLeftDirectPassiveSourceBound :=
  let enhancedCharacter := fun E : commonSupportPool source.columns source.columns
      (fun i => (source.ideal i).val) (fun i => (source.ideal i).val) =>
    (canonicalFirstCommonBlock C source.columns source.columns source.ideal source.ideal
      E.val E.property).sectorCharacter C P (character E)
  let baseExtraction := literalLeftDirectExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalLeftDirectOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 hlive baseExtraction baseBinding
    (literalLeftDirectCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
    oldLeftScalar (literalLeftDirectAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 hlive baseExtraction baseBinding
    (literalLeftDirectCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
    oldRightScalar (literalLeftDirectAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hproductL : oldLeftAtoms.centered = true →
      oldLeftAtoms.scale₁ true * oldLeftAtoms.scale₂ true =
        oldLeftAtoms.scale₁ false * oldLeftAtoms.scale₂ false := by
    dsimp only [literalLeftDirectAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : oldRightAtoms.centered = true →
      oldRightAtoms.scale₁ true * oldRightAtoms.scale₂ true =
        oldRightAtoms.scale₁ false * oldRightAtoms.scale₂ false := by
    dsimp only [literalLeftDirectAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  let originalExtraction := v.redistributedLiteralExtraction oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j 1 hlive
    baseExtraction baseBinding rfl rfl
  let originalBinding := v.redistributedLiteralOrdinaryBinding oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j 1 hlive
    baseExtraction baseBinding rfl rfl
  have hcL : leftScalar ≠ 0 := mul_ne_zero hcOldL
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (oldLeftAtoms.normProfileFactor_pos δ₁ δ₂)))
  have hcR : rightScalar ≠ 0 := mul_ne_zero hcOldR
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (oldRightAtoms.normProfileFactor_pos δ₁ δ₂)))
  have hbL : ∀ r, 0 < leftBalance r :=
    fun _ => zero_lt_one
  have hbR : ∀ r, 0 < rightBalance r :=
    fun _ => zero_lt_one
  let extraction := originalExtraction.trans
    (originalExtraction.leaf.stripColumnConstants leftScalar rightScalar hcL hcR)
  let binding := v.stripExistingOrdinaryBinding leftAtoms rightAtoms exceptional F firstPoint j
    1 hlive originalExtraction originalBinding leftScalar rightScalar hcL hcR
    leftBalance rightBalance hbL hbR
  have hwindow : Set.Icc lo hi ⊆ Set.Ioi 0 := fun _ hy => lt_of_lt_of_le hlo hy.1
  let EL := (literalLeftDirectProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ v.2.2.1).redistributeNormFactors δ₁ δ₂
  let ER := (literalLeftDirectProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ v.2.2.2.1).redistributeNormFactors δ₁ δ₂
  let TL := literalLeftDirectFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ v.2.2.1
  let TR := literalLeftDirectFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ v.2.2.2.1
  let profilesL := v.literalLeftProfileSupport leftAtoms EL rfl rfl (fun _ => rfl)
  let profilesR := v.literalRightProfileSupport rightAtoms ER rfl rfl (fun _ => rfl)
  let computedL := v.literalLeftComputedProfiles leftAtoms EL rfl rfl (fun _ => rfl)
    leftScalar leftBalance TL
  let computedR := v.literalRightComputedProfiles rightAtoms ER rfl rfl (fun _ => rfl)
    rightScalar rightBalance TR
  let recipeL := v.literalLeftRecipe leftAtoms
    ((literalLeftDirectRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1).redistributeNormFactors δ₁ δ₂)
  let recipeR := v.literalRightRecipe rightAtoms
    ((literalLeftDirectRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1).redistributeNormFactors δ₁ δ₂)
  have hbaseL : (v.literalLeftAtoms leftAtoms).base = Z := by
    change (v.literalLeftAtoms oldLeftAtoms).base = Z
    simp only [ActualGaussStage.CoveredClassKey.literalLeftAtoms,
      ActualGaussStage.CoveredClassKey.literalLeftOriginal,
      literalLeftDirectAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hbaseR : (v.literalRightAtoms rightAtoms).base = Z := by
    change (v.literalRightAtoms oldRightAtoms).base = Z
    simp only [ActualGaussStage.CoveredClassKey.literalRightAtoms,
      ActualGaussStage.CoveredClassKey.literalRightOriginal,
      literalLeftDirectAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hcorr : Q.correction ∈ (data ξ).theta := by
    rcases Q.correction_mem ξ with hc | hc
    · simpa only [hc] using hone
    · exact hc
  have hactive : geometry.skeleton.R = idealLogLength Z (firstActiveRadical DE.1 DE.2) := by
    change idealLogLength Z (firstActiveRadical geometry.ideals.first.val
      geometry.ideals.opposite.val) = _
    rw [firstIdeal, oppositeIdeal]
  have hphysical : geometry.skeleton.E =
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val := by
    change idealLogLength Z geometry.ideals.complementary.val = _
    rw [physicalDivisor]
  let choice : CanonicalLiteralPassiveSource.PhaseChoice fixedPhases C := .unamplified
  have hmoving : geometry.skeleton.wo = 0 := by
    change geometry.tag.movingLength Z = _
    rw [branchTag]
    rfl
  have hpaidSupport : A.exteriorNorm
      ((choice.phases.moving P R Q.moving).effectiveFullSupport Q.remaining) ≤
        Z ^ (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo) := by
    change A.exteriorNorm ((fixedPhases.moving P R Q.moving).effectiveFullSupport Q.remaining) ≤
      Z ^ (a.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo)
    rw [hactive, hphysical, hmoving, add_zero]
    exact CanonicalLiteralPaidSupport.unamplified_left P R C b D
      Q.moving Q.remaining firstFixed hfirst Z a.q hZ oldSupport
  v.literalPassiveNormalizedFamily_ordinaryCost_le_sourcePairs
    (P := P) (Rchar := R) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := source) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := zero_lt_one.trans hZ) (cutoff := cutoff₂) (hcutoff := hcutoff₂)
    (hnorm := hnorm) (dimension := dimension) (width := width) (character := character) (dyad := dyad)
    (LC := cover) (RC := cover) (exceptional := exceptional) (firstKernel := F) (x := firstPoint)
    (j := j) (hlive := hlive) (firstSign := 1)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hbL) (hrightBalance := hbR)
    (firstSupport := primeSupport DE.1) (hfirst := fun _ hp => support_prime hp)
    (leftProfiles := profilesL) (rightProfiles := profilesR)
    (hbaseLeft := hbaseL) (hbaseRight := hbaseR)
    (F := fixedPhases) (choice := choice) (parent := data ξ) (oldMoving := Q.moving)
    (correction := Q.correction) (hcorr := hcorr) (remaining := Q.remaining) (extra := extra) (hextra := rfl)
    (leftRecipe := recipeL) (rightRecipe := recipeR)
    (profileBound := profileBound) (hprofileBound := hprofileBound) (hprofile := hprofile)
    (a := a) (step := step) (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit) (hnonunit := hnonunit)
    (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport)
    (reference := reference) (time := t) (hone := hone) (hroot := hroot) (hemb := hemb)
    (hbackground := hbackground) (hslot := hslot) (hexceptional := hexceptional)
    (domain := domain) (direct := direct) (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := originalWindow) (hreference := hreference) (htime := htime)
    (horders := fun z hz => CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _ hz))
    (leftComputed := computedL) (rightComputed := computedR) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
    (X := extraction) (binding := binding)

end LiteralLeftDirectPassiveSourceBound

section LiteralRightDirectPassiveSourceBound

variable (hnorm : ∀ h ∈ p.rightData.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool p.rightData.columns p.rightData.columns
  (fun i => (p.rightData.ideal i).val) (fun i => (p.rightData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool p.rightData.columns p.rightData.columns
  (fun i => (p.rightData.ideal i).val) (fun i => (p.rightData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.rightSourceCover raw.originalAtlas S χ)
local notation "firstPoint" => (fun i => -(-Real.log (A.exteriorNorm (b.rightResidual i))))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "oldLeftScalar" => literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "oldRightScalar" => literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
local notation "leftAtoms" => oldLeftAtoms.redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => oldRightAtoms.redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "fixedPhases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
local notation "extra" => literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
local notation "source" => p.rightData.directSource (p.rightDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live)
variable (profileBound : ℝ) (hprofileBound : 0 ≤ profileBound)
variable (hprofile : ∀ h ∈ (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).rows,
  ‖v.chart.weight h‖ ≤ profileBound)
variable (geometry : OriginalNominalGeometry (K := K) a Z step)
variable (hretained : geometry.retainedScale = retainedScale)
variable (henlargement : geometry.enlargement = g)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct v.block.primes v.block.leftMultiplicity).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct v.block.primes v.block.rightMultiplicity).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)).val)
variable (hnonunit : geometry.ideals.nonunitPart.val =
  (secondPatternNonunitIdeal v.block.primes
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)).val)
variable (direct : geometry.tag = .direct → (data ξ).geometry.slotCount = 0)
variable (columnLoss cutoffExponent : ℝ)
variable (hcolumnLoss : 0 ≤ columnLoss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (hsmall : 2 * (2 * columnLoss + cutoffExponent) ≤ step)
variable (hcutoffPower : cutoff₂ ≤ Z ^ cutoffExponent)
variable (hactiveColumns : ∀ i ∈ (p.rightData.directSource (p.rightDivisorCoefficient S χ)).columns,
  (p.rightData.directSource (p.rightDivisorCoefficient S χ)).coefficient i ≠ 0 →
  A.exteriorNorm ((p.rightData.directSource (p.rightDivisorCoefficient S χ)).ideal i) ≤
    Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss))
variable (oldSupport : A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) ≤ Z ^ a.q)
variable (firstIdeal : geometry.ideals.first.val = DE.2)
variable (oppositeIdeal : geometry.ideals.opposite.val = DE.1)
variable (physicalDivisor : geometry.ideals.complementary.val =
  (firstPhysicalDivisorIdeal (A := A) D).val)
variable (branchTag : geometry.tag = .direct)
variable (hexceptional : (v.leaf exceptional F firstPoint j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).literalCharacter C P R
    (CanonicalLiteralActualCharacters.unamplifiedPhases firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst)
    Q.moving Q.correction
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
    (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) h ∈ (data ξ).theta)

/-- The original right direct source reaches the actual passive source integrals
under the original Fourier measure. Applying the returned function supplies only the individual
analytic certificates for the computed original characters. -/
def literalRightDirectPassiveSourceBound :=
  let enhancedCharacter := fun E : commonSupportPool source.columns source.columns
      (fun i => (source.ideal i).val) (fun i => (source.ideal i).val) =>
    (canonicalFirstCommonBlock C source.columns source.columns source.ideal source.ideal
      E.val E.property).sectorCharacter C P (character E)
  let baseExtraction := literalRightDirectExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalRightDirectOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) hlive baseExtraction baseBinding
    (literalRightDirectCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
    oldLeftScalar (literalRightDirectAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) hlive baseExtraction baseBinding
    (literalRightDirectCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
    oldRightScalar (literalRightDirectAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hproductL : oldLeftAtoms.centered = true →
      oldLeftAtoms.scale₁ true * oldLeftAtoms.scale₂ true =
        oldLeftAtoms.scale₁ false * oldLeftAtoms.scale₂ false := by
    dsimp only [literalRightDirectAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : oldRightAtoms.centered = true →
      oldRightAtoms.scale₁ true * oldRightAtoms.scale₂ true =
        oldRightAtoms.scale₁ false * oldRightAtoms.scale₂ false := by
    dsimp only [literalRightDirectAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  let originalExtraction := v.redistributedLiteralExtraction oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j (-1) hlive
    baseExtraction baseBinding rfl rfl
  let originalBinding := v.redistributedLiteralOrdinaryBinding oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j (-1) hlive
    baseExtraction baseBinding rfl rfl
  have hcL : leftScalar ≠ 0 := mul_ne_zero hcOldL
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (oldLeftAtoms.normProfileFactor_pos δ₁ δ₂)))
  have hcR : rightScalar ≠ 0 := mul_ne_zero hcOldR
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (oldRightAtoms.normProfileFactor_pos δ₁ δ₂)))
  have hbL : ∀ r, 0 < leftBalance r :=
    fun _ => zero_lt_one
  have hbR : ∀ r, 0 < rightBalance r :=
    fun _ => zero_lt_one
  let extraction := originalExtraction.trans
    (originalExtraction.leaf.stripColumnConstants leftScalar rightScalar hcL hcR)
  let binding := v.stripExistingOrdinaryBinding leftAtoms rightAtoms exceptional F firstPoint j
    (-1) hlive originalExtraction originalBinding leftScalar rightScalar hcL hcR
    leftBalance rightBalance hbL hbR
  have hwindow : Set.Icc lo hi ⊆ Set.Ioi 0 := fun _ hy => lt_of_lt_of_le hlo hy.1
  let EL := (literalRightDirectProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ v.2.2.1).redistributeNormFactors δ₁ δ₂
  let ER := (literalRightDirectProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ v.2.2.2.1).redistributeNormFactors δ₁ δ₂
  let TL := literalRightDirectFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ v.2.2.1
  let TR := literalRightDirectFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ v.2.2.2.1
  let profilesL := v.literalLeftProfileSupport leftAtoms EL rfl rfl (fun _ => rfl)
  let profilesR := v.literalRightProfileSupport rightAtoms ER rfl rfl (fun _ => rfl)
  let computedL := v.literalLeftComputedProfiles leftAtoms EL rfl rfl (fun _ => rfl)
    leftScalar leftBalance TL
  let computedR := v.literalRightComputedProfiles rightAtoms ER rfl rfl (fun _ => rfl)
    rightScalar rightBalance TR
  let recipeL := v.literalLeftRecipe leftAtoms
    ((literalRightDirectRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1).redistributeNormFactors δ₁ δ₂)
  let recipeR := v.literalRightRecipe rightAtoms
    ((literalRightDirectRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1).redistributeNormFactors δ₁ δ₂)
  have hbaseL : (v.literalLeftAtoms leftAtoms).base = Z := by
    change (v.literalLeftAtoms oldLeftAtoms).base = Z
    simp only [ActualGaussStage.CoveredClassKey.literalLeftAtoms,
      ActualGaussStage.CoveredClassKey.literalLeftOriginal,
      literalRightDirectAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hbaseR : (v.literalRightAtoms rightAtoms).base = Z := by
    change (v.literalRightAtoms oldRightAtoms).base = Z
    simp only [ActualGaussStage.CoveredClassKey.literalRightAtoms,
      ActualGaussStage.CoveredClassKey.literalRightOriginal,
      literalRightDirectAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hcorr : Q.correction ∈ (data ξ).theta := by
    rcases Q.correction_mem ξ with hc | hc
    · simpa only [hc] using hone
    · exact hc
  have hactive : geometry.skeleton.R = idealLogLength Z (firstActiveRadical DE.1 DE.2) := by
    change idealLogLength Z (firstActiveRadical geometry.ideals.first.val
      geometry.ideals.opposite.val) = _
    rw [firstIdeal, oppositeIdeal,
      firstActiveRadical_swap_of_support DE.1 DE.2 b.common_support_eq]
  have hphysical : geometry.skeleton.E =
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val := by
    change idealLogLength Z geometry.ideals.complementary.val = _
    rw [physicalDivisor]
  let choice : CanonicalLiteralPassiveSource.PhaseChoice fixedPhases C := .unamplified
  have hmoving : geometry.skeleton.wo = 0 := by
    change geometry.tag.movingLength Z = _
    rw [branchTag]
    rfl
  have hpaidSupport : A.exteriorNorm
      ((choice.phases.moving P R Q.moving).effectiveFullSupport Q.remaining) ≤
        Z ^ (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo) := by
    change A.exteriorNorm ((fixedPhases.moving P R Q.moving).effectiveFullSupport Q.remaining) ≤
      Z ^ (a.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo)
    rw [hactive, hphysical, hmoving, add_zero]
    exact CanonicalLiteralPaidSupport.unamplified_right P R C b D
      Q.moving Q.remaining firstFixed hfirst Z a.q hZ oldSupport
  v.literalPassiveNormalizedFamily_ordinaryCost_le_sourcePairs
    (P := P) (Rchar := R) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := source) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := zero_lt_one.trans hZ) (cutoff := cutoff₂) (hcutoff := hcutoff₂)
    (hnorm := hnorm) (dimension := dimension) (width := width) (character := character) (dyad := dyad)
    (LC := cover) (RC := cover) (exceptional := exceptional) (firstKernel := F) (x := firstPoint)
    (j := j) (hlive := hlive) (firstSign := (-1))
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hbL) (hrightBalance := hbR)
    (firstSupport := primeSupport DE.1) (hfirst := fun _ hp => support_prime hp)
    (leftProfiles := profilesL) (rightProfiles := profilesR)
    (hbaseLeft := hbaseL) (hbaseRight := hbaseR)
    (F := fixedPhases) (choice := choice) (parent := data ξ) (oldMoving := Q.moving)
    (correction := Q.correction) (hcorr := hcorr) (remaining := Q.remaining) (extra := extra) (hextra := rfl)
    (leftRecipe := recipeL) (rightRecipe := recipeR)
    (profileBound := profileBound) (hprofileBound := hprofileBound) (hprofile := hprofile)
    (a := a) (step := step) (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit) (hnonunit := hnonunit)
    (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport)
    (reference := reference) (time := t) (hone := hone) (hroot := hroot) (hemb := hemb)
    (hbackground := hbackground) (hslot := hslot) (hexceptional := hexceptional)
    (domain := domain) (direct := direct) (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := originalWindow) (hreference := hreference) (htime := htime)
    (horders := fun z hz => CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _ hz))
    (leftComputed := computedL) (rightComputed := computedR) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
    (X := extraction) (binding := binding)

end LiteralRightDirectPassiveSourceBound

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectPassiveSourceBound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectPassiveSourceBound
