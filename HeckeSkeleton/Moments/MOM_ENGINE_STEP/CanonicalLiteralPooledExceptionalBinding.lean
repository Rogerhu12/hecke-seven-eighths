import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPooledExceptionalSides
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalRelativeSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectExceptionalBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMainFactorFreeNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolFactorFreeNormalization

/-!
# The four actual pooled exceptional sources on their original leaves

The original main and valuation coefficient identities construct the
stored common extraction and its exact ordinary dictionary. Redistribution
moves the same positive norm factors into the original first scalar pair.
The actual live leaf proves both scalars nonzero. The stored theta-class
integrand is then identified with the exceptional sides constructed from
that same original parent, without supplying a source estimate.
-/

set_option autoImplicit false
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
section LeftMainExceptionalBinding

variable (hnorm : ∀ h ∈ (p.divisorPools.leftData S).mainRows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool (p.divisorPools.leftData S).columns (p.divisorPools.leftData S).columns
  (fun i => ((p.divisorPools.leftData S).ideal i).val) (fun i => ((p.divisorPools.leftData S).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool (p.divisorPools.leftData S).columns (p.divisorPools.leftData S).columns
  (fun i => ((p.divisorPools.leftData S).ideal i).val) (fun i => ((p.divisorPools.leftData S).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (((p.leftSourceCovers raw.originalAtlas S χ).main))
local notation "firstPoint" => (fun i => -Real.log (A.exteriorNorm (b.leftResidual i)))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main)) (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main)))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main)) (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main)))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "oldLeftScalar" => literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "oldRightScalar" => literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
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
local notation "source" => (p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live)

/-- The original coefficient identities and the actual live leaf
construct this common extraction, its dictionary and the two nonzero
first scalars. These are the objects used before the exceptional bound. -/
def literalLeftMainExceptionalExtraction :
    { extraction : (v.leaf exceptional F firstPoint j).ConstantAtomExtraction //
      extraction.leaf.OrdinaryBinding
        (v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j 1 hlive) ∧
        leftScalar ≠ 0 ∧ rightScalar ≠ 0 } :=
  let enhancedCharacter := fun E : commonSupportPool source.columns source.columns
      (fun i => (source.ideal i).val) (fun i => (source.ideal i).val) =>
    (canonicalFirstCommonBlock C source.columns source.columns source.ideal source.ideal
      E.val E.property).sectorCharacter C P (character E)
  let baseExtraction := literalLeftMainExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalLeftMainOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 hlive baseExtraction baseBinding
    (literalLeftMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
    oldLeftScalar (literalLeftMainAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 hlive baseExtraction baseBinding
    (literalLeftMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
    oldRightScalar (literalLeftMainAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hproductL : oldLeftAtoms.centered = true →
      oldLeftAtoms.scale₁ true * oldLeftAtoms.scale₂ true =
        oldLeftAtoms.scale₁ false * oldLeftAtoms.scale₂ false := by
    dsimp only [literalLeftMainAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : oldRightAtoms.centered = true →
      oldRightAtoms.scale₁ true * oldRightAtoms.scale₂ true =
        oldRightAtoms.scale₁ false * oldRightAtoms.scale₂ false := by
    dsimp only [literalLeftMainAtoms]
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
  ⟨originalExtraction, originalBinding, hcL, hcR⟩

local notation "construction" => literalLeftMainExceptionalExtraction
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (hroot := hroot) (hemb := hemb) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := retainedScale) (g := g) (hscale := hscale)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := dimension) (width := width)
    (domain := domain) (hnorm := hnorm) (character := character) (dyad := dyad)
    (v := v) (exceptional := exceptional) (F := F) (firstFixed := firstFixed)
    (hfirst := hfirst) (j := j) (hS := hS) (hlive := hlive)
local notation "sides" => literalLeftMainExceptionalSides
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (reference := reference) (href := href) (orders := orders)
    (amplitude := originalBound) (hamplitude := horiginalBound)
    (originalWindow := originalWindow) (hreference := hreference) (ht := htime)
    (hcompact := isCompact_Icc) (hpositive := fun _ hy => lt_of_lt_of_le hlo hy.1)
    (hprime := hprime) (v := v) (exceptional := exceptional) (kernel := F)
    (j := j) (hlive := hlive) (firstFixed := firstFixed) (hfirst := hfirst)

variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (thetaPair : theta × theta)
local notation "classRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).restrictRows (characters.thetaClass thetaPair)

/-- The original theta partition of the stored leaf is exactly the
pair of exceptional frames returned by the same original side factory.
The input equality specifies that original partition; no coefficient,
whole-polynomial identity or estimate is assumed. -/
theorem literalLeftMainExceptionalSource_eq
    (hpredicate : (v.leaf exceptional F firstPoint j).exceptional = characters.exceptional)
    (z : ℝ × ℝ) :
    (((construction.val.stripOuter leftScalar rightScalar
        construction.property.2.1 construction.property.2.2).
      thetaClassLeaf characters thetaPair).exceptionalIntegrand z) =
        (sides.1.val.frame classRows C .left).exceptionalMagnitude
          (sides.2.val.frame classRows C .right)
          (sides.1.val.comparison classRows C .left)
          (sides.2.val.comparison classRows C .right) characters (WithLp.toLp 2 z) := by
  have live : (v.leaf exceptional F firstPoint j).Live := hlive
  let allocation := v.literalAllocation exceptional F firstPoint j live
  have hb := v.literalStripOuter_theta_integrand leftAtoms rightAtoms exceptional F
    firstPoint j 1 live construction.val construction.property.1
    leftScalar rightScalar construction.property.2.1 construction.property.2.2
    (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    characters hpredicate thetaPair z
  have hp := CanonicalLiteralExceptionalOriginalSideFactory.Result.pair_magnitude_eq
    sides.1 sides.2 C classRows v.leftReindex.ideal_product v.rightReindex.ideal_product
    (Finset.mem_filter.mp allocation.property).2.2.1
    (Finset.mem_filter.mp allocation.property).2.2.2 characters (WithLp.toLp 2 z)
  exact hb.trans hp.symm

include hroot hemb domain hS hlive in
/-- A nonzero original allocated coefficient forces each actual
redistributed second common scalar to be nonzero, before the exceptional
partition or any completed source estimate is used. -/
theorem literalLeftMainExceptionalCommon_nonzero :
    (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch ≠ 0 ∧
      (v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch ≠ 0 := by
  have live : (v.leaf exceptional F firstPoint j).Live := hlive
  exact ⟨construction.val.leftScalar_ne_zero_of_live live,
    construction.val.rightScalar_ne_zero_of_live live⟩

end LeftMainExceptionalBinding

section RightMainExceptionalBinding

variable (hnorm : ∀ h ∈ (p.divisorPools.rightData S).mainRows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool (p.divisorPools.rightData S).columns (p.divisorPools.rightData S).columns
  (fun i => ((p.divisorPools.rightData S).ideal i).val) (fun i => ((p.divisorPools.rightData S).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool (p.divisorPools.rightData S).columns (p.divisorPools.rightData S).columns
  (fun i => ((p.divisorPools.rightData S).ideal i).val) (fun i => ((p.divisorPools.rightData S).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (((p.rightSourceCovers raw.originalAtlas S χ).main))
local notation "firstPoint" => (fun i => Real.log (A.exteriorNorm (b.rightResidual i)))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main)) (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main)))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main)) (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).main)))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "oldLeftScalar" => literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "oldRightScalar" => literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
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
local notation "source" => (p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live)

/-- The original coefficient identities and the actual live leaf
construct this common extraction, its dictionary and the two nonzero
first scalars. These are the objects used before the exceptional bound. -/
def literalRightMainExceptionalExtraction :
    { extraction : (v.leaf exceptional F firstPoint j).ConstantAtomExtraction //
      extraction.leaf.OrdinaryBinding
        (v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j (-1) hlive) ∧
        leftScalar ≠ 0 ∧ rightScalar ≠ 0 } :=
  let enhancedCharacter := fun E : commonSupportPool source.columns source.columns
      (fun i => (source.ideal i).val) (fun i => (source.ideal i).val) =>
    (canonicalFirstCommonBlock C source.columns source.columns source.ideal source.ideal
      E.val E.property).sectorCharacter C P (character E)
  let baseExtraction := literalRightMainExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalRightMainOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) hlive baseExtraction baseBinding
    (literalRightMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
    oldLeftScalar (literalRightMainAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) hlive baseExtraction baseBinding
    (literalRightMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
    oldRightScalar (literalRightMainAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hproductL : oldLeftAtoms.centered = true →
      oldLeftAtoms.scale₁ true * oldLeftAtoms.scale₂ true =
        oldLeftAtoms.scale₁ false * oldLeftAtoms.scale₂ false := by
    dsimp only [literalRightMainAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : oldRightAtoms.centered = true →
      oldRightAtoms.scale₁ true * oldRightAtoms.scale₂ true =
        oldRightAtoms.scale₁ false * oldRightAtoms.scale₂ false := by
    dsimp only [literalRightMainAtoms]
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
  ⟨originalExtraction, originalBinding, hcL, hcR⟩

local notation "construction" => literalRightMainExceptionalExtraction
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (hroot := hroot) (hemb := hemb) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := retainedScale) (g := g) (hscale := hscale)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := dimension) (width := width)
    (domain := domain) (hnorm := hnorm) (character := character) (dyad := dyad)
    (v := v) (exceptional := exceptional) (F := F) (firstFixed := firstFixed)
    (hfirst := hfirst) (j := j) (hS := hS) (hlive := hlive)
local notation "sides" => literalRightMainExceptionalSides
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (reference := reference) (href := href) (orders := orders)
    (amplitude := originalBound) (hamplitude := horiginalBound)
    (originalWindow := originalWindow) (hreference := hreference) (ht := htime)
    (hcompact := isCompact_Icc) (hpositive := fun _ hy => lt_of_lt_of_le hlo hy.1)
    (hprime := hprime) (v := v) (exceptional := exceptional) (kernel := F)
    (j := j) (hlive := hlive) (firstFixed := firstFixed) (hfirst := hfirst)

variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (thetaPair : theta × theta)
local notation "classRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).restrictRows (characters.thetaClass thetaPair)

/-- The original theta partition of the stored leaf is exactly the
pair of exceptional frames returned by the same original side factory.
The input equality specifies that original partition; no coefficient,
whole-polynomial identity or estimate is assumed. -/
theorem literalRightMainExceptionalSource_eq
    (hpredicate : (v.leaf exceptional F firstPoint j).exceptional = characters.exceptional)
    (z : ℝ × ℝ) :
    (((construction.val.stripOuter leftScalar rightScalar
        construction.property.2.1 construction.property.2.2).
      thetaClassLeaf characters thetaPair).exceptionalIntegrand z) =
        (sides.1.val.frame classRows C .left).exceptionalMagnitude
          (sides.2.val.frame classRows C .right)
          (sides.1.val.comparison classRows C .left)
          (sides.2.val.comparison classRows C .right) characters (WithLp.toLp 2 z) := by
  have live : (v.leaf exceptional F firstPoint j).Live := hlive
  let allocation := v.literalAllocation exceptional F firstPoint j live
  have hb := v.literalStripOuter_theta_integrand leftAtoms rightAtoms exceptional F
    firstPoint j (-1) live construction.val construction.property.1
    leftScalar rightScalar construction.property.2.1 construction.property.2.2
    (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    characters hpredicate thetaPair z
  have hp := CanonicalLiteralExceptionalOriginalSideFactory.Result.pair_magnitude_eq
    sides.1 sides.2 C classRows v.leftReindex.ideal_product v.rightReindex.ideal_product
    (Finset.mem_filter.mp allocation.property).2.2.1
    (Finset.mem_filter.mp allocation.property).2.2.2 characters (WithLp.toLp 2 z)
  simp only [show -(-(1 : ℝ)) = 1 from neg_neg (1 : ℝ)] at hb
  exact hb.trans hp.symm

include hroot hemb domain hS hlive in
/-- A nonzero original allocated coefficient forces each actual
redistributed second common scalar to be nonzero, before the exceptional
partition or any completed source estimate is used. -/
theorem literalRightMainExceptionalCommon_nonzero :
    (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch ≠ 0 ∧
      (v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch ≠ 0 := by
  have live : (v.leaf exceptional F firstPoint j).Live := hlive
  exact ⟨construction.val.leftScalar_ne_zero_of_live live,
    construction.val.rightScalar_ne_zero_of_live live⟩

end RightMainExceptionalBinding

variable (q : pool.primes) (n : ℕ)

section LeftPoolExceptionalBinding

variable (hnorm : ∀ h ∈ (p.divisorPools.leftData S).errorRows q.val,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (((p.leftSourceCovers raw.originalAtlas S χ).residual q n))
local notation "firstPoint" => (fun i : (p.divisorPools.leftData S).valuationColumns q.val n =>
  -Real.log (A.exteriorNorm (b.leftResidual i.val)))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)) (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)) (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ q n v.2.2.1
local notation "oldRightAtoms" => literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ q n v.2.2.2.1
local notation "oldLeftScalar" => literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n v.2.2.1
local notation "oldRightScalar" => literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n v.2.2.2.1
local notation "leftAtoms" => oldLeftAtoms.redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => oldRightAtoms.redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "fixedPhases" => CanonicalLiteralActualCharacters.amplifiedPhases C
  firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n
local notation "extra" => literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact support_prime hp
        · rcases Finset.mem_singleton.mp hp with rfl
          exact q.val.val.prime)
local notation "source" => (p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val)
variable (hlive : ((ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.fiberCoveredLeaf
  ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) exceptional F (fun i : (p.divisorPools.leftData S).valuationColumns q.val n =>
      -Real.log (A.exteriorNorm (b.leftResidual i.val))) ⟨v, j⟩).Live)

/-- The original coefficient identities and the actual live leaf
construct this common extraction, its dictionary and the two nonzero
first scalars. These are the objects used before the exceptional bound. -/
def literalLeftPoolExceptionalExtraction :
    { extraction : (v.leaf exceptional F firstPoint j).ConstantAtomExtraction //
      extraction.leaf.OrdinaryBinding
        (v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j 1 ((v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive)) ∧
        leftScalar ≠ 0 ∧ rightScalar ≠ 0 } :=
  let enhancedCharacter := fun E : commonSupportPool source.columns source.columns
      (fun i => (source.ideal i).val) (fun i => (source.ideal i).val) =>
    (canonicalFirstCommonBlock C source.columns source.columns source.ideal source.ideal
      E.val E.property).sectorCharacter C P (character E)
  have bareLive : (v.leaf exceptional F firstPoint j).Live :=
    (v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive
  let baseExtraction := literalLeftPoolExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width q n hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalLeftPoolOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width q n hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 bareLive baseExtraction baseBinding
    (literalLeftPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1)
    oldLeftScalar (literalLeftPoolAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 bareLive baseExtraction baseBinding
    (literalLeftPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1)
    oldRightScalar (literalLeftPoolAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1)
  have hproductL : oldLeftAtoms.centered = true →
      oldLeftAtoms.scale₁ true * oldLeftAtoms.scale₂ true =
        oldLeftAtoms.scale₁ false * oldLeftAtoms.scale₂ false := by
    dsimp only [literalLeftPoolAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : oldRightAtoms.centered = true →
      oldRightAtoms.scale₁ true * oldRightAtoms.scale₂ true =
        oldRightAtoms.scale₁ false * oldRightAtoms.scale₂ false := by
    dsimp only [literalLeftPoolAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  let originalExtraction := v.redistributedLiteralExtraction oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j 1 bareLive
    baseExtraction baseBinding rfl rfl
  let originalBinding := v.redistributedLiteralOrdinaryBinding oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j 1 bareLive
    baseExtraction baseBinding rfl rfl
  have hcL : leftScalar ≠ 0 := mul_ne_zero hcOldL
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (oldLeftAtoms.normProfileFactor_pos δ₁ δ₂)))
  have hcR : rightScalar ≠ 0 := mul_ne_zero hcOldR
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (oldRightAtoms.normProfileFactor_pos δ₁ δ₂)))
  ⟨originalExtraction, originalBinding, hcL, hcR⟩

local notation "construction" => literalLeftPoolExceptionalExtraction
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (hroot := hroot) (hemb := hemb) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := retainedScale) (g := g) (hscale := hscale)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := dimension) (width := width)
    (domain := domain) (hnorm := hnorm) (character := character) (dyad := dyad)
    (v := v) (exceptional := exceptional) (F := F) (firstFixed := firstFixed)
    (hfirst := hfirst) (j := j) (hS := hS) (hlive := hlive) (q := q) (n := n)
local notation "sides" => literalLeftPoolExceptionalSides
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (reference := reference) (href := href) (orders := orders)
    (amplitude := originalBound) (hamplitude := horiginalBound)
    (originalWindow := originalWindow) (hreference := hreference) (ht := htime)
    (hcompact := isCompact_Icc) (hpositive := fun _ hy => lt_of_lt_of_le hlo hy.1)
    (hprime := hprime) (v := v) (exceptional := exceptional) (kernel := F)
    (j := j) (hlive := hlive) (firstFixed := firstFixed) (hfirst := hfirst) (q := q) (n := n)

variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (thetaPair : theta × theta)
local notation "classRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).restrictRows (characters.thetaClass thetaPair)

/-- The original theta partition of the stored leaf is exactly the
pair of exceptional frames returned by the same original side factory.
The input equality specifies that original partition; no coefficient,
whole-polynomial identity or estimate is assumed. -/
theorem literalLeftPoolExceptionalSource_eq
    (hpredicate : (v.leaf exceptional F firstPoint j).exceptional = characters.exceptional)
    (z : ℝ × ℝ) :
    (((construction.val.stripOuter leftScalar rightScalar
        construction.property.2.1 construction.property.2.2).
      thetaClassLeaf characters thetaPair).exceptionalIntegrand z) =
        (sides.1.val.frame classRows C .left).exceptionalMagnitude
          (sides.2.val.frame classRows C .right)
          (sides.1.val.comparison classRows C .left)
          (sides.2.val.comparison classRows C .right) characters (WithLp.toLp 2 z) := by
  have live : (v.leaf exceptional F firstPoint j).Live := ((v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive)
  let allocation := v.literalAllocation exceptional F firstPoint j live
  have hb := v.literalStripOuter_theta_integrand leftAtoms rightAtoms exceptional F
    firstPoint j 1 live construction.val construction.property.1
    leftScalar rightScalar construction.property.2.1 construction.property.2.2
    (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    characters hpredicate thetaPair z
  have hp := CanonicalLiteralExceptionalOriginalSideFactory.Result.pair_magnitude_eq
    sides.1 sides.2 C classRows v.leftReindex.ideal_product v.rightReindex.ideal_product
    (Finset.mem_filter.mp allocation.property).2.2.1
    (Finset.mem_filter.mp allocation.property).2.2.2 characters (WithLp.toLp 2 z)
  exact hb.trans hp.symm

include hroot hemb domain hS hlive in
/-- A nonzero original allocated coefficient forces each actual
redistributed second common scalar to be nonzero, before the exceptional
partition or any completed source estimate is used. -/
theorem literalLeftPoolExceptionalCommon_nonzero :
    (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch ≠ 0 ∧
      (v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch ≠ 0 := by
  have live : (v.leaf exceptional F firstPoint j).Live := ((v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive)
  exact ⟨construction.val.leftScalar_ne_zero_of_live live,
    construction.val.rightScalar_ne_zero_of_live live⟩

end LeftPoolExceptionalBinding

section RightPoolExceptionalBinding

variable (hnorm : ∀ h ∈ (p.divisorPools.rightData S).errorRows q.val,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (((p.rightSourceCovers raw.originalAtlas S χ).residual q n))
local notation "firstPoint" => (fun i : (p.divisorPools.rightData S).valuationColumns q.val n =>
  Real.log (A.exteriorNorm (b.rightResidual i.val)))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)) (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)) (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ q n v.2.2.1
local notation "oldRightAtoms" => literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ q n v.2.2.2.1
local notation "oldLeftScalar" => literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n v.2.2.1
local notation "oldRightScalar" => literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n v.2.2.2.1
local notation "leftAtoms" => oldLeftAtoms.redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => oldRightAtoms.redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "fixedPhases" => CanonicalLiteralActualCharacters.amplifiedPhases C
  firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n
local notation "extra" => literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact support_prime hp
        · rcases Finset.mem_singleton.mp hp with rfl
          exact q.val.val.prime)
local notation "source" => (p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val)
variable (hlive : ((ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.fiberCoveredLeaf
  ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) exceptional F (fun i : (p.divisorPools.rightData S).valuationColumns q.val n =>
      Real.log (A.exteriorNorm (b.rightResidual i.val))) ⟨v, j⟩).Live)

/-- The original coefficient identities and the actual live leaf
construct this common extraction, its dictionary and the two nonzero
first scalars. These are the objects used before the exceptional bound. -/
def literalRightPoolExceptionalExtraction :
    { extraction : (v.leaf exceptional F firstPoint j).ConstantAtomExtraction //
      extraction.leaf.OrdinaryBinding
        (v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j (-1) ((v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive)) ∧
        leftScalar ≠ 0 ∧ rightScalar ≠ 0 } :=
  let enhancedCharacter := fun E : commonSupportPool source.columns source.columns
      (fun i => (source.ideal i).val) (fun i => (source.ideal i).val) =>
    (canonicalFirstCommonBlock C source.columns source.columns source.ideal source.ideal
      E.val E.property).sectorCharacter C P (character E)
  have bareLive : (v.leaf exceptional F firstPoint j).Live :=
    (v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive
  let baseExtraction := literalRightPoolExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width q n hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalRightPoolOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width q n hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) bareLive baseExtraction baseBinding
    (literalRightPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1)
    oldLeftScalar (literalRightPoolAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) bareLive baseExtraction baseBinding
    (literalRightPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1)
    oldRightScalar (literalRightPoolAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1)
  have hproductL : oldLeftAtoms.centered = true →
      oldLeftAtoms.scale₁ true * oldLeftAtoms.scale₂ true =
        oldLeftAtoms.scale₁ false * oldLeftAtoms.scale₂ false := by
    dsimp only [literalRightPoolAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : oldRightAtoms.centered = true →
      oldRightAtoms.scale₁ true * oldRightAtoms.scale₂ true =
        oldRightAtoms.scale₁ false * oldRightAtoms.scale₂ false := by
    dsimp only [literalRightPoolAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  let originalExtraction := v.redistributedLiteralExtraction oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j (-1) bareLive
    baseExtraction baseBinding rfl rfl
  let originalBinding := v.redistributedLiteralOrdinaryBinding oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j (-1) bareLive
    baseExtraction baseBinding rfl rfl
  have hcL : leftScalar ≠ 0 := mul_ne_zero hcOldL
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (oldLeftAtoms.normProfileFactor_pos δ₁ δ₂)))
  have hcR : rightScalar ≠ 0 := mul_ne_zero hcOldR
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (oldRightAtoms.normProfileFactor_pos δ₁ δ₂)))
  ⟨originalExtraction, originalBinding, hcL, hcR⟩

local notation "construction" => literalRightPoolExceptionalExtraction
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (hroot := hroot) (hemb := hemb) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := retainedScale) (g := g) (hscale := hscale)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := dimension) (width := width)
    (domain := domain) (hnorm := hnorm) (character := character) (dyad := dyad)
    (v := v) (exceptional := exceptional) (F := F) (firstFixed := firstFixed)
    (hfirst := hfirst) (j := j) (hS := hS) (hlive := hlive) (q := q) (n := n)
local notation "sides" => literalRightPoolExceptionalSides
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (reference := reference) (href := href) (orders := orders)
    (amplitude := originalBound) (hamplitude := horiginalBound)
    (originalWindow := originalWindow) (hreference := hreference) (ht := htime)
    (hcompact := isCompact_Icc) (hpositive := fun _ hy => lt_of_lt_of_le hlo hy.1)
    (hprime := hprime) (v := v) (exceptional := exceptional) (kernel := F)
    (j := j) (hlive := hlive) (firstFixed := firstFixed) (hfirst := hfirst) (q := q) (n := n)

variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (thetaPair : theta × theta)
local notation "classRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).restrictRows (characters.thetaClass thetaPair)

/-- The original theta partition of the stored leaf is exactly the
pair of exceptional frames returned by the same original side factory.
The input equality specifies that original partition; no coefficient,
whole-polynomial identity or estimate is assumed. -/
theorem literalRightPoolExceptionalSource_eq
    (hpredicate : (v.leaf exceptional F firstPoint j).exceptional = characters.exceptional)
    (z : ℝ × ℝ) :
    (((construction.val.stripOuter leftScalar rightScalar
        construction.property.2.1 construction.property.2.2).
      thetaClassLeaf characters thetaPair).exceptionalIntegrand z) =
        (sides.1.val.frame classRows C .left).exceptionalMagnitude
          (sides.2.val.frame classRows C .right)
          (sides.1.val.comparison classRows C .left)
          (sides.2.val.comparison classRows C .right) characters (WithLp.toLp 2 z) := by
  have live : (v.leaf exceptional F firstPoint j).Live := ((v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive)
  let allocation := v.literalAllocation exceptional F firstPoint j live
  have hb := v.literalStripOuter_theta_integrand leftAtoms rightAtoms exceptional F
    firstPoint j (-1) live construction.val construction.property.1
    leftScalar rightScalar construction.property.2.1 construction.property.2.2
    (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    characters hpredicate thetaPair z
  have hp := CanonicalLiteralExceptionalOriginalSideFactory.Result.pair_magnitude_eq
    sides.1 sides.2 C classRows v.leftReindex.ideal_product v.rightReindex.ideal_product
    (Finset.mem_filter.mp allocation.property).2.2.1
    (Finset.mem_filter.mp allocation.property).2.2.2 characters (WithLp.toLp 2 z)
  simp only [show -(-(1 : ℝ)) = 1 from neg_neg (1 : ℝ)] at hb
  exact hb.trans hp.symm

include hroot hemb domain hS hlive in
/-- A nonzero original allocated coefficient forces each actual
redistributed second common scalar to be nonzero, before the exceptional
partition or any completed source estimate is used. -/
theorem literalRightPoolExceptionalCommon_nonzero :
    (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch ≠ 0 ∧
      (v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch ≠ 0 := by
  have live : (v.leaf exceptional F firstPoint j).Live := ((v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive)
  exact ⟨construction.val.leftScalar_ne_zero_of_live live,
    construction.val.rightScalar_ne_zero_of_live live⟩

end RightPoolExceptionalBinding

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainExceptionalExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainExceptionalExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolExceptionalExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolExceptionalExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainExceptionalSource_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainExceptionalSource_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolExceptionalSource_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolExceptionalSource_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainExceptionalCommon_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainExceptionalCommon_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolExceptionalCommon_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolExceptionalCommon_nonzero
