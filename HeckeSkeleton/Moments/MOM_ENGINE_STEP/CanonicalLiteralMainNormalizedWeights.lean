import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMainNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolOriginalWeightWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNominalWeightWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormalizedWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormalizedLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMainBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolComputedProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredComputedProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStripExistingBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralQuotientScales

/-!
# The two actual main normalizations have their original allowance bound

The proof functions below reproduce the exact literal constructor's
internal data and supply all its weight windows from the original
source constructors. Their four remaining analytic arguments are the
same original single-character certificates used by that constructor.
No occurrence bound, Gauss lower bound, capacity identity, normalized
child or completed family estimate is an input.

The only added ideal identity names the complete original first
extraction in the nominal coordinates. In a pool branch it contains
the full actual valuation power. Original fixed thresholds and error
windows are retained explicitly.
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

section LiteralLeftMainNormalization

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
local notation "cover" => (((p.leftSourceCovers (raw).originalAtlas S χ).main))
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

local notation "leftAtoms" => literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "rightAtoms" => literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "leftScalar" => literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "rightScalar" => literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
local notation "leftBalance" => literalLeftMainBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ v.2.2.1
local notation "rightBalance" => literalLeftMainBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ v.2.2.2.1
local notation "fixedPhases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
local notation "extra" => literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
local notation "source" => (p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)
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
variable (hactiveColumns : ∀ i ∈ ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).columns,
  ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).coefficient i ≠ 0 →
  A.exteriorNorm (((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).ideal i) ≤
    Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss))
variable (hold : A.exteriorNorm
  (((CanonicalLiteralActualCharacters.unamplifiedPhases firstFixed
    (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst)
    .moving P R Q.moving).effectiveFullSupport
      (Q.remaining * literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))) ≤
  Z ^ (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo))
variable (hexceptional : (v.leaf exceptional F firstPoint j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).literalCharacter C P R
    (CanonicalLiteralActualCharacters.unamplifiedPhases firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst)
    Q.moving Q.correction
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
    (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) h ∈ (data ξ).theta)

variable (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hfirstFrozen : geometry.literalFirstExtraction.val = DE.1)
variable (herrorPos : 0 < error)
variable (hannulusThreshold : OriginalPairAllowanceProduction.annulusThreshold hi error ≤ Z)
variable (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
variable (hsupportError : geometry.supportError ≤ error)
variable (hphysicalError : 2 * columnLoss + cutoffExponent ≤ error)
variable (firstNormalization : ℝ)
variable (hfirstNormalization : firstNormalization =
  firstLeftAllowance Z (geometry.skeleton.A +
    (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E))
    geometry.ideals.first.val geometry.ideals.opposite.val)

/-- The weight of the same normalization data, with all source atom
and Gauss windows supplied internally from the original profile. -/
def literalLeftMainNormalizationWeight :=
  let enhancedCharacter := fun E : commonSupportPool (source).columns (source).columns
      (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) =>
    (canonicalFirstCommonBlock C (source).columns (source).columns (source).ideal (source).ideal
      E.val E.property).sectorCharacter C P (character E)
  let originalExtraction := literalLeftMainExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let originalBinding := literalLeftMainOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcL : leftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero leftAtoms rightAtoms
    exceptional F firstPoint j 1 hlive originalExtraction originalBinding
    (literalLeftMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
    leftScalar (literalLeftMainAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  have hcR : rightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero leftAtoms rightAtoms
    exceptional F firstPoint j 1 hlive originalExtraction originalBinding
    (literalLeftMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
    rightScalar (literalLeftMainAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hbL : ∀ r, 0 < leftBalance r :=
    fun r => CanonicalLiteralBalancedSchwartz.balance_pos _ _ δ₁ δ₂ r
  have hbR : ∀ r, 0 < rightBalance r :=
    fun r => CanonicalLiteralBalancedSchwartz.balance_pos _ _ δ₁ δ₂ r
  let extraction := originalExtraction.trans
    (originalExtraction.leaf.stripColumnConstants leftScalar rightScalar hcL hcR)
  let binding := v.stripExistingOrdinaryBinding leftAtoms rightAtoms exceptional F firstPoint j
    1 hlive originalExtraction originalBinding leftScalar rightScalar hcL hcR
    leftBalance rightBalance hbL hbR
  have hwindow : Set.Icc lo hi ⊆ Set.Ioi 0 := fun _ hy => lt_of_lt_of_le hlo hy.1
  let EL := literalLeftMainProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ v.2.2.1
  let ER := literalLeftMainProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ v.2.2.2.1
  let TL := literalLeftMainComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ hδsum v.2.2.1
  let TR := literalLeftMainComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ hδsum v.2.2.2.1
  let profilesL := v.literalLeftProfileSupport leftAtoms EL rfl rfl (fun _ => rfl)
  let profilesR := v.literalRightProfileSupport rightAtoms ER rfl rfl (fun _ => rfl)
  let computedL := v.literalLeftComputedProfiles leftAtoms EL rfl rfl (fun _ => rfl)
    leftScalar leftBalance TL
  let computedR := v.literalRightComputedProfiles rightAtoms ER rfl rfl (fun _ => rfl)
    rightScalar rightBalance TR
  let recipeL := v.literalLeftRecipe leftAtoms
    (literalLeftMainRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  let recipeR := v.literalRightRecipe rightAtoms
    (literalLeftMainRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hbaseL : (v.literalLeftAtoms leftAtoms).base = Z := by
    simp only [ActualGaussStage.CoveredClassKey.literalLeftAtoms,
      ActualGaussStage.CoveredClassKey.literalLeftOriginal,
      literalLeftMainAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hbaseR : (v.literalRightAtoms rightAtoms).base = Z := by
    simp only [ActualGaussStage.CoveredClassKey.literalRightAtoms,
      ActualGaussStage.CoveredClassKey.literalRightOriginal,
      literalLeftMainAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hcorr : Q.correction ∈ (data ξ).theta := by
    rcases Q.correction_mem ξ with hc | hc
    · simpa only [hc] using hone
    · exact hc
  have hzero : (0, 0) ∈ CanonicalLogProfiles.sourceOrders
      (CanonicalLogProfiles.sourceOrders orders) :=
    CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _
        (hprimeOrders CanonicalFullKappaPrime.zero_mem_orders))
  let windowsL := literalLeftMainOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδsum v.2.2.1
    originalWindow hzero htime hprime hi hhi (fun _ hx => hx.2) cap hcap domain
  let windowsR := literalLeftMainOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδsum v.2.2.2.1
    originalWindow hzero htime hprime hi hhi (fun _ hx => hx.2) cap hcap domain
  have htotal : a.n₁ + a.n₂ + (data ξ).geometry.totalLength = a.n₁ + a.n₂ + a.z := by
    rw [domain.total_length]
  have hcenteredL : (leftAtoms).centered = centered := by
    simp only [literalLeftMainAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_centered_eq] <;> rfl
  have hcenteredR : (rightAtoms).centered = centered := by
    simp only [literalLeftMainAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_centered_eq] <;> rfl
  fun analyticLeft analyticRight hanalyticLeft hanalyticRight =>
  v.literalNormalizationData_allowance_from_original_atoms
    (P := P) (Rchar := R) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := source) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := zero_lt_one.trans hZ) (cutoff := cutoff₂) (hcutoff := hcutoff₂)
    (hnorm := hnorm) (dimension := dimension) (width := width) (character := character) (dyad := dyad)
    (LC := cover) (RC := cover) (exceptional := exceptional) (firstKernel := F) (x := firstPoint)
    (j := j) (hlive := hlive) (firstSign := 1)
    («leftAtoms» := leftAtoms) («rightAtoms» := rightAtoms)
    («leftScalar» := leftScalar) («rightScalar» := rightScalar)
    («leftBalance» := leftBalance) («rightBalance» := rightBalance)
    (hleftBalance := hbL) (hrightBalance := hbR)
    (firstSupport := primeSupport DE.1) (hfirst := fun _ hp => support_prime hp)
    (leftProfiles := profilesL) (rightProfiles := profilesR)
    (hbaseLeft := hbaseL) (hbaseRight := hbaseR)
    (F := fixedPhases) (parent := data ξ) (oldMoving := Q.moving)
    (correction := Q.correction) (hcorr := hcorr) (remaining := Q.remaining) («extra» := extra)
    (hextra := rfl) (leftRecipe := recipeL) (rightRecipe := recipeR)
    (profileBound := profileBound) (hprofileBound := hprofileBound) (hprofile := hprofile)
    (a := a) (step := step) (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit) (hnonunit := hnonunit)
    (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns) (hold := hold)
    (reference := reference) (time := t) (hone := hone) (hroot := hroot) (hemb := hemb)
    (hbackground := hbackground) (hslot := hslot) (hexceptional := hexceptional)
    (domain := domain) (direct := direct) (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    («original» := originalWindow) (hreference := hreference) (htime := htime)
    (horders := fun z hz => CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _ hz))
    (leftComputed := computedL) (rightComputed := computedR) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
    (X := extraction) (binding := binding)
    (analyticLeft := analyticLeft) (analyticRight := analyticRight)
    (hanalyticLeft := hanalyticLeft) (hanalyticRight := hanalyticRight)
    (cap := cap) (hcountL := windowsL.slots) (hcountR := windowsR.slots)
    (atomBound := CanonicalLiteralMassProfilePower.slotBudget originalBound)
    (hAtomBound := windowsL.atomBound_one)
    (hcostL := windowsL.prime_atoms) (hcostR := windowsR.prime_atoms)
    (hprimeL := windowsL.prime_norm) (hprimeR := windowsR.prime_norm)
    (hslotsL := fun _ => rfl) (hslotsR := fun _ => rfl)
    (hfirstL := windowsL.nominal_scale geometry hfirstFrozen htotal hcenteredL)
    (hfirstR := windowsR.nominal_scale geometry hfirstFrozen htotal hcenteredR)
    (hgaussL := windowsL.nominal_gauss geometry hfirstFrozen htotal)
    (hgaussR := windowsR.nominal_gauss geometry hfirstFrozen htotal)
    (herrorPos := herrorPos) (hannulusThreshold := hannulusThreshold)
    (hscaleThreshold := hscaleThreshold) (hsupportError := hsupportError)
    (hphysicalError := hphysicalError) (firstNormalization := firstNormalization)
    (hfirstNormalization := hfirstNormalization)

end LiteralLeftMainNormalization

section LiteralRightMainNormalization

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
local notation "cover" => (((p.rightSourceCovers (raw).originalAtlas S χ).main))
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

local notation "leftAtoms" => literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "rightAtoms" => literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "leftScalar" => literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "rightScalar" => literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
local notation "leftBalance" => literalRightMainBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ v.2.2.1
local notation "rightBalance" => literalRightMainBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ v.2.2.2.1
local notation "fixedPhases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
local notation "extra" => literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
local notation "source" => (p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)
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
variable (hactiveColumns : ∀ i ∈ ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).columns,
  ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).coefficient i ≠ 0 →
  A.exteriorNorm (((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).ideal i) ≤
    Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss))
variable (hold : A.exteriorNorm
  (((CanonicalLiteralActualCharacters.unamplifiedPhases firstFixed
    (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst)
    .moving P R Q.moving).effectiveFullSupport
      (Q.remaining * literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))) ≤
  Z ^ (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo))
variable (hexceptional : (v.leaf exceptional F firstPoint j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).literalCharacter C P R
    (CanonicalLiteralActualCharacters.unamplifiedPhases firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst)
    Q.moving Q.correction
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
    (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) h ∈ (data ξ).theta)

variable (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hfirstFrozen : geometry.literalFirstExtraction.val = DE.2)
variable (herrorPos : 0 < error)
variable (hannulusThreshold : OriginalPairAllowanceProduction.annulusThreshold hi error ≤ Z)
variable (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
variable (hsupportError : geometry.supportError ≤ error)
variable (hphysicalError : 2 * columnLoss + cutoffExponent ≤ error)
variable (firstNormalization : ℝ)
variable (hfirstNormalization : firstNormalization =
  firstLeftAllowance Z (geometry.skeleton.A +
    (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E))
    geometry.ideals.first.val geometry.ideals.opposite.val)

/-- The weight of the same normalization data, with all source atom
and Gauss windows supplied internally from the original profile. -/
def literalRightMainNormalizationWeight :=
  let enhancedCharacter := fun E : commonSupportPool (source).columns (source).columns
      (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) =>
    (canonicalFirstCommonBlock C (source).columns (source).columns (source).ideal (source).ideal
      E.val E.property).sectorCharacter C P (character E)
  let originalExtraction := literalRightMainExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let originalBinding := literalRightMainOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcL : leftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero leftAtoms rightAtoms
    exceptional F firstPoint j (-1) hlive originalExtraction originalBinding
    (literalRightMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
    leftScalar (literalRightMainAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  have hcR : rightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero leftAtoms rightAtoms
    exceptional F firstPoint j (-1) hlive originalExtraction originalBinding
    (literalRightMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
    rightScalar (literalRightMainAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hbL : ∀ r, 0 < leftBalance r :=
    fun r => CanonicalLiteralBalancedSchwartz.balance_pos _ _ δ₁ δ₂ r
  have hbR : ∀ r, 0 < rightBalance r :=
    fun r => CanonicalLiteralBalancedSchwartz.balance_pos _ _ δ₁ δ₂ r
  let extraction := originalExtraction.trans
    (originalExtraction.leaf.stripColumnConstants leftScalar rightScalar hcL hcR)
  let binding := v.stripExistingOrdinaryBinding leftAtoms rightAtoms exceptional F firstPoint j
    (-1) hlive originalExtraction originalBinding leftScalar rightScalar hcL hcR
    leftBalance rightBalance hbL hbR
  have hwindow : Set.Icc lo hi ⊆ Set.Ioi 0 := fun _ hy => lt_of_lt_of_le hlo hy.1
  let EL := literalRightMainProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ v.2.2.1
  let ER := literalRightMainProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ v.2.2.2.1
  let TL := literalRightMainComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ hδsum v.2.2.1
  let TR := literalRightMainComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ hδsum v.2.2.2.1
  let profilesL := v.literalLeftProfileSupport leftAtoms EL rfl rfl (fun _ => rfl)
  let profilesR := v.literalRightProfileSupport rightAtoms ER rfl rfl (fun _ => rfl)
  let computedL := v.literalLeftComputedProfiles leftAtoms EL rfl rfl (fun _ => rfl)
    leftScalar leftBalance TL
  let computedR := v.literalRightComputedProfiles rightAtoms ER rfl rfl (fun _ => rfl)
    rightScalar rightBalance TR
  let recipeL := v.literalLeftRecipe leftAtoms
    (literalRightMainRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  let recipeR := v.literalRightRecipe rightAtoms
    (literalRightMainRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hbaseL : (v.literalLeftAtoms leftAtoms).base = Z := by
    simp only [ActualGaussStage.CoveredClassKey.literalLeftAtoms,
      ActualGaussStage.CoveredClassKey.literalLeftOriginal,
      literalRightMainAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hbaseR : (v.literalRightAtoms rightAtoms).base = Z := by
    simp only [ActualGaussStage.CoveredClassKey.literalRightAtoms,
      ActualGaussStage.CoveredClassKey.literalRightOriginal,
      literalRightMainAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hcorr : Q.correction ∈ (data ξ).theta := by
    rcases Q.correction_mem ξ with hc | hc
    · simpa only [hc] using hone
    · exact hc
  have hzero : (0, 0) ∈ CanonicalLogProfiles.sourceOrders
      (CanonicalLogProfiles.sourceOrders orders) :=
    CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _
        (hprimeOrders CanonicalFullKappaPrime.zero_mem_orders))
  let windowsL := literalRightMainOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδsum v.2.2.1
    originalWindow hzero htime hprime hi hhi (fun _ hx => hx.2) cap hcap domain
  let windowsR := literalRightMainOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδsum v.2.2.2.1
    originalWindow hzero htime hprime hi hhi (fun _ hx => hx.2) cap hcap domain
  have htotal : a.n₁ + a.n₂ + (data ξ).geometry.totalLength = a.n₁ + a.n₂ + a.z := by
    rw [domain.total_length]
  have hcenteredL : (leftAtoms).centered = centered := by
    simp only [literalRightMainAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_centered_eq] <;> rfl
  have hcenteredR : (rightAtoms).centered = centered := by
    simp only [literalRightMainAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_centered_eq] <;> rfl
  fun analyticLeft analyticRight hanalyticLeft hanalyticRight =>
  v.literalNormalizationData_allowance_from_original_atoms
    (P := P) (Rchar := R) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := source) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := zero_lt_one.trans hZ) (cutoff := cutoff₂) (hcutoff := hcutoff₂)
    (hnorm := hnorm) (dimension := dimension) (width := width) (character := character) (dyad := dyad)
    (LC := cover) (RC := cover) (exceptional := exceptional) (firstKernel := F) (x := firstPoint)
    (j := j) (hlive := hlive) (firstSign := (-1))
    («leftAtoms» := leftAtoms) («rightAtoms» := rightAtoms)
    («leftScalar» := leftScalar) («rightScalar» := rightScalar)
    («leftBalance» := leftBalance) («rightBalance» := rightBalance)
    (hleftBalance := hbL) (hrightBalance := hbR)
    (firstSupport := primeSupport DE.1) (hfirst := fun _ hp => support_prime hp)
    (leftProfiles := profilesL) (rightProfiles := profilesR)
    (hbaseLeft := hbaseL) (hbaseRight := hbaseR)
    (F := fixedPhases) (parent := data ξ) (oldMoving := Q.moving)
    (correction := Q.correction) (hcorr := hcorr) (remaining := Q.remaining) («extra» := extra)
    (hextra := rfl) (leftRecipe := recipeL) (rightRecipe := recipeR)
    (profileBound := profileBound) (hprofileBound := hprofileBound) (hprofile := hprofile)
    (a := a) (step := step) (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit) (hnonunit := hnonunit)
    (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns) (hold := hold)
    (reference := reference) (time := t) (hone := hone) (hroot := hroot) (hemb := hemb)
    (hbackground := hbackground) (hslot := hslot) (hexceptional := hexceptional)
    (domain := domain) (direct := direct) (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    («original» := originalWindow) (hreference := hreference) (htime := htime)
    (horders := fun z hz => CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _ hz))
    (leftComputed := computedL) (rightComputed := computedR) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
    (X := extraction) (binding := binding)
    (analyticLeft := analyticLeft) (analyticRight := analyticRight)
    (hanalyticLeft := hanalyticLeft) (hanalyticRight := hanalyticRight)
    (cap := cap) (hcountL := windowsL.slots) (hcountR := windowsR.slots)
    (atomBound := CanonicalLiteralMassProfilePower.slotBudget originalBound)
    (hAtomBound := windowsL.atomBound_one)
    (hcostL := windowsL.prime_atoms) (hcostR := windowsR.prime_atoms)
    (hprimeL := windowsL.prime_norm) (hprimeR := windowsR.prime_norm)
    (hslotsL := fun _ => rfl) (hslotsR := fun _ => rfl)
    (hfirstL := windowsL.nominal_scale geometry hfirstFrozen htotal hcenteredL)
    (hfirstR := windowsR.nominal_scale geometry hfirstFrozen htotal hcenteredR)
    (hgaussL := windowsL.nominal_gauss geometry hfirstFrozen htotal)
    (hgaussR := windowsR.nominal_gauss geometry hfirstFrozen htotal)
    (herrorPos := herrorPos) (hannulusThreshold := hannulusThreshold)
    (hscaleThreshold := hscaleThreshold) (hsupportError := hsupportError)
    (hphysicalError := hphysicalError) (firstNormalization := firstNormalization)
    (hfirstNormalization := hfirstNormalization)

end LiteralRightMainNormalization

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep


#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainNormalizationWeight
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainNormalizationWeight
