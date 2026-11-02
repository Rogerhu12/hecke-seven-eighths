import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralAnalyticProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralCoveredStrip
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceGates
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyBase

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# The original covered row class produces all passive normalized sides

The original row label, two literal tables, common-row atoms and scalar
extraction are retained. Only the uncharged deletion mask is expanded
into the actual independent passive allocations before normalization.
The paid support window is used for every one of these allocations.

The original profile representatives and slot recipes construct both
side normalizations. The finite pair family then contains all nonzero
passive labels and both original rectangles, before its activity test.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]



variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

local instance canonicalLiteralPassiveCoveredCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))
variable (LC RC : SourceCartesianCover G.columns G.ideal)
variable (v : (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.gated (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.supported (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad)))) LC RC)
variable (exceptional : (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.gated (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.supported (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad))).CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.AllocationKey v))
variable (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).Live) (firstSign : ℝ)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (leftScalar rightScalar : ℂ)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)
variable (leftProfiles : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).ProfileData)
variable (rightProfiles : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).ProfileData)
variable (hbaseLeft : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).base = Z)
variable (hbaseRight : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).base = Z)
variable {ω ψ : HeckeCharacter K}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (choice : CanonicalLiteralPassiveSource.PhaseChoice F C)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (leftSlots : OriginalSlotDictionary parent ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).length)
variable (hleftCharacters : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).characters =
  CanonicalLiteralPhaseCalibration.sourceCharacters P Rchar F parent oldMoving
    correction remaining extra leftSlots.index)
variable (rightSlots : OriginalSlotDictionary parent ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).length)
variable (hrightCharacters : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).characters =
  CanonicalLiteralPhaseCalibration.sourceCharacters P Rchar F parent oldMoving
    correction remaining extra rightSlots.index)
variable (profileBound : ℝ) (hprofileBound : 0 ≤ profileBound)
variable (hprofile : ∀ h ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).rows,
  ‖(HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).weight h‖ ≤ profileBound)
variable (a : RealParameters) (step : ℝ)
variable (geometry : OriginalNominalGeometry (K := K) a Z step)
variable (hretained : geometry.retainedScale = retainedScale)
variable (henlargement : geometry.enlargement = g)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v))).val)
variable (hnonunit : geometry.ideals.nonunitPart.val =
  (secondPatternNonunitIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v))).val)
variable (columnLoss cutoffExponent : ℝ)
variable (hcolumnLoss : 0 ≤ columnLoss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)
variable (hactiveColumns : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
  A.exteriorNorm (G.ideal i) ≤
    Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss))
variable (hpaidSupport : A.exteriorNorm ((choice.phases.moving P Rchar oldMoving).effectiveFullSupport
  remaining) ≤
    Z ^ (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo))
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
  ¬ FiniteOrder parent.plainBackground)
variable (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
variable (hexceptional : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).exceptional = fun h =>
  (HeckeSkeleton.Moments.EngineStepV2.ActualSecondCorrelationRows.literalCharacter ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v))) C P Rchar F oldMoving
    correction ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v))
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalSector (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) P ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)) h ∈ parent.theta)

local notation "rootLength" => idealLogLength Z
  (secondSixthRootIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity).val
local notation "paidCutoff" => 2 * columnLoss + cutoffExponent
local notation "m" => (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.literalRowParameter geometry) paidCutoff
local notation "q" => (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.literalSupportParameter geometry) rootLength
local notation "rectangles" =>
  (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalStrippedRectangles v) leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance
local notation "leftTable" => (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTable" => (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).scale rightScalar⁻¹).balancePlain rightBalance
local notation "leftTests" => (leftProfiles.scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTests" => (rightProfiles.scale rightScalar⁻¹).balancePlain rightBalance

local notation "normalizationRows" =>
  ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRows v) leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar
local notation "ordinaryRows" => (normalizationRows).restrictRows
  (fun h => ¬((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).exceptional h)
local notation "allocation" => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalAllocation v) exceptional firstKernel x j hlive
local notation "pattern" => (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)
local notation "sector" => (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalSector (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) P ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)

variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent a Z Y₁ Y₂ floor padding)
variable (direct : geometry.tag = .direct → parent.geometry.slotCount = 0)
variable (hsmall : 2 * (2 * columnLoss + cutoffExponent) ≤ step)
variable (error : ℝ) (herror : 0 ≤ error)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights : Set ℝ} {originalOrders : Finset (ℕ × ℕ)}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi) (orders : Finset (ℕ × ℕ))
variable {originalBound : ℝ}
variable (original : RawProfileWindow originalRows originalHeights (Set.Icc lo hi)
  originalOrders parent originalBound)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (horders : orders ⊆ originalOrders)
variable (leftComputed : CanonicalLiteralFullKappaInput.ComputedProfiles
  ((leftProfiles.scale leftScalar⁻¹).balancePlain leftBalance)
  (Set.Icc lo hi) orders originalBound)
variable (rightComputed : CanonicalLiteralFullKappaInput.ComputedProfiles
  ((rightProfiles.scale rightScalar⁻¹).balancePlain rightBalance)
  (Set.Icc lo hi) orders originalBound)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)

variable (normBox heightC : ℝ)
variable (analyticWindow : CanonicalOriginalPrimeAnalyticProvider.Window
  (A := A) (P := P) (R := Rchar) parent.theta normBox heightC)
variable (boundary : a.κ < 1 → FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
variable (hslotInverse : ∀ i, (parent.slotCoefficient i)⁻¹ ∈ parent.theta)
variable (hwidthBox : m + q ≤ normBox)
variable (hheight : heightC * (1 + Real.log Z) ≤ analyticHeight)


local notation "leftAllocation" => ((rectangles).leftFrame C false).allocation
local notation "rightAllocation" => ((rectangles).rightFrame C false).allocation
local notation "leftPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => leftSlots.index (SlotRestriction.index (leftAllocation).keep i))
local notation "rightPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => rightSlots.index (SlotRestriction.index (rightAllocation).keep i))

/-- Each side is constructed on the same physical ordinary row class.
No finished side normalization is an input to this producer. -/
def literalPassiveNormalizedFamilyOfWindow :=
  have hp : (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.NonunitLabelStable (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  have hs : (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.SectorLabelStable (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) P :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_sectorLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  have hmaskL : (HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.MaskIndicator ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftOriginal v) leftAtoms).characters) := by
    change (HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.MaskIndicator ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).characters)
    rw [hleftCharacters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra leftSlots.index
  have hmaskR : (HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.MaskIndicator ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightOriginal v) rightAtoms).characters) := by
    change (HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.MaskIndicator ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).characters)
    rw [hrightCharacters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra rightSlots.index
  let mass := (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRowMass v) leftAtoms rightAtoms hmaskL hmaskR hp
    profileBound hprofileBound hprofile).withColumnConstants leftScalar rightScalar).restrictRows
      (fun h => ¬((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).exceptional h)
  have hordinary : (fun h => ¬((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).exceptional h) =
      fun h => (HeckeSkeleton.Moments.EngineStepV2.ActualSecondCorrelationRows.literalCharacter ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v))) C P Rchar F
        oldMoving correction pattern sector h ∉ parent.theta := by
    rw [hexceptional]
  have hk : geometry.skeleton.Krow = Real.log retainedScale / Real.log Z := by
    change Real.log geometry.retainedScale / Real.log Z = _
    rw [hretained]
  have hg : geometry.skeleton.g = g := henlargement
  have hw := (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.literalParameters_secondWidth geometry) columnLoss cutoffExponent rootLength
  rw [hk, hg, hsecond, hopposite, hunit, hnonunit] at hw
  let leftGeometry := (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.atBase geometry) (leftTable).base hbaseLeft
  let rightGeometry := (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.atBase (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.swapSecond geometry)) (rightTable).base hbaseRight
  have hpaidCutoff : 0 ≤ paidCutoff := by positivity
  have hlm : (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.literalRowParameter leftGeometry) paidCutoff = m :=
    (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.atBase_literalRowParameter geometry) (leftTable).base hbaseLeft paidCutoff
  have hrm : (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.literalRowParameter rightGeometry) paidCutoff = m := by
    rw [OriginalNominalGeometry.atBase_literalRowParameter,
      (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.swapSecond_literalRowParameter geometry)]
  have hrootL : idealLogLength (leftTable).base
      (secondSixthRootIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity
        (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity).val = rootLength := by rw [hbaseLeft]
  have hrootR : idealLogLength (rightTable).base
      (secondSixthRootIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity
        (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity).val = rootLength := by
    have he : secondSixthRootIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity
        (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity =
        secondSixthRootIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity
          (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity := by
      unfold secondSixthRootIdeal
      apply congrArg (primePowerProduct (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes)
      funext i
      rw [min_comm]
    rw [he, hbaseRight]
  have hlq : (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.literalSupportParameter leftGeometry) (idealLogLength (leftTable).base
      (secondSixthRootIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity
        (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity).val) = q := by
    rw [hrootL]
    exact (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.atBase_literalSupportParameter geometry) (leftTable).base hbaseLeft rootLength
  have hrq : (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.literalSupportParameter rightGeometry) (idealLogLength (rightTable).base
      (secondSixthRootIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity
        (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity).val) = q := by
    rw [hrootR, OriginalNominalGeometry.atBase_literalSupportParameter,
      (HeckeSkeleton.Moments.EngineStepV2.OriginalNominalGeometry.swapSecond_literalSupportParameter geometry)]
  have hunitR : rightGeometry.ideals.unitPart.val =
      (secondPatternUnitIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity
        (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity pattern).val := by
    rw [secondPatternUnitIdeal_swap]
    exact hunit
  have hdomainL : PairedEngineDomain centered parent a (leftTable).base Y₁ Y₂ floor padding := by
    simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
      CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using domain
  have hdomainR : PairedEngineDomain centered parent a (rightTable).base Y₁ Y₂ floor padding := by
    simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
      CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using domain
  let leftProducer := fun (aL : CanonicalLiteralPassiveNonzero.nonzeroLabels leftTests
      leftAllocation A (choice.mask extra)) (r : Bool) =>
    (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.literalPassiveSideFromWindow (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v))
      (P := P) (Rchar := Rchar) (hclass := hp) (hsector := hs)
      (X := cutoff) (hX := hcutoff) (label := (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v))
      (weight := (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRows v) leftAtoms rightAtoms).withColumnConstants
        leftScalar rightScalar).weight)
      (keep₁ := fun h => ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).correlation h ≠ 0)
      (keep₂ := fun h => ¬((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).exceptional h)
      (rowMass := mass) (d := leftTable) (W := leftTests) (B := leftAllocation)
      (F := F) (choice := choice) (parent := parent) (oldMoving := oldMoving)
      (correction := correction) (hcorr := hcorr) (remaining := remaining) (extra := extra)
      (slots := leftSlots) (a := aL.val) (ha := aL.property)
      (retainedScale := retainedScale) (g := g)
      (a₀ := geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss)
      (oldq := geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E)
      (wo := geometry.skeleton.wo) (cutoffExponent := cutoffExponent) (hscale := hscale)
      (hradius := by
        change _ = CanonicalRowBall.gaussRadius retainedScale (leftTable).base g hscale _
        rw [hbaseLeft]
        rfl)
      (hcutoff := by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
        CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using hcutoffPower)
      (hproduct := by
        intro i hi j hj hpair
        have he := ActualGaussSource.active_gram_pair_norm_le C G _ Z _ hZ
          hactiveColumns i hi j hj hpair
        simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
          CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using he)
      (hpaidSupport := by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
        CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using hpaidSupport)
      («m» := m) («q» := q) (κ := a.κ)
      (hwidth := by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
        CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using hw)
      (inverse := CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
      (hone := hone) (hroot := hroot) (hemb := hemb)
      (hbackground := hbackground) (hslot := hslot) (side := .left)
      (firstSign := firstSign) (rectangle := r) (keep₂_eq := hordinary)
      (parentParameters := a) (step := step) (geometry := leftGeometry)
      (capacityCutoff := paidCutoff) (hcapacityCutoff := hpaidCutoff) (hsmall := hsmall)
      (rowParameter := hlm) (supportParameter := hlq) (kappa := rfl)
      (domain := hdomainL) (direct := direct) (error := error) (herr := herror)
      (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
      (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
      (reference := reference) (time := time) (inverse_eq := rfl)
      (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
      (original := original) (hreference := hreference) (htime := htime) (horders := horders)
      (computed := leftComputed) (hprimeOrders := hprimeOrders)
      (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
      (normBox := normBox) (heightC := heightC) (analyticWindow := analyticWindow)
      (boundary := boundary) (hslotInverse := hslotInverse) (hwidthBox := hwidthBox)
      (hheight := by
        simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
          CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using hheight)
  let rightProducer := fun (aR : CanonicalLiteralPassiveNonzero.nonzeroLabels rightTests
      rightAllocation A (choice.mask extra)) (r : Bool) =>
    (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.literalPassiveSideFromWindow (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v))
      (P := P) (Rchar := Rchar) (hclass := hp) (hsector := hs)
      (X := cutoff) (hX := hcutoff) (label := (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v))
      (weight := (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRows v) leftAtoms rightAtoms).withColumnConstants
        leftScalar rightScalar).weight)
      (keep₁ := fun h => ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows ∅ cutoff hcutoff (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).correlation h ≠ 0)
      (keep₂ := fun h => ¬((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).exceptional h)
      (rowMass := mass) (d := rightTable) (W := rightTests) (B := rightAllocation)
      (F := F) (choice := choice) (parent := parent) (oldMoving := oldMoving)
      (correction := correction) (hcorr := hcorr) (remaining := remaining) (extra := extra)
      (slots := rightSlots) (a := aR.val) (ha := aR.property)
      (retainedScale := retainedScale) (g := g)
      (a₀ := geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss)
      (oldq := geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E)
      (wo := geometry.skeleton.wo) (cutoffExponent := cutoffExponent) (hscale := hscale)
      (hradius := by
        change _ = CanonicalRowBall.gaussRadius retainedScale (rightTable).base g hscale _
        rw [hbaseRight]
        rfl)
      (hcutoff := by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
        CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using hcutoffPower)
      (hproduct := by
        intro i hi j hj hpair
        have he := ActualGaussSource.active_gram_pair_norm_le C G _ Z _ hZ
          hactiveColumns i hi j hj hpair
        simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
          CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using he)
      (hpaidSupport := by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
        CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using hpaidSupport)
      («m» := m) («q» := q) (κ := a.κ)
      (hwidth := by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
        CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using hw)
      (inverse := CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
      (hone := hone) (hroot := hroot) (hemb := hemb)
      (hbackground := hbackground) (hslot := hslot) (side := .right)
      (firstSign := -firstSign) (rectangle := r) (keep₂_eq := hordinary)
      (parentParameters := a) (step := step) (geometry := rightGeometry)
      (capacityCutoff := paidCutoff) (hcapacityCutoff := hpaidCutoff) (hsmall := hsmall)
      (rowParameter := hrm) (supportParameter := hrq) (kappa := rfl)
      (domain := hdomainR) (direct := direct) (error := error) (herr := herror)
      (hsecond := hopposite) (hopposite := hsecond) (hunit := hunitR)
      (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
      (reference := reference) (time := time) (inverse_eq := rfl)
      (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
      (original := original) (hreference := hreference) (htime := htime) (horders := horders)
      (computed := rightComputed) (hprimeOrders := hprimeOrders)
      (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
      (normBox := normBox) (heightC := heightC) (analyticWindow := analyticWindow)
      (boundary := boundary) (hslotInverse := hslotInverse) (hwidthBox := hwidthBox)
      (hheight := by
        simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
          CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using hheight)
  let result := CanonicalLiteralPassiveNormalizedFamily.family C ordinaryRows leftTests rightTests
    leftAllocation rightAllocation leftPaid rightPaid (choice.mask extra) (choice.mask extra)
    firstSign (-firstSign)
    (fun b => leftProducer b.1 b.2)
    (fun b => rightProducer b.1 b.2)
    (hbaseRight.trans hbaseLeft.symm)
  result.atBase Z hbaseLeft

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStepV2

