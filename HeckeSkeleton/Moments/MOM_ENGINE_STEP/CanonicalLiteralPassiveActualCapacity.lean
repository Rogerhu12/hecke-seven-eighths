import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNormalizedRadii
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralArithmeticInput

/-!
# Actual capacity inputs of the independent passive family

The side records below expose the computations already stored in the
covered passive family. Their calibrations and normalized capacities
are definitionally the existing ones. No new removed set or child is
selected. Original length bindings and individual prime atoms are
calculated from those same calibrations.

An active member supplies its own original ordinary-row anchor. The
left and right passive divisors remain independent, and the actual
right capacity uses the original swapped row mass exactly once.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralActualProfiles PrimeCancellation.Analytic

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

local instance canonicalLiteralPassiveCapacityCircleCharacterFintype :
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
variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoveredClassKey LC RC)
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)
variable (hlive : (v.leaf exceptional firstKernel x j).Live) (firstSign : ℝ)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (leftScalar rightScalar : ℂ)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ p ∈ firstSupport, Prime p)
variable (leftProfiles : ProfileSupport (v.literalLeftAtoms leftAtoms)
  ((primeSupport A.cS ∪ firstSupport) ∪ primeSupport v.1.val.1))
variable (rightProfiles : ProfileSupport (v.literalRightAtoms rightAtoms)
  ((primeSupport A.cS ∪ firstSupport) ∪ primeSupport v.1.val.1))
variable (hbaseLeft : (v.literalLeftAtoms leftAtoms).base = Z)
variable (hbaseRight : (v.literalRightAtoms rightAtoms).base = Z)
variable {ω ψ : HeckeCharacter K}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (choice : CanonicalLiteralPassiveSource.PhaseChoice F C)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (leftRecipe : CanonicalLiteralActualCharacters.Recipe P Rchar F parent oldMoving
  correction remaining extra (v.literalLeftAtoms leftAtoms))
variable (rightRecipe : CanonicalLiteralActualCharacters.Recipe P Rchar F parent oldMoving
  correction remaining extra (v.literalRightAtoms rightAtoms))
variable (profileBound : ℝ) (hprofileBound : 0 ≤ profileBound)
variable (hprofile : ∀ h ∈ (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).rows,
  ‖v.chart.weight h‖ ≤ profileBound)
variable (a : RealParameters) (step : ℝ)
variable (geometry : OriginalNominalGeometry (K := K) a Z step)
variable (hretained : geometry.retainedScale = retainedScale)
variable (henlargement : geometry.enlargement = g)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct v.block.primes v.block.leftMultiplicity).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct v.block.primes v.block.rightMultiplicity).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity
    (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)).val)
variable (hnonunit : geometry.ideals.nonunitPart.val =
  (secondPatternNonunitIdeal v.block.primes
    (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)).val)
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
variable (hexceptional : (v.leaf exceptional firstKernel x j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).literalCharacter C P Rchar F oldMoving
    correction (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)
    (v.chart.originalSector P ∅ cutoff hcutoff v.rowLabel) h ∈ parent.theta)

local notation "rootLength" => idealLogLength Z
  (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity).val
local notation "paidCutoff" => 2 * columnLoss + cutoffExponent
local notation "m" => geometry.literalRowParameter paidCutoff
local notation "q" => geometry.literalSupportParameter rootLength
local notation "rectangles" =>
  v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance
local notation "leftTable" => ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTable" => ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).balancePlain rightBalance
local notation "leftTests" => (leftProfiles.profiles.scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTests" => (rightProfiles.profiles.scale rightScalar⁻¹).balancePlain rightBalance

local notation "normalizationRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar
local notation "ordinaryRows" => (normalizationRows).restrictRows
  (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
local notation "allocation" => v.literalAllocation exceptional firstKernel x j hlive
local notation "pattern" => v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel
local notation "sector" => v.chart.originalSector P ∅ cutoff hcutoff v.rowLabel

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
  ((leftProfiles.profiles.scale leftScalar⁻¹).balancePlain leftBalance)
  (Set.Icc lo hi) orders originalBound)
variable (rightComputed : CanonicalLiteralFullKappaInput.ComputedProfiles
  ((rightProfiles.profiles.scale rightScalar⁻¹).balancePlain rightBalance)
  (Set.Icc lo hi) orders originalBound)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)

local notation "leftAllocation" => ((rectangles).leftFrame C false).allocation
local notation "rightAllocation" => ((rectangles).rightFrame C false).allocation
local notation "leftPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => leftRecipe.slots.index (SlotRestriction.index (leftAllocation).keep i))
local notation "rightPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => rightRecipe.slots.index (SlotRestriction.index (rightAllocation).keep i))

local notation "production" =>
  v.literalPassiveNormalizedFamily
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

local notation "Labels" => CanonicalLiteralPassiveNormalizedFamily.PairLabel (A := A)
  leftTests rightTests leftAllocation rightAllocation (choice.mask extra) (choice.mask extra)
local notation "passiveLeft" => fun b : Labels =>
  CanonicalLiteralPassiveSource.branch leftTests leftAllocation A (choice.mask extra) b.1.1.val
local notation "passiveRight" => fun b : Labels =>
  CanonicalLiteralPassiveSource.branch rightTests rightAllocation A (choice.mask extra) b.2.1.val
private theorem passiveCapacity_leftEndpoints
    {H J : Type*} [Fintype J] [DecidableEq J]
    {a₀ : RealParameters} {Z₀ step₀ : ℝ}
    (rows : ActualSecondCorrelationRows A σ H J)
    (geometry₀ : OriginalNominalGeometry (K := K) a₀ Z₀ step₀)
    (base : ℝ) (hbase : base = Z₀) (physicalError : ℝ) :
    (geometry₀.atBase base hbase).literalRowParameter physicalError =
        geometry₀.literalRowParameter physicalError ∧
      (geometry₀.atBase base hbase).literalSupportParameter
        (idealLogLength base
          (secondSixthRootIdeal rows.primes rows.leftMultiplicity rows.rightMultiplicity).val) =
        geometry₀.literalSupportParameter (idealLogLength Z₀
          (secondSixthRootIdeal rows.primes rows.leftMultiplicity rows.rightMultiplicity).val) := by
  refine ⟨geometry₀.atBase_literalRowParameter base hbase physicalError, ?_⟩
  rw [OriginalNominalGeometry.atBase_literalSupportParameter, hbase]

private theorem passiveCapacity_rightEndpoints
    {H J : Type*} [Fintype J] [DecidableEq J]
    {a₀ : RealParameters} {Z₀ step₀ : ℝ}
    (rows : ActualSecondCorrelationRows A σ H J)
    (geometry₀ : OriginalNominalGeometry (K := K) a₀ Z₀ step₀)
    (base : ℝ) (hbase : base = Z₀) (physicalError : ℝ) :
    (geometry₀.swapSecond.atBase base hbase).literalRowParameter physicalError =
        geometry₀.literalRowParameter physicalError ∧
      (geometry₀.swapSecond.atBase base hbase).literalSupportParameter
        (idealLogLength base
          (secondSixthRootIdeal rows.primes rows.rightMultiplicity rows.leftMultiplicity).val) =
        geometry₀.literalSupportParameter (idealLogLength Z₀
          (secondSixthRootIdeal rows.primes rows.leftMultiplicity rows.rightMultiplicity).val) := by
  have hroot : secondSixthRootIdeal rows.primes rows.rightMultiplicity rows.leftMultiplicity =
      secondSixthRootIdeal rows.primes rows.leftMultiplicity rows.rightMultiplicity :=
    SecondColumnSide.literal_root .right rows
  constructor
  · rw [OriginalNominalGeometry.atBase_literalRowParameter,
      OriginalNominalGeometry.swapSecond_literalRowParameter]
  · rw [OriginalNominalGeometry.atBase_literalSupportParameter,
      OriginalNominalGeometry.swapSecond_literalSupportParameter, hroot, hbase]

local notation "leftGeometry" => geometry.atBase (leftTable).base hbaseLeft
local notation "rightGeometry" => geometry.swapSecond.atBase (rightTable).base hbaseRight

local notation "originalMass" =>
  v.literalOriginalArithmeticMass
    (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := G) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff) (hcutoff := hcutoff)
    (hnorm := hnorm) (dimension := dimension) (width := width)
    (character := character) (dyad := dyad) (LC := LC) (RC := RC)
    (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar)
    (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
    (remaining := remaining) (extra := extra)
    (leftRecipe := leftRecipe) (rightRecipe := rightRecipe)
    (profileBound := profileBound) (hprofileBound := hprofileBound) (hprofile := hprofile)

local notation "leftPassiveTable" =>
  CanonicalLiteralPassiveSource.table leftTests leftAllocation A leftPaid
local notation "rightPassiveTable" =>
  CanonicalLiteralPassiveSource.table rightTests rightAllocation A rightPaid
local notation "leftPassiveTests" =>
  CanonicalLiteralPassiveSource.profiles leftTests leftAllocation A leftPaid
local notation "rightPassiveTests" =>
  CanonicalLiteralPassiveSource.profiles rightTests rightAllocation A rightPaid
local notation "leftFrame" => fun b : Labels =>
  CanonicalLiteralPassiveFrames.frame leftTests leftAllocation A leftPaid C ordinaryRows
    .left (choice.mask extra) b.1.1.val firstSign b.1.2
local notation "rightFrame" => fun b : Labels =>
  CanonicalLiteralPassiveFrames.frame rightTests rightAllocation A rightPaid C ordinaryRows
    .right (choice.mask extra) b.2.1.val (-firstSign) b.2.2
local notation "leftOriginalSlots" => CanonicalLiteralPassiveFrames.tableOriginalSlots
  leftTests leftAllocation A leftPaid parent leftRecipe.slots
local notation "rightOriginalSlots" => CanonicalLiteralPassiveFrames.tableOriginalSlots
  rightTests rightAllocation A rightPaid parent rightRecipe.slots

/-- The already constructed left side, before its child projection. -/
def literalPassiveLeftSideNormalization :=
  fun analyticLeft analyticRight heightLeft heightRight (b : Labels) =>
  let cal := (production analyticLeft analyticRight heightLeft heightRight).leftCalibration b
  show SecondSideNormalization (leftFrame b) ω ψ Set.univ Set.univ (Set.Icc 0 hi) orders from by
  have hcoordinates := passiveCapacity_leftEndpoints ordinaryRows geometry (leftTable).base hbaseLeft paidCutoff
  have hm := hcoordinates.1
  have hq := hcoordinates.2
  have hdomain : PairedEngineDomain centered parent a (leftTable).base Y₁ Y₂ floor padding := by
    have hb : (leftTable).base = Z := hbaseLeft
    simpa only [hb] using domain
  exact (leftPassiveTable).produceLiteralSideAll leftPassiveTests ordinaryRows .left (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (CanonicalLiteralPassiveFrames.columnExterior leftTests leftAllocation A)
    (CanonicalLiteralPassiveFrames.columnExterior_val_of_mem leftTests leftAllocation A)
    firstSign b.1.2 b.1.1.val.val.1 b.1.1.val.val.2
    (Finset.mem_filter.mp b.1.1.val.property).2 cal
    P Rchar choice.phases parent oldMoving correction hcorr remaining 1 a step leftGeometry
    pattern sector leftOriginalSlots paidCutoff reference time
    (by intro ξ; rw [hm, hq]; rfl) (by rw [hm, hq]; rfl) hdomain direct (by positivity) hsmall error herror
    v.block.left_positive v.block.right_positive hsecond hopposite hunit hstep mesh hmesh hfit
    lo hi hlo hhi orders original hreference htime horders
    (leftComputed.passiveTable leftAllocation A leftPaid) hprimeOrders
    δ analyticHeight hδ hδhi (analyticLeft b.1.1 b.1.2) (heightLeft b.1.1 b.1.2)

/-- The original occurrence and scale ledger in the same left capacity. -/
def literalPassiveLeftLengthBinding :=
  fun analyticLeft analyticRight heightLeft heightRight (b : Labels) =>
  let cal := (production analyticLeft analyticRight heightLeft heightRight).leftCalibration b
  show cal.OriginalSixthLengthBinding parent a step leftGeometry
      (idealLogLength (leftTable).base
        (secondSixthRootIdeal (ordinaryRows).primes (ordinaryRows).leftMultiplicity
          (ordinaryRows).rightMultiplicity).val) from by
  have hcoordinates := passiveCapacity_leftEndpoints ordinaryRows geometry (leftTable).base hbaseLeft paidCutoff
  have hm := hcoordinates.1
  have hq := hcoordinates.2
  have hdomain : PairedEngineDomain centered parent a (leftTable).base Y₁ Y₂ floor padding := by
    have hb : (leftTable).base = Z := hbaseLeft
    simpa only [hb] using domain
  exact (leftPassiveTable).literalCapacityBinding ordinaryRows .left (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (CanonicalLiteralPassiveFrames.columnExterior leftTests leftAllocation A)
    (CanonicalLiteralPassiveFrames.columnExterior_val_of_mem leftTests leftAllocation A)
    firstSign b.1.2 b.1.1.val.val.1 b.1.1.val.val.2
    (Finset.mem_filter.mp b.1.1.val.property).2 cal
    parent a step leftGeometry (slots := leftOriginalSlots) (cutoff := paidCutoff)
    (hparameters := by rw [hm, hq]; rfl) (domain := hdomain) (direct := direct)
    (hcutoff := by positivity) (hsmall := hsmall) (error := error) (herr := herror)

/-- Individual original-prime bounds from the same computed Fourier profiles. -/
def literalPassiveLeftCapacityAtoms :=
  fun analyticLeft analyticRight heightLeft heightRight (b : Labels) =>
  let cal := (production analyticLeft analyticRight heightLeft heightRight).leftCalibration b
  show cal.OriginalCapacityAtoms from by
  have hcoordinates := passiveCapacity_leftEndpoints ordinaryRows geometry (leftTable).base hbaseLeft paidCutoff
  have hm := hcoordinates.1
  have hq := hcoordinates.2
  have hdomain : PairedEngineDomain centered parent a (leftTable).base Y₁ Y₂ floor padding := by
    have hb : (leftTable).base = Z := hbaseLeft
    simpa only [hb] using domain
  exact (leftPassiveTable).literalCapacityAtoms leftPassiveTests ordinaryRows .left (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (CanonicalLiteralPassiveFrames.columnExterior leftTests leftAllocation A)
    (CanonicalLiteralPassiveFrames.columnExterior_val_of_mem leftTests leftAllocation A)
    firstSign b.1.2 b.1.1.val.val.1 b.1.1.val.val.2
    (Finset.mem_filter.mp b.1.1.val.property).2 cal
    P Rchar choice.phases parent oldMoving correction hcorr remaining 1 a step leftGeometry
    pattern sector leftOriginalSlots paidCutoff reference time
    (by intro ξ; rw [hm, hq]; rfl) (by rw [hm, hq]; rfl) hdomain mesh hmesh hfit lo hi hlo hhi orders original
    hreference htime horders (leftComputed.passiveTable leftAllocation A leftPaid) hprimeOrders
    δ analyticHeight hδ hδhi (analyticLeft b.1.1 b.1.2) (heightLeft b.1.1 b.1.2)

/-- The already constructed right side, before its child projection. -/
def literalPassiveRightSideNormalization :=
  fun analyticLeft analyticRight heightLeft heightRight (b : Labels) =>
  let cal := (production analyticLeft analyticRight heightLeft heightRight).rightCalibration b
  show SecondSideNormalization (rightFrame b) ω ψ Set.univ Set.univ (Set.Icc 0 hi) orders from by
  have hcoordinates := passiveCapacity_rightEndpoints ordinaryRows geometry (rightTable).base hbaseRight paidCutoff
  have hm := hcoordinates.1
  have hq := hcoordinates.2
  have hdomain : PairedEngineDomain centered parent a (rightTable).base Y₁ Y₂ floor padding := by
    have hb : (rightTable).base = Z := hbaseRight
    simpa only [hb] using domain
  have hunitR : (rightGeometry).ideals.unitPart.val =
      (secondPatternUnitIdeal (ordinaryRows).primes (ordinaryRows).rightMultiplicity
        (ordinaryRows).leftMultiplicity pattern).val := by
    rw [secondPatternUnitIdeal_swap]
    exact hunit
  exact (rightPassiveTable).produceLiteralSideAll rightPassiveTests ordinaryRows .right (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (CanonicalLiteralPassiveFrames.columnExterior rightTests rightAllocation A)
    (CanonicalLiteralPassiveFrames.columnExterior_val_of_mem rightTests rightAllocation A)
    (-firstSign) b.2.2 b.2.1.val.val.1 b.2.1.val.val.2
    (Finset.mem_filter.mp b.2.1.val.property).2 cal
    P Rchar choice.phases parent oldMoving correction hcorr remaining 1 a step rightGeometry
    pattern sector rightOriginalSlots paidCutoff reference time
    (by intro ξ; rw [hm, hq]; rfl) (by rw [hm, hq]; rfl) hdomain direct (by positivity) hsmall error herror
    v.block.left_positive v.block.right_positive hopposite hsecond hunitR hstep mesh hmesh hfit
    lo hi hlo hhi orders original hreference htime horders
    (rightComputed.passiveTable rightAllocation A rightPaid) hprimeOrders
    δ analyticHeight hδ hδhi (analyticRight b.2.1 b.2.2) (heightRight b.2.1 b.2.2)

/-- The original occurrence and scale ledger in the same right capacity. -/
def literalPassiveRightLengthBinding :=
  fun analyticLeft analyticRight heightLeft heightRight (b : Labels) =>
  let cal := (production analyticLeft analyticRight heightLeft heightRight).rightCalibration b
  show cal.OriginalSixthLengthBinding parent a step rightGeometry
      (idealLogLength (rightTable).base
        (secondSixthRootIdeal (ordinaryRows).primes (ordinaryRows).rightMultiplicity
          (ordinaryRows).leftMultiplicity).val) from by
  have hcoordinates := passiveCapacity_rightEndpoints ordinaryRows geometry (rightTable).base hbaseRight paidCutoff
  have hm := hcoordinates.1
  have hq := hcoordinates.2
  have hdomain : PairedEngineDomain centered parent a (rightTable).base Y₁ Y₂ floor padding := by
    have hb : (rightTable).base = Z := hbaseRight
    simpa only [hb] using domain
  exact (rightPassiveTable).literalCapacityBinding ordinaryRows .right (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (CanonicalLiteralPassiveFrames.columnExterior rightTests rightAllocation A)
    (CanonicalLiteralPassiveFrames.columnExterior_val_of_mem rightTests rightAllocation A)
    (-firstSign) b.2.2 b.2.1.val.val.1 b.2.1.val.val.2
    (Finset.mem_filter.mp b.2.1.val.property).2 cal
    parent a step rightGeometry (slots := rightOriginalSlots) (cutoff := paidCutoff)
    (hparameters := by rw [hm, hq]; rfl) (domain := hdomain) (direct := direct)
    (hcutoff := by positivity) (hsmall := hsmall) (error := error) (herr := herror)

/-- Individual original-prime bounds from the same computed Fourier profiles. -/
def literalPassiveRightCapacityAtoms :=
  fun analyticLeft analyticRight heightLeft heightRight (b : Labels) =>
  let cal := (production analyticLeft analyticRight heightLeft heightRight).rightCalibration b
  show cal.OriginalCapacityAtoms from by
  have hcoordinates := passiveCapacity_rightEndpoints ordinaryRows geometry (rightTable).base hbaseRight paidCutoff
  have hm := hcoordinates.1
  have hq := hcoordinates.2
  have hdomain : PairedEngineDomain centered parent a (rightTable).base Y₁ Y₂ floor padding := by
    have hb : (rightTable).base = Z := hbaseRight
    simpa only [hb] using domain
  exact (rightPassiveTable).literalCapacityAtoms rightPassiveTests ordinaryRows .right (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (CanonicalLiteralPassiveFrames.columnExterior rightTests rightAllocation A)
    (CanonicalLiteralPassiveFrames.columnExterior_val_of_mem rightTests rightAllocation A)
    (-firstSign) b.2.2 b.2.1.val.val.1 b.2.1.val.val.2
    (Finset.mem_filter.mp b.2.1.val.property).2 cal
    P Rchar choice.phases parent oldMoving correction hcorr remaining 1 a step rightGeometry
    pattern sector rightOriginalSlots paidCutoff reference time
    (by intro ξ; rw [hm, hq]; rfl) (by rw [hm, hq]; rfl) hdomain mesh hmesh hfit lo hi hlo hhi orders original
    hreference htime horders (rightComputed.passiveTable rightAllocation A rightPaid) hprimeOrders
    δ analyticHeight hδ hδhi (analyticRight b.2.1 b.2.2) (heightRight b.2.1 b.2.2)

local notation "leftSide" =>
  v.literalPassiveLeftSideNormalization
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

local notation "rightSide" =>
  v.literalPassiveRightSideNormalization
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

local notation "leftLengths" =>
  v.literalPassiveLeftLengthBinding
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

local notation "rightLengths" =>
  v.literalPassiveRightLengthBinding
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

local notation "leftAtomsInput" =>
  v.literalPassiveLeftCapacityAtoms
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

local notation "rightAtomsInput" =>
  v.literalPassiveRightCapacityAtoms
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

local notation "leftFrozen" => fun b : Labels =>
  CanonicalLiteralPassiveFrames.frozenBounds leftTests leftAllocation leftPaid C ordinaryRows
    .left (choice.mask extra) b.1.1.val firstSign b.1.2
    (CanonicalLiteralPaidCharacters.paidSourceCharacters_maskIndicator P Rchar choice.phases
      parent oldMoving correction remaining
      (fun i => leftRecipe.slots.index (SlotRestriction.index (leftAllocation).keep i)))
    b.1.1.property
local notation "rightFrozen" => fun b : Labels =>
  CanonicalLiteralPassiveFrames.frozenBounds rightTests rightAllocation rightPaid C ordinaryRows
    .right (choice.mask extra) b.2.1.val (-firstSign) b.2.2
    (CanonicalLiteralPaidCharacters.paidSourceCharacters_maskIndicator P Rchar choice.phases
      parent oldMoving correction remaining
      (fun i => rightRecipe.slots.index (SlotRestriction.index (rightAllocation).keep i)))
    b.2.1.property

@[simp] theorem literalPassiveLeftSideNormalization_calibration :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (leftSide analyticLeft analyticRight heightLeft heightRight b).calibration =
        (production analyticLeft analyticRight heightLeft heightRight).leftCalibration b := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

/-- The exposed side is the same capacity which selected the stored child. -/
@[simp] theorem literalPassiveNormalizedFamily_leftCapacity_eq :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (production analyticLeft analyticRight heightLeft heightRight).leftCapacity b =
        (leftSide analyticLeft analyticRight heightLeft heightRight b).normalizedCapacityData := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveNormalizedFamily_leftArithmeticCalibration :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (leftFrame b).arithmeticCalibration
          ((production analyticLeft analyticRight heightLeft heightRight).leftCalibration b)
          originalMass (leftFrozen b) =
        (production analyticLeft analyticRight heightLeft heightRight).leftCalibration b := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveLeftLengthBinding_rawError :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (leftLengths analyticLeft analyticRight heightLeft heightRight b).rawScaleError =
        (leftPassiveTable).computedRawError geometry.skeleton.rawDegree error b.1.2 := by
  intro analyticLeft analyticRight heightLeft heightRight b
  change (leftPassiveTable).computedRawError (leftGeometry).skeleton.rawDegree error b.1.2 = _
  rw [OriginalNominalGeometry.atBase_skeleton]

@[simp] theorem literalPassiveLeftLengthBinding_widthError :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (leftLengths analyticLeft analyticRight heightLeft heightRight b).scales.error = paidCutoff := by
  intro analyticLeft analyticRight heightLeft heightRight b
  simp only [literalPassiveLeftLengthBinding,
    CanonicalLiteralRectangles.Atoms.literalCapacityBinding,
    CanonicalLiteralRectangles.Atoms.factorsOriginalSixthLengthsAll_error]

@[simp] theorem literalPassiveLeftCapacityAtoms_leftAnnulus :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (leftAtomsInput analyticLeft analyticRight heightLeft heightRight b).leftAnnulus = hi := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveLeftCapacityAtoms_rightAnnulus :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (leftAtomsInput analyticLeft analyticRight heightLeft heightRight b).rightAnnulus = hi := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveLeftSideNormalization_bounds :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (leftSide analyticLeft analyticRight heightLeft heightRight b).bounds = fun _ => 1 := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveRightSideNormalization_calibration :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (rightSide analyticLeft analyticRight heightLeft heightRight b).calibration =
        (production analyticLeft analyticRight heightLeft heightRight).rightCalibration b := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

/-- The exposed side is the same capacity which selected the stored child. -/
@[simp] theorem literalPassiveNormalizedFamily_rightCapacity_eq :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (production analyticLeft analyticRight heightLeft heightRight).rightCapacity b =
        (rightSide analyticLeft analyticRight heightLeft heightRight b).normalizedCapacityData := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveNormalizedFamily_rightArithmeticCalibration :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (rightFrame b).arithmeticCalibration
          ((production analyticLeft analyticRight heightLeft heightRight).rightCalibration b)
          originalMass (rightFrozen b) =
        (production analyticLeft analyticRight heightLeft heightRight).rightCalibration b := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveRightLengthBinding_rawError :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (rightLengths analyticLeft analyticRight heightLeft heightRight b).rawScaleError =
        (rightPassiveTable).computedRawError geometry.swapSecond.skeleton.rawDegree error b.2.2 := by
  intro analyticLeft analyticRight heightLeft heightRight b
  change (rightPassiveTable).computedRawError (rightGeometry).skeleton.rawDegree error b.2.2 = _
  rw [OriginalNominalGeometry.atBase_skeleton]

@[simp] theorem literalPassiveRightLengthBinding_widthError :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (rightLengths analyticLeft analyticRight heightLeft heightRight b).scales.error = paidCutoff := by
  intro analyticLeft analyticRight heightLeft heightRight b
  simp only [literalPassiveRightLengthBinding,
    CanonicalLiteralRectangles.Atoms.literalCapacityBinding,
    CanonicalLiteralRectangles.Atoms.factorsOriginalSixthLengthsAll_error]

@[simp] theorem literalPassiveRightCapacityAtoms_leftAnnulus :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (rightAtomsInput analyticLeft analyticRight heightLeft heightRight b).leftAnnulus = hi := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveRightCapacityAtoms_rightAnnulus :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (rightAtomsInput analyticLeft analyticRight heightLeft heightRight b).rightAnnulus = hi := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveRightSideNormalization_bounds :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      (rightSide analyticLeft analyticRight heightLeft heightRight b).bounds = fun _ => 1 := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

/-- This is the original row-mass capacity of the same left side. -/
theorem literalPassiveNormalizedFamily_leftCapacity_actual :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels) (anchor : (ordinaryRows).rows),
      HEq (leftSide analyticLeft analyticRight heightLeft heightRight b).capacity
        ((leftLengths analyticLeft analyticRight heightLeft heightRight b).capacityInput
          originalMass v.block.right_positive anchor hsecond hopposite hunit
          hstep mesh hmesh hfit (leftAtomsInput analyticLeft analyticRight heightLeft heightRight b)) := by
  intro analyticLeft analyticRight heightLeft heightRight b anchor
  let cal := (production analyticLeft analyticRight heightLeft heightRight).leftCalibration b
  have hcoordinates := passiveCapacity_leftEndpoints ordinaryRows geometry (leftTable).base hbaseLeft paidCutoff
  have hm := hcoordinates.1
  have hq := hcoordinates.2
  have hdomain : PairedEngineDomain centered parent a (leftTable).base Y₁ Y₂ floor padding := by
    have hb : (leftTable).base = Z := hbaseLeft
    simpa only [hb] using domain
  exact (leftPassiveTable).produceLiteralLeftSideAll_capacity_actual_heq leftPassiveTests
    ordinaryRows (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (CanonicalLiteralPassiveFrames.columnExterior leftTests leftAllocation A)
    (CanonicalLiteralPassiveFrames.columnExterior_val_of_mem leftTests leftAllocation A)
    firstSign b.1.2 b.1.1.val.val.1 b.1.1.val.val.2
    (Finset.mem_filter.mp b.1.1.val.property).2 cal
    P Rchar choice.phases parent oldMoving correction hcorr remaining 1 a step leftGeometry
    pattern sector leftOriginalSlots paidCutoff reference time
    (by intro ξ; rw [hm, hq]; rfl) (by rw [hm, hq]; rfl) hdomain direct (by positivity)
    hsmall error herror v.block.left_positive v.block.right_positive hsecond hopposite hunit
    hstep mesh hmesh hfit lo hi hlo hhi orders original hreference htime horders
    (leftComputed.passiveTable leftAllocation A leftPaid) hprimeOrders
    δ analyticHeight hδ hδhi (analyticLeft b.1.1 b.1.2) (heightLeft b.1.1 b.1.2)
    originalMass anchor rfl

/-- This is the original row-mass capacity of the same right side. -/
theorem literalPassiveNormalizedFamily_rightCapacity_actual :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels) (anchor : (ordinaryRows).rows),
      HEq (rightSide analyticLeft analyticRight heightLeft heightRight b).capacity
        ((rightLengths analyticLeft analyticRight heightLeft heightRight b).capacityInput
          ((originalMass).swapColumns v.block.right_positive) (originalMass).left_positive anchor hopposite hsecond hunit
          hstep mesh hmesh hfit (rightAtomsInput analyticLeft analyticRight heightLeft heightRight b)) := by
  intro analyticLeft analyticRight heightLeft heightRight b anchor
  let cal := (production analyticLeft analyticRight heightLeft heightRight).rightCalibration b
  have hcoordinates := passiveCapacity_rightEndpoints ordinaryRows geometry (rightTable).base hbaseRight paidCutoff
  have hm := hcoordinates.1
  have hq := hcoordinates.2
  have hdomain : PairedEngineDomain centered parent a (rightTable).base Y₁ Y₂ floor padding := by
    have hb : (rightTable).base = Z := hbaseRight
    simpa only [hb] using domain
  have hunitR : (rightGeometry).ideals.unitPart.val =
      (secondPatternUnitIdeal (ordinaryRows).primes (ordinaryRows).rightMultiplicity
        (ordinaryRows).leftMultiplicity pattern).val := by
    rw [secondPatternUnitIdeal_swap]
    exact hunit
  exact (rightPassiveTable).produceLiteralRightSideAll_capacity_actual_heq rightPassiveTests
    ordinaryRows (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (CanonicalLiteralPassiveFrames.columnExterior rightTests rightAllocation A)
    (CanonicalLiteralPassiveFrames.columnExterior_val_of_mem rightTests rightAllocation A)
    (-firstSign) b.2.2 b.2.1.val.val.1 b.2.1.val.val.2
    (Finset.mem_filter.mp b.2.1.val.property).2 cal
    P Rchar choice.phases parent oldMoving correction hcorr remaining 1 a step rightGeometry
    pattern sector rightOriginalSlots paidCutoff reference time
    (by intro ξ; rw [hm, hq]; rfl) (by rw [hm, hq]; rfl) hdomain direct (by positivity)
    hsmall error herror v.block.left_positive v.block.right_positive hopposite hsecond hunitR
    hstep mesh hmesh hfit lo hi hlo hhi orders original hreference htime horders
    (rightComputed.passiveTable rightAllocation A rightPaid) hprimeOrders
    δ analyticHeight hδ hδhi (analyticRight b.2.1 b.2.2) (heightRight b.2.1 b.2.2)
    originalMass anchor rfl

/-- Activity is tested on this new passive source itself. Its own
nonzero energy supplies an original ordinary-row witness. -/
theorem literalPassiveNormalizedFamily_activeRows_nonempty :
    ∀ analyticLeft analyticRight heightLeft heightRight
      (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ),
      Nonempty (ordinaryRows).rows := by
  intro analyticLeft analyticRight heightLeft heightRight b
  have hnonzero := (Finset.mem_filter.mp b.property).2.1
  obtain ⟨ξ, hξ⟩ := not_forall.mp hnonzero
  have hrows : (leftFrame b.val).source.rows.Nonempty := by
    by_contra he
    have hempty := Finset.not_nonempty_iff_eq_empty.mp he
    apply hξ
    change (leftFrame b.val).source.energy (σ := σ) ξ = 0
    simp only [ActualAllocatedSource.energy, jointColumnEnergy, hempty, Finset.sum_empty]
  obtain ⟨h, _⟩ := hrows
  exact ⟨⟨h.val, (Finset.mem_filter.mp h.property).1⟩⟩

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveLeftSideNormalization

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveLeftLengthBinding

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveLeftCapacityAtoms

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveRightSideNormalization

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveRightLengthBinding

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveRightCapacityAtoms

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_leftCapacity_eq

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_leftArithmeticCalibration

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_leftCapacity_actual

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_rightCapacity_eq

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_rightArithmeticCalibration

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_rightCapacity_actual

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_activeRows_nonempty
