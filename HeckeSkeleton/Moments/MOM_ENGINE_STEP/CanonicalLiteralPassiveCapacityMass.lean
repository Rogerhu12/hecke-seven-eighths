import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveActualCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveCapacityWindow
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralOriginalFrozenPairCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtomCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredGaussScale
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionIndependentMass

/-!
# The actual passive family pays its independent allocation costs

The capacities and normalized children below are precisely those in
the actual covered passive family. Their original prime and length
inputs are computed by the existing producers. Activity supplies an
ordinary-row anchor and the valid original comparison rectangle.

The original second allocation has one shared divisor. Its two frozen
costs remain outside the new family and contribute one slot power.
The two later passive divisors are independent: both square-root norms
are retained in the sharp estimate. Common and new frozen atoms give
the other two slot powers, and the original row profile occurs once.
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

local instance canonicalLiteralPassiveCapacityMassCircleCharacterFintype :
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

local notation "leftCapacityProof" =>
  v.literalPassiveNormalizedFamily_leftCapacity_actual
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

local notation "rightCapacityProof" =>
  v.literalPassiveNormalizedFamily_rightCapacity_actual
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

local notation "activeRowsProof" =>
  v.literalPassiveNormalizedFamily_activeRows_nonempty
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

local notation "originalFrozenPair" =>
  CanonicalLiteralRectangles.Atoms.originalFrozenPairCost
    leftTable rightTable leftAllocation rightAllocation

/-- Primitive occurrence windows suffice for the same already chosen
passive children. The two new divisor norms remain separate. -/
theorem literalPassiveNormalizedFamily_allowance_from_original_atoms
    (cap : ℕ)
    (hcountL : (LC.branch v.2.2.1).slotCount ≤ cap)
    (hcountR : (RC.branch v.2.2.2.1).slotCount ≤ cap)
    (atomBound : ℝ) (hAtomBound : 1 ≤ atomBound)
    (hcostL : ∀ i p, leftAtoms.primeAtomCost i p ≤ atomBound)
    (hcostR : ∀ i p, rightAtoms.primeAtomCost i p ≤ atomBound)
    (hprimeL : leftAtoms.PrimeNormWindow hi)
    (hprimeR : rightAtoms.PrimeNormWindow hi)
    (hslotsL : ∀ i, v.literalLeftParent.reindex.slots i = leftAtoms.slots i)
    (hslotsR : ∀ i, v.literalRightParent.reindex.slots i = rightAtoms.slots i)
    (hfirstL : ∀ r, r = false ∨ leftAtoms.centered = true →
      leftAtoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        hi ^ cap * Z ^ (a.n₁ + a.n₂ + a.z))
    (hfirstR : ∀ r, r = false ∨ rightAtoms.centered = true →
      rightAtoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        hi ^ cap * Z ^ (a.n₁ + a.n₂ + a.z))
    (hgaussL : Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤
      leftAtoms.gaussScale)
    (hgaussR : Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤
      rightAtoms.gaussScale)
    (herrorPos : 0 < error)
    (hannulusThreshold : OriginalPairAllowanceProduction.annulusThreshold hi error ≤ Z)
    (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
    (hsupportError : geometry.supportError ≤ error)
    (hphysicalError : 2 * columnLoss + cutoffExponent ≤ error)
    (firstNormalization : ℝ)
    (hfirstNormalization : firstNormalization =
      firstLeftAllowance Z (geometry.skeleton.A +
        (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E))
        geometry.ideals.first.val geometry.ideals.opposite.val)
    (parentWidth : ℝ) : ∀ analyticLeft analyticRight heightLeft heightRight
      (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ),
      originalFrozenPair *
          (production analyticLeft analyticRight heightLeft heightRight).weight Finset.univ parentWidth b /
          firstNormalization ≤
        ((Γ.index : ℝ) * (profileBound * ‖leftScalar‖ * ‖rightScalar‖) *
          atomBound ^ (3 * cap) * orbitalFieldFactor K) *
          Z ^ (geometry.skeleton.wo + geometry.tag.poolLength step + 5 * error / 3 + mesh) *
            (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
              ((Ideal.absNorm j.1.val : ℝ) *
                (Real.sqrt (Ideal.absNorm (passiveLeft b.val).divisor : ℝ) *
                  Real.sqrt (Ideal.absNorm (passiveRight b.val).divisor : ℝ)) * Z ^ parentWidth) := by
  intro analyticLeft analyticRight heightLeft heightRight b
  let family := production analyticLeft analyticRight heightLeft heightRight
  let anchor := Classical.choice (activeRowsProof analyticLeft analyticRight heightLeft heightRight b)
  let LF := leftFrame b.val
  let RF := rightFrame b.val
  let BL := leftFrozen b.val
  let BR := rightFrozen b.val
  let lc := leftSide analyticLeft analyticRight heightLeft heightRight b.val
  let rc := rightSide analyticLeft analyticRight heightLeft heightRight b.val
  let LL := leftLengths analyticLeft analyticRight heightLeft heightRight b.val
  let LR := rightLengths analyticLeft analyticRight heightLeft heightRight b.val
  let AL := leftAtomsInput analyticLeft analyticRight heightLeft heightRight b.val
  let AR := rightAtomsInput analyticLeft analyticRight heightLeft heightRight b.val
  have hactiveL : ¬ ∀ ξ, LF.source.energy (σ := σ) ξ = 0 :=
    (Finset.mem_filter.mp b.property).2.1
  have hactiveR : ¬ ∀ ξ, RF.source.energy (σ := σ) ξ = 0 :=
    (Finset.mem_filter.mp b.property).2.2
  have hbL : leftAtoms.base = Z := hbaseLeft
  have hbR : rightAtoms.base = Z := hbaseRight
  have hrawL : LL.rawScaleError ≤ error := by
    rw [literalPassiveLeftLengthBinding_rawError]
    have hh := v.literalLeftAtoms_passiveActiveRawError ordinaryRows leftAtoms leftScalar⁻¹
      leftBalance leftTests leftAllocation leftPaid (choice.mask extra) b.val.1.1.val
      .left firstSign b.val.1.2 hactiveL a step (geometry.atBase leftAtoms.base hbL)
      (hsecond.trans v.block.common_left) hi hhi cap hcountL hprimeL hslotsL
      (by simpa only [hbL] using hfirstL) error
      (by simpa only [hbL] using hscaleThreshold)
    simpa only [OriginalNominalGeometry.atBase_skeleton] using hh.le
  have hrawR : LR.rawScaleError ≤ error := by
    rw [literalPassiveRightLengthBinding_rawError]
    have hh := v.literalRightAtoms_passiveActiveRawError ordinaryRows rightAtoms rightScalar⁻¹
      rightBalance rightTests rightAllocation rightPaid (choice.mask extra) b.val.2.1.val
      .right (-firstSign) b.val.2.2 hactiveR a step (geometry.swapSecond.atBase rightAtoms.base hbR)
      (hopposite.trans v.block.common_right) hi hhi cap hcountR hprimeR hslotsR
      (by simpa only [hbR] using hfirstR) error
      (by simpa only [hbR] using hscaleThreshold)
    simpa only [OriginalNominalGeometry.atBase_skeleton] using hh.le
  have hcommonL : ∀ i ∈ Finset.univ \ (originalMass).leftAtoms.keep,
      (originalMass).leftAtoms.annulus i * (originalMass).leftAtoms.profile i ≤ atomBound := by
    intro i _
    change (v.literalLeftOriginal leftAtoms).primeAtomCost i
      (v.literalLeftBranch.witness.2 i) ≤ atomBound
    exact hcostL i _
  have hcommonR : ∀ i ∈ Finset.univ \ (originalMass).rightAtoms.keep,
      (originalMass).rightAtoms.annulus i * (originalMass).rightAtoms.profile i ≤ atomBound := by
    intro i _
    change (v.literalRightOriginal rightAtoms).primeAtomCost i
      (v.literalRightBranch.witness.2 i) ≤ atomBound
    exact hcostR i _
  have hfrozenL : ∀ i ∈ Finset.univ \ LF.source.allocation.keep,
      BL.annulus i * BL.profile i ≤ atomBound := by
    intro i _
    change (leftPassiveTable).primeAtomCost i (LF.allocation.witness.2 i) ≤ atomBound
    exact hcostL (SlotRestriction.index v.literalLeftBranch.keep
      (SlotRestriction.index (leftAllocation).keep i)) _
  have hfrozenR : ∀ i ∈ Finset.univ \ RF.source.allocation.keep,
      BR.annulus i * BR.profile i ≤ atomBound := by
    intro i _
    change (rightPassiveTable).primeAtomCost i (RF.allocation.witness.2 i) ≤ atomBound
    exact hcostR (SlotRestriction.index v.literalRightBranch.keep
      (SlotRestriction.index (rightAllocation).keep i)) _
  have hleftBefore : v.literalLeftBranch.keep.card ≤ cap :=
    (by simpa only [Fintype.card_fin] using
      Finset.card_le_univ v.literalLeftBranch.keep).trans hcountL
  have hrightBefore : v.literalRightBranch.keep.card ≤ cap :=
    (by simpa only [Fintype.card_fin] using
      Finset.card_le_univ v.literalRightBranch.keep).trans hcountR
  have hleftSlots : (leftAllocation).keep.card ≤ cap :=
    (by simpa only [Fintype.card_fin] using
      Finset.card_le_univ (leftAllocation).keep).trans hleftBefore
  have hrightSlots : (rightAllocation).keep.card ≤ cap :=
    (by simpa only [Fintype.card_fin] using
      Finset.card_le_univ (rightAllocation).keep).trans hrightBefore
  have hscaleL : Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤
      LF.normalizationScale := by
    rw [CanonicalLiteralPassiveFrames.frame_normalizationScale]
    change Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤ (leftTable).gaussScale
    simpa only [v.literalLeftStripped_gaussScale] using hgaussL
  have hscaleR : Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤
      RF.normalizationScale := by
    rw [CanonicalLiteralPassiveFrames.frame_normalizationScale]
    change Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤ (rightTable).gaussScale
    simpa only [v.literalRightStripped_gaussScale] using hgaussR
  have hradius : Z ^ (-geometry.skeleton.Krow - geometry.skeleton.g) ≤
      (originalMass).radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (originalMass).mask)).val := by
    change Z ^ (-geometry.skeleton.Krow - geometry.skeleton.g) ≤
      (retainedScale * Z ^ g)⁻¹ * (sIntegerElementNorm K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).val
    rw [sIntegerMaskGenerator_empty_norm, mul_one, ← hretained, ← henlargement]
    exact le_of_eq (geometry.literalInverseRadius domain.scale)
  have hpair := normalized_sixth_pair_original_allowance_independent
    LF RF lc.calibration rc.calibration originalMass BL BR lc.capacity rc.capacity
    lc.amplitude rc.amplitude lc.amplitude_pos rc.amplitude_pos
    lc.bounds rc.bounds lc.bounds_nonneg rc.bounds_nonneg lc.factor rc.factor
    (family.leftChild Finset.univ b) (family.rightChild Finset.univ b)
    parent a Z step geometry (family.left_base b.val) (family.right_base b.val)
    v.block.right_positive anchor hsecond hopposite hunit hnonunit LL LR AL AR
    hstep mesh hmesh hfit
    (eq_of_heq (leftCapacityProof analyticLeft analyticRight heightLeft heightRight b.val anchor))
    (eq_of_heq (rightCapacityProof analyticLeft analyticRight heightLeft heightRight b.val anchor))
    domain.scale cap atomBound hAtomBound rfl rfl hleftSlots hrightSlots hcountL hcountR
    hcommonL hcommonR hfrozenL hfrozenR firstNormalization hfirstNormalization
    hi error herrorPos hannulusThreshold le_rfl le_rfl le_rfl le_rfl hsupportError
    hrawL hrawR
    (by simpa only [literalPassiveLeftLengthBinding_widthError] using hphysicalError)
    (by simpa only [literalPassiveRightLengthBinding_widthError] using hphysicalError)
    hscaleL hscaleR hradius
  change family.weight Finset.univ 0 b / firstNormalization ≤ _ at hpair
  have hleftIdeal : (originalMass).leftIdeal = v.1.val.1 := v.block.common_left
  have hrightIdeal : (originalMass).rightIdeal = v.1.val.2 := v.block.common_right
  simp only [literalOriginalArithmeticMass_fiber, literalOriginalArithmeticMass_profileBound,
    hleftIdeal, hrightIdeal] at hpair
  have hslotOldL : ∀ i ∈ Finset.univ \ (leftAllocation).keep,
      ((Ideal.absNorm ((leftAllocation).witness.2 i).asIdeal : ℝ) /
        (leftTable).base ^ (leftTable).length i) *
          ‖(leftTable).slotWeight i ((leftAllocation).witness.2 i)‖ ^ 2 ≤ atomBound := by
    intro i _
    exact hcostL (SlotRestriction.index v.literalLeftBranch.keep i) _
  have hslotOldR : ∀ i ∈ Finset.univ \ (rightAllocation).keep,
      ((Ideal.absNorm ((rightAllocation).witness.2 i).asIdeal : ℝ) /
        (rightTable).base ^ (rightTable).length i) *
          ‖(rightTable).slotWeight i ((rightAllocation).witness.2 i)‖ ^ 2 ≤ atomBound := by
    intro i _
    exact hcostR (SlotRestriction.index v.literalRightBranch.keep i) _
  have houter : originalFrozenPair ≤ atomBound ^ cap / (Ideal.absNorm j.1.val : ℝ) :=
    CanonicalLiteralRectangles.Atoms.originalFrozenPairCost_le_shared
      leftTable rightTable leftAllocation rightAllocation cap atomBound hAtomBound
      hleftBefore hrightBefore hslotOldL hslotOldR rfl
  have hNpos : 0 < firstNormalization := by
    rw [hfirstNormalization]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans domain.scale) _
  have hweighted := mul_le_mul houter hpair
    (div_nonneg (family.weight_nonneg Finset.univ 0 b (zero_lt_one.trans domain.scale)) hNpos.le)
    (div_nonneg (pow_nonneg (zero_le_one.trans hAtomBound) cap) (Nat.cast_nonneg _))
  have hzero : originalFrozenPair * family.weight Finset.univ 0 b / firstNormalization ≤
      ((Γ.index : ℝ) * (profileBound * ‖leftScalar‖ * ‖rightScalar‖) *
        atomBound ^ (3 * cap) * orbitalFieldFactor K) *
        Z ^ (geometry.skeleton.wo + geometry.tag.poolLength step + 5 * error / 3 + mesh) *
          (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
            ((Ideal.absNorm j.1.val : ℝ) *
              (Real.sqrt (Ideal.absNorm (passiveLeft b.val).divisor : ℝ) *
                Real.sqrt (Ideal.absNorm (passiveRight b.val).divisor : ℝ))) := by
    apply (show originalFrozenPair * family.weight Finset.univ 0 b / firstNormalization =
        originalFrozenPair * (family.weight Finset.univ 0 b / firstNormalization) by ring).le.trans
    apply hweighted.trans_eq
    rw [show 3 * cap = cap + 2 * cap by omega, pow_add]
    ring
  have hpw : family.weight Finset.univ parentWidth b =
      family.weight Finset.univ 0 b / Z ^ parentWidth := by
    simp only [ActualNormalizedPairFamily.weight, normalizedCapacityPairWeight,
      Real.rpow_zero, div_one]
  rw [hpw]
  convert div_le_div_of_nonneg_right hzero (Real.rpow_nonneg
    (zero_lt_one.trans domain.scale).le parentWidth) using 1 <;> ring

local notation "actualAllowance" =>
  v.literalPassiveNormalizedFamily_allowance_from_original_atoms
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

/-- Integral norms of the two actual new divisors are at least one.
This weaker endpoint is convenient for the later original index sum;
it keeps the old shared inverse norm and its third slot cost. -/
theorem literalPassiveNormalizedFamily_allowance_coarse_from_original_atoms
    (cap : ℕ)
    (hcountL : (LC.branch v.2.2.1).slotCount ≤ cap)
    (hcountR : (RC.branch v.2.2.2.1).slotCount ≤ cap)
    (atomBound : ℝ) (hAtomBound : 1 ≤ atomBound)
    (hcostL : ∀ i p, leftAtoms.primeAtomCost i p ≤ atomBound)
    (hcostR : ∀ i p, rightAtoms.primeAtomCost i p ≤ atomBound)
    (hprimeL : leftAtoms.PrimeNormWindow hi)
    (hprimeR : rightAtoms.PrimeNormWindow hi)
    (hslotsL : ∀ i, v.literalLeftParent.reindex.slots i = leftAtoms.slots i)
    (hslotsR : ∀ i, v.literalRightParent.reindex.slots i = rightAtoms.slots i)
    (hfirstL : ∀ r, r = false ∨ leftAtoms.centered = true →
      leftAtoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        hi ^ cap * Z ^ (a.n₁ + a.n₂ + a.z))
    (hfirstR : ∀ r, r = false ∨ rightAtoms.centered = true →
      rightAtoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        hi ^ cap * Z ^ (a.n₁ + a.n₂ + a.z))
    (hgaussL : Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤
      leftAtoms.gaussScale)
    (hgaussR : Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤
      rightAtoms.gaussScale)
    (herrorPos : 0 < error)
    (hannulusThreshold : OriginalPairAllowanceProduction.annulusThreshold hi error ≤ Z)
    (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
    (hsupportError : geometry.supportError ≤ error)
    (hphysicalError : 2 * columnLoss + cutoffExponent ≤ error)
    (firstNormalization : ℝ)
    (hfirstNormalization : firstNormalization =
      firstLeftAllowance Z (geometry.skeleton.A +
        (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E))
        geometry.ideals.first.val geometry.ideals.opposite.val)
    (parentWidth : ℝ) : ∀ analyticLeft analyticRight heightLeft heightRight
      (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ),
      originalFrozenPair *
          (production analyticLeft analyticRight heightLeft heightRight).weight Finset.univ parentWidth b /
          firstNormalization ≤
        ((Γ.index : ℝ) * (profileBound * ‖leftScalar‖ * ‖rightScalar‖) *
          atomBound ^ (3 * cap) * orbitalFieldFactor K) *
          Z ^ (geometry.skeleton.wo + geometry.tag.poolLength step + 5 * error / 3 + mesh) *
            (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
              ((Ideal.absNorm j.1.val : ℝ) * Z ^ parentWidth) := by
  intro analyticLeft analyticRight heightLeft heightRight b
  have h := actualAllowance cap hcountL hcountR atomBound hAtomBound hcostL hcostR
    hprimeL hprimeR hslotsL hslotsR hfirstL hfirstR hgaussL hgaussR herrorPos
    hannulusThreshold hscaleThreshold hsupportError hphysicalError
    firstNormalization hfirstNormalization parentWidth
    analyticLeft analyticRight heightLeft heightRight b
  have hnormL : (1 : ℝ) ≤ (Ideal.absNorm (passiveLeft b.val).divisor : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (leftFrozen b.val).divisor_ne_zero)
  have hnormR : (1 : ℝ) ≤ (Ideal.absNorm (passiveRight b.val).divisor : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (rightFrozen b.val).divisor_ne_zero)
  have hden : (1 : ℝ) ≤
      Real.sqrt (Ideal.absNorm (passiveLeft b.val).divisor : ℝ) *
        Real.sqrt (Ideal.absNorm (passiveRight b.val).divisor : ℝ) :=
    one_le_mul_of_one_le_of_one_le
      (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnormL)
      (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnormR)
  have hfield := orbitalFieldFactor_nonneg K
  have hAtomBound0 : 0 ≤ atomBound := zero_le_one.trans hAtomBound
  have hbound0 : 0 ≤
      ((Γ.index : ℝ) * (profileBound * ‖leftScalar‖ * ‖rightScalar‖) *
        atomBound ^ (3 * cap) * orbitalFieldFactor K) *
        Z ^ (geometry.skeleton.wo + geometry.tag.poolLength step + 5 * error / 3 + mesh) *
          (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
            ((Ideal.absNorm j.1.val : ℝ) * Z ^ parentWidth) := by
    positivity
  apply h.trans
  calc
    _ = (((Γ.index : ℝ) * (profileBound * ‖leftScalar‖ * ‖rightScalar‖) *
        atomBound ^ (3 * cap) * orbitalFieldFactor K) *
        Z ^ (geometry.skeleton.wo + geometry.tag.poolLength step + 5 * error / 3 + mesh) *
          (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
            ((Ideal.absNorm j.1.val : ℝ) * Z ^ parentWidth)) /
              (Real.sqrt (Ideal.absNorm (passiveLeft b.val).divisor : ℝ) *
                Real.sqrt (Ideal.absNorm (passiveRight b.val).divisor : ℝ)) := by ring
    _ ≤ _ := div_le_self hbound0 hden

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_allowance_from_original_atoms

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_allowance_coarse_from_original_atoms
