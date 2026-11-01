import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNormalizedRadii
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralOriginalFrozenCost

/-!
# Kernel mass of the actual independent passive family

The family is produced on the original covered row class. Its two
passive allocations are independent and its children are exactly those
chosen by `literalPassiveNormalizedFamily`. The original two Fourier
kernels remain unchanged.

The earlier shared allocation has its actual witness-based frozen
cost outside the family, once on each side before taking square roots.
Its product is a single outer weight. The two new passive divisors
remain in the exact arithmetic weight sum. Neither a final profile
bound nor a capacity or kernel-mass estimate is an input.

All finite Fourier orders and the kernel constant depend only on the
fixed field, characters, cap and order. The complete radius power is
`(cap + 2) + (cap + 2)`, including every pre-removal profile on both sides.
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

local instance canonicalLiteralPassiveKernelCircleCharacterFintype :
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
local notation "ordinaryRows" => normalizationRows.restrictRows
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

local notation "leftAllocation" => (rectangles.leftFrame C false).allocation
local notation "rightAllocation" => (rectangles.rightFrame C false).allocation
local notation "leftPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => leftRecipe.slots.index (SlotRestriction.index leftAllocation.keep i))
local notation "rightPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => rightRecipe.slots.index (SlotRestriction.index rightAllocation.keep i))

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
local notation "leftParameters" => fun b : Labels =>
  CanonicalLiteralAllocatedData.parameters
    (CanonicalLiteralPassiveSource.table leftTests leftAllocation A leftPaid)
    (passiveLeft b) b.1.2 m q a.κ
local notation "rightParameters" => fun b : Labels =>
  CanonicalLiteralAllocatedData.parameters
    (CanonicalLiteralPassiveSource.table rightTests rightAllocation A rightPaid)
    (passiveRight b) b.2.2 m q a.κ
local notation "leftCoefficient" => fun b : Labels =>
  (leftComputed.passiveTable leftAllocation A leftPaid).coefficient Z (leftParameters b)
    isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign b.1.2
local notation "rightCoefficient" => fun b : Labels =>
  (rightComputed.passiveTable rightAllocation A rightPaid).coefficient Z (rightParameters b)
    isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) b.2.2
local notation "analyticFactor" => CanonicalFullKappaPrime.radiusFactor K Z δ mesh
  (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
  (CompleteMovingRowRecipe.primeMaskLogBound A Z (m + q))

local notation "leftRadiusProof" =>
  v.literalPassiveNormalizedFamily_leftRadius
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

local notation "rightRadiusProof" =>
  v.literalPassiveNormalizedFamily_rightRadius
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

local notation "leftActiveBound" =>
  v.literalPassiveNormalizedFamily_leftActiveCoefficient_le
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

local notation "rightActiveBound" =>
  v.literalPassiveNormalizedFamily_rightActiveCoefficient_le
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

local notation "originalLeaf" => v.leaf exceptional firstKernel x j
local notation "oldFrozenWeight" =>
  Real.sqrt (leftTable.originalFrozenCost leftAllocation) *
    Real.sqrt (rightTable.originalFrozenCost rightAllocation)
local notation "originalOuter" => originalLeaf.weight * oldFrozenWeight

/-- The profile model and first-scale equalities are the literal
constructor projections. The active estimates, two retained-count
bounds and all capacity-radius identities are proved internally for
this actual family. The original allocation cost occurs once. -/
theorem literalPassiveNormalizedFamily_kernelMass
    {leftSeedSlots rightSeedSlots : ℕ}
    (leftSeed : CanonicalLiteralRectangles.Atoms (K := K) leftSeedSlots)
    (rightSeed : CanonicalLiteralRectangles.Atoms (K := K) rightSeedSlots)
    {leftFirstPrimes rightFirstPrimes : Finset (Ideal (𝓞 K))}
    (leftFirst : SupportCartesianBranch leftSeed.plain₁ leftSeed.plain₂ leftSeed.slots leftFirstPrimes)
    (rightFirst : SupportCartesianBranch rightSeed.plain₁ rightSeed.plain₂ rightSeed.slots rightFirstPrimes)
    (δ₁ : ℝ) (hδlo : 0 ≤ δ₁ + δ₂) (hδhi' : δ₁ + δ₂ ≤ 1 / 2)
    (hcomparisonL : leftSeed.centered = true →
      leftSeed.scale₁ true * leftSeed.scale₂ true = leftSeed.scale₁ false * leftSeed.scale₂ false)
    (hcomparisonR : rightSeed.centered = true →
      rightSeed.scale₁ true * rightSeed.scale₂ true = rightSeed.scale₁ false * rightSeed.scale₂ false)
    (hcenteredL : leftTable.centered = leftSeed.centered)
    (hcenteredR : rightTable.centered = rightSeed.centered)
    (hbaseL : (v.literalLeftOriginal leftAtoms).base = leftSeed.base)
    (hbaseR : (v.literalRightOriginal rightAtoms).base = rightSeed.base)
    (hfirstL₁ : ∀ r, (v.literalLeftOriginal leftAtoms).scale₁ r = (leftSeed.extract leftFirst).scale₁ r)
    (hfirstL₂ : ∀ r, (v.literalLeftOriginal leftAtoms).scale₂ r = (leftSeed.extract leftFirst).scale₂ r)
    (hfirstR₁ : ∀ r, (v.literalRightOriginal rightAtoms).scale₁ r = (rightSeed.extract rightFirst).scale₁ r)
    (hfirstR₂ : ∀ r, (v.literalRightOriginal rightAtoms).scale₂ r = (rightSeed.extract rightFirst).scale₂ r)
    (hboundL : leftComputed.bound = fun r => originalBound + originalBound *
      CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ orders *
        (1 + CanonicalLiteralBalancedSchwartz.factor leftSeed leftFirst δ₁ δ₂ r))
    (hboundR : rightComputed.bound = fun r => originalBound + originalBound *
      CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ orders *
        (1 + CanonicalLiteralBalancedSchwartz.factor rightSeed rightFirst δ₁ δ₂ r))
    (hfirstSign : firstSign = 1 ∨ firstSign = -1)
    (cap : ℕ) (hcap : parent.geometry.slotCount ≤ cap) :
    ∀ analyticLeft analyticRight heightLeft heightRight,
    let family := production analyticLeft analyticRight heightLeft heightRight
    let labels := (Finset.univ : Finset Labels)
    let μ := actualNestedLabelMeasure (fun _ : Labels => originalLeaf.firstKernel)
      (fun _ : Labels => originalLeaf.secondKernel) (fun _ : Labels => originalOuter)
    let fixed := CanonicalLiteralActiveRadius.twoSignsCoefficient
      originalBound lo hi hlo δ₁ δ₂ orders
    (∀ rs : family.active labels,
      IsFiniteMeasure (family.kernel labels μ (a.m + a.q) rs)) ∧
      (∑ rs : family.active labels, (family.kernel labels μ (a.m + a.q) rs).real Set.univ) ≤
        CanonicalLiteralKernelConstants.constant K A σ ω ψ cap (orders.sup Prod.snd) *
          (2 * analyticFactor) ^ ((cap + 2) + (cap + 2)) *
            (1 + fixed) ^ ((cap + 2) + (cap + 2)) *
              (CanonicalLiteralKernelConstants.firstOrders K A σ ω ψ cap (orders.sup Prod.snd)).sup
                (schwartzSeminormFamily ℝ ℝ ℂ) originalLeaf.firstKernel *
              (CanonicalLiteralKernelConstants.secondOrders K A σ ω ψ cap (orders.sup Prod.snd)).sup
                (schwartzSeminormFamily ℝ ℝ ℂ) originalLeaf.secondKernel *
                ∑ rs : family.active labels,
                  originalOuter * family.weight labels (a.m + a.q) rs := by
  intro analyticLeft analyticRight heightLeft heightRight
  dsimp only
  let family := production analyticLeft analyticRight heightLeft heightRight
  let L := leftCoefficient
  let R := rightCoefficient
  let factor := analyticFactor
  let fixed := CanonicalLiteralActiveRadius.twoSignsCoefficient originalBound lo hi hlo δ₁ δ₂ orders
  let s₁ := CanonicalLiteralKernelConstants.firstOrders K A σ ω ψ cap (orders.sup Prod.snd)
  let s₂ := CanonicalLiteralKernelConstants.secondOrders K A σ ω ψ cap (orders.sup Prod.snd)
  let S₁ := s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) originalLeaf.firstKernel
  let S₂ := s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) originalLeaf.secondKernel
  have hL (rs : Labels) : 0 ≤ L rs :=
    (leftComputed.passiveTable leftAllocation A leftPaid).coefficient_nonneg Z _ domain.scale.le
      isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign rs.1.2
  have hR (rs : Labels) : 0 ≤ R rs :=
    (rightComputed.passiveTable rightAllocation A rightPaid).coefficient_nonneg Z _ domain.scale.le
      isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) rs.2.2
  have hfactor : 1 ≤ factor := CanonicalFullKappaPrime.one_le_radiusFactor
    (K := K) Z δ mesh (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
    (CompleteMovingRowRecipe.primeMaskLogBound A Z (m + q)) domain.scale.le hδ.le hmesh
  have hB : 0 ≤ originalBound :=
    (show 0 ≤ originalOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (original.leftRep reference time) by positivity).trans
      (original.left_bound reference hreference time htime)
  have hfixed : 0 ≤ fixed := CanonicalLiteralActiveRadius.twoSignsCoefficient_nonneg
    originalBound lo hi hB hlo hhi δ₁ δ₂ orders
  have hS₁ : 0 ≤ S₁ := by positivity
  have hS₂ : 0 ≤ S₂ := by positivity
  have hLfixed (rs : family.active Finset.univ) : L rs.val ≤ fixed :=
    (leftActiveBound leftSeed leftFirst δ₁ hδlo hδhi' hcomparisonL hcenteredL
      hbaseL hfirstL₁ hfirstL₂ hboundL analyticLeft analyticRight heightLeft heightRight rs).trans
      (CanonicalLiteralActiveRadius.fixedCoefficient_le_twoSigns
        originalBound lo hi hlo δ₁ δ₂ firstSign orders hfirstSign)
  have hnegativeSign : -firstSign = 1 ∨ -firstSign = -1 := by
    rcases hfirstSign with h | h
    · right; rw [h]
    · left; rw [h]; norm_num
  have hRfixed (rs : family.active Finset.univ) : R rs.val ≤ fixed :=
    (rightActiveBound rightSeed rightFirst δ₁ hδlo hδhi' hcomparisonR hcenteredR
      hbaseR hfirstR₁ hfirstR₂ hboundR analyticLeft analyticRight heightLeft heightRight rs).trans
      (CanonicalLiteralActiveRadius.fixedCoefficient_le_twoSigns
        originalBound lo hi hlo δ₁ δ₂ (-firstSign) orders hnegativeSign)
  let control := (2 * factor) ^ ((cap + 2) + (cap + 2)) *
    (1 + fixed) ^ ((cap + 2) + (cap + 2)) * S₁ * S₂
  have hprofiles (rs : family.active Finset.univ) :
      pairedProfileEnvelopeConstant (CanonicalFullKappaPrime.enlargedCoefficient (L rs.val) factor)
        (CanonicalFullKappaPrime.enlargedCoefficient (R rs.val) factor) cap cap *
          S₁ * S₂ ≤ control := by
    have he := (CanonicalFullKappaPrime.paired_envelopeConstant_le
      (L rs.val) (R rs.val) factor (hL rs.val) (hR rs.val) hfactor cap cap).trans
      (mul_le_mul_of_nonneg_left
        (CanonicalFullKappaPrime.paired_envelopeConstant_le_bound (L rs.val) (R rs.val) fixed
          (hL rs.val) (hR rs.val) (hLfixed rs) (hRfixed rs) cap cap)
        (pow_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hfactor)) _))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hS₁) hS₂
  have hcapL (rs : Labels) : (family.leftSource rs).allocation.keep.card ≤ cap := by
    let slots := CanonicalLiteralPassiveFrames.tableOriginalSlots
      leftTests leftAllocation A leftPaid parent leftRecipe.slots
    have hf : family.leftSlots rs ≤ parent.geometry.slotCount := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective slots.index slots.index.injective
    have hk : (family.leftSource rs).allocation.keep.card ≤ family.leftSlots rs := by
      simpa only [Fintype.card_fin] using
        Finset.card_le_univ (family.leftSource rs).allocation.keep
    exact hk.trans (hf.trans hcap)
  have hcapR (rs : Labels) : (family.rightSource rs).allocation.keep.card ≤ cap := by
    let slots := CanonicalLiteralPassiveFrames.tableOriginalSlots
      rightTests rightAllocation A rightPaid parent rightRecipe.slots
    have hf : family.rightSlots rs ≤ parent.geometry.slotCount := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective slots.index slots.index.injective
    have hk : (family.rightSource rs).allocation.keep.card ≤ family.rightSlots rs := by
      simpa only [Fintype.card_fin] using
        Finset.card_le_univ (family.rightSource rs).allocation.keep
    exact hk.trans (hf.trans hcap)
  have houter : 0 ≤ originalOuter := mul_nonneg originalLeaf.weight_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hm := (actual_finite_normalized_kernel_mass_active
    (F := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := ℝ) (E := ℝ)
    cap (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd))
      .choose_spec.choose_spec.choose_spec.2
  have hout := hm Z hZ family Finset.univ
    (fun _ : Labels => originalLeaf.firstKernel) (fun _ : Labels => originalLeaf.secondKernel)
    (fun _ : Labels => originalOuter)
    (fun rs => CanonicalFullKappaPrime.enlargedCoefficient (L rs) factor)
    (fun rs => CanonicalFullKappaPrime.enlargedCoefficient (R rs) factor)
    (a.m + a.q) control (fun _ _ => houter)
    (fun rs _ => CanonicalFullKappaPrime.enlargedCoefficient_nonneg
      (hL rs) (zero_le_one.trans hfactor))
    (fun rs _ => CanonicalFullKappaPrime.enlargedCoefficient_nonneg
      (hR rs) (zero_le_one.trans hfactor))
    (fun rs _ => hcapL rs) (fun rs _ => hcapR rs)
    (fun rs _ z => leftRadiusProof analyticLeft analyticRight heightLeft heightRight rs z)
    (fun rs _ z => rightRadiusProof analyticLeft analyticRight heightLeft heightRight rs z)
    hprofiles
  refine ⟨hout.1, hout.2.trans_eq ?_⟩
  dsimp only [control, S₁, S₂, s₁, s₂, CanonicalLiteralKernelConstants.constant]
  ring

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_kernelMass
