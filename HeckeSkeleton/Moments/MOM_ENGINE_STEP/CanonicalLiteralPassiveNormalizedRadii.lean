import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveCoveredProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSideRadii
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveActiveRadius
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveActivity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralKernelConstants

/-!
# The radii of the actual covered passive family

The family here is the output of the original covered-row producer,
including its exact change-of-base proof. Its left and right passive
labels are independent. All calibrations, capacities, children and
computed profile coefficients are the ones already constructed there.

The active coefficient estimate uses a nonzero member of that same
new passive source. The three real plain divisors remain in the scale
identity, and the ordinary comparison rectangle is excluded using its
own zero energy. Cancellation before passive decomposition is not
used to infer activity of any branch.
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

local instance canonicalLiteralPassiveRadiiCircleCharacterFintype :
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

@[simp] theorem literalPassiveNormalizedFamily_leftParameters :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      ((production analyticLeft analyticRight heightLeft heightRight).leftCalibration b).parameters =
        leftParameters b := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveNormalizedFamily_rightParameters :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels),
      ((production analyticLeft analyticRight heightLeft heightRight).rightCalibration b).parameters =
        rightParameters b := by
  intro analyticLeft analyticRight heightLeft heightRight b
  rfl

@[simp] theorem literalPassiveNormalizedFamily_leftRadius :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels) (z : ℝ × ℝ),
      ((production analyticLeft analyticRight heightLeft heightRight).leftCapacity b).radius
          (WithLp.toLp 2 z) =
        polynomialProfileRadius
          (CanonicalFullKappaPrime.enlargedCoefficient (leftCoefficient b) analyticFactor)
          (orders.sup Prod.snd) (orders.sup Prod.snd) z := by
  intro analyticLeft analyticRight heightLeft heightRight b z
  let GL := geometry.atBase leftTable.base hbaseLeft
  have hmL : GL.literalRowParameter paidCutoff = m :=
    geometry.atBase_literalRowParameter leftTable.base hbaseLeft paidCutoff
  have hrootL : idealLogLength leftTable.base
      (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.leftMultiplicity
        ordinaryRows.rightMultiplicity).val = rootLength := by
    change idealLogLength (v.literalLeftAtoms leftAtoms).base
      (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity).val = _
    rw [hbaseLeft]
  have hqL : GL.literalSupportParameter
      (idealLogLength leftTable.base
        (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.leftMultiplicity
          ordinaryRows.rightMultiplicity).val) = q := by
    rw [hrootL]
    exact geometry.atBase_literalSupportParameter leftTable.base hbaseLeft rootLength
  change polynomialProfileRadius
    (CanonicalFullKappaPrime.enlargedCoefficient
      ((leftComputed.passiveTable leftAllocation A leftPaid).coefficient leftTable.base
        (leftParameters b) isCompact_Icc
        (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign b.1.2)
      (CanonicalFullKappaPrime.radiusFactor K leftTable.base δ mesh
        (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
        (CompleteMovingRowRecipe.primeMaskLogBound A leftTable.base
          (GL.literalRowParameter paidCutoff + GL.literalSupportParameter
            (idealLogLength leftTable.base
              (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.leftMultiplicity
                ordinaryRows.rightMultiplicity).val)))))
    (orders.sup Prod.snd) (orders.sup Prod.snd) z = _
  rw [hmL, hqL]
  have hb : leftTable.base = Z := hbaseLeft
  rw [hb]

@[simp] theorem literalPassiveNormalizedFamily_rightRadius :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels) (z : ℝ × ℝ),
      ((production analyticLeft analyticRight heightLeft heightRight).rightCapacity b).radius
          (WithLp.toLp 2 z) =
        polynomialProfileRadius
          (CanonicalFullKappaPrime.enlargedCoefficient (rightCoefficient b) analyticFactor)
          (orders.sup Prod.snd) (orders.sup Prod.snd) z := by
  intro analyticLeft analyticRight heightLeft heightRight b z
  let GR := geometry.swapSecond.atBase rightTable.base hbaseRight
  have hmR : GR.literalRowParameter paidCutoff = m := by
    rw [OriginalNominalGeometry.atBase_literalRowParameter,
      geometry.swapSecond_literalRowParameter]
  have hrootR : idealLogLength rightTable.base
      (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.rightMultiplicity
        ordinaryRows.leftMultiplicity).val = rootLength := by
    have he := SecondColumnSide.literal_root .right ordinaryRows
    change secondSixthRootIdeal ordinaryRows.primes ordinaryRows.rightMultiplicity
      ordinaryRows.leftMultiplicity = secondSixthRootIdeal ordinaryRows.primes
      ordinaryRows.leftMultiplicity ordinaryRows.rightMultiplicity at he
    rw [he]
    change idealLogLength (v.literalRightAtoms rightAtoms).base
      (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity).val = _
    rw [hbaseRight]
  have hqR : GR.literalSupportParameter
      (idealLogLength rightTable.base
        (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.rightMultiplicity
          ordinaryRows.leftMultiplicity).val) = q := by
    rw [hrootR, OriginalNominalGeometry.atBase_literalSupportParameter,
      geometry.swapSecond_literalSupportParameter]
  change polynomialProfileRadius
    (CanonicalFullKappaPrime.enlargedCoefficient
      ((rightComputed.passiveTable rightAllocation A rightPaid).coefficient rightTable.base
        (rightParameters b) isCompact_Icc
        (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) b.2.2)
      (CanonicalFullKappaPrime.radiusFactor K rightTable.base δ mesh
        (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
        (CompleteMovingRowRecipe.primeMaskLogBound A rightTable.base
          (GR.literalRowParameter paidCutoff + GR.literalSupportParameter
            (idealLogLength rightTable.base
              (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.rightMultiplicity
                ordinaryRows.leftMultiplicity).val)))))
    (orders.sup Prod.snd) (orders.sup Prod.snd) z = _
  rw [hmR, hqR]
  have hb : rightTable.base = Z := hbaseRight
  rw [hb]

@[simp] theorem literalPassiveNormalizedFamily_leftPrimeBound :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels)
      (i : Fin (passiveLeft b).keep.card),
      ((production analyticLeft analyticRight heightLeft heightRight).leftCapacity b).primeBound i = 1 := by
  intro analyticLeft analyticRight heightLeft heightRight b i
  rfl

@[simp] theorem literalPassiveNormalizedFamily_rightPrimeBound :
    ∀ analyticLeft analyticRight heightLeft heightRight (b : Labels)
      (i : Fin (passiveRight b).keep.card),
      ((production analyticLeft analyticRight heightLeft heightRight).rightCapacity b).primeBound i = 1 := by
  intro analyticLeft analyticRight heightLeft heightRight b i
  rfl

/-- The active witness is taken after passive decomposition and from
this exact left calibration. Its comparison scale is used only when
that comparison rectangle is present. -/
theorem literalPassiveNormalizedFamily_leftActiveCoefficient_le
    {seedSlots : ℕ} (seed : CanonicalLiteralRectangles.Atoms (K := K) seedSlots)
    {firstPrimes : Finset (Ideal (𝓞 K))}
    (first : SupportCartesianBranch seed.plain₁ seed.plain₂ seed.slots firstPrimes)
    (δ₁ : ℝ) (hδlo : 0 ≤ δ₁ + δ₂) (hδhi' : δ₁ + δ₂ ≤ 1 / 2)
    (hcomparison : seed.centered = true →
      seed.scale₁ true * seed.scale₂ true = seed.scale₁ false * seed.scale₂ false)
    (hcentered : leftTable.centered = seed.centered)
    (hbase : (v.literalLeftOriginal leftAtoms).base = seed.base)
    (hfirst₁ : ∀ r, (v.literalLeftOriginal leftAtoms).scale₁ r = (seed.extract first).scale₁ r)
    (hfirst₂ : ∀ r, (v.literalLeftOriginal leftAtoms).scale₂ r = (seed.extract first).scale₂ r)
    (hbound : leftComputed.bound = fun r => originalBound + originalBound *
      CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ orders *
        (1 + CanonicalLiteralBalancedSchwartz.factor seed first δ₁ δ₂ r)) :
    ∀ analyticLeft analyticRight heightLeft heightRight,
    ∀ rs : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ,
      leftCoefficient rs.val ≤
        CanonicalLiteralRadiusBound.fixedCoefficient originalBound lo hi hlo δ₁ δ₂ firstSign orders := by
  intro analyticLeft analyticRight heightLeft heightRight rs
  let family := production analyticLeft analyticRight heightLeft heightRight
  have hactive : ¬ ∀ ξ, (CanonicalLiteralPassiveFrames.frame leftTests leftAllocation A leftPaid
      C ordinaryRows .left (choice.mask extra) rs.val.1.1.val firstSign rs.val.1.2).source.energy
        (σ := σ) ξ = 0 := (Finset.mem_filter.mp rs.property).2.1
  have hwhich := CanonicalLiteralPassiveFrames.active_rectangle leftTests leftAllocation A leftPaid
    C ordinaryRows .left (choice.mask extra) rs.val.1.1.val firstSign rs.val.1.2 hactive
  have hproduct : seed.scale₁ rs.val.1.2 * seed.scale₂ rs.val.1.2 =
      seed.scale₁ false * seed.scale₂ false := by
    rcases hwhich with hr | hc
    · rw [hr]
    · cases hr : rs.val.1.2 with
      | false => simp only [hr]
      | true => simpa only [hr] using hcomparison (hcentered.symm.trans hc)
  have hB : 0 ≤ originalBound :=
    (show 0 ≤ originalOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (original.leftRep reference time) by positivity).trans
      (original.left_bound reference hreference time htime)
  have hf := CanonicalLiteralPassiveActiveRadius.coefficient_le_fixed_of_source_active
    seed first (v.literalLeftOriginal leftAtoms) v.literalLeftBranch
    v.literalLeftResidualAtlas rfl leftScalar⁻¹ leftBalance leftTests leftAllocation leftPaid
    (choice.mask extra) rs.val.1.1.val leftComputed rs.val.1.2 m q a.κ δ₁ δ₂ firstSign false
    hB hlo hhi hδlo hδhi' hproduct hbase (hfirst₁ rs.val.1.2) (hfirst₂ rs.val.1.2)
    (congrFun hbound rs.val.1.2)
    (family.leftSource rs.val) (family.leftCalibration rs.val)
    hbase rfl (fun _ => rfl) (fun _ => rfl) hactive
  have hb : (family.leftSource rs.val).base = Z := hbaseLeft
  simpa only [hb] using hf

/-- The right source uses its own independent passive allocation and
the unchanged negative Fourier orientation. -/
theorem literalPassiveNormalizedFamily_rightActiveCoefficient_le
    {seedSlots : ℕ} (seed : CanonicalLiteralRectangles.Atoms (K := K) seedSlots)
    {firstPrimes : Finset (Ideal (𝓞 K))}
    (first : SupportCartesianBranch seed.plain₁ seed.plain₂ seed.slots firstPrimes)
    (δ₁ : ℝ) (hδlo : 0 ≤ δ₁ + δ₂) (hδhi' : δ₁ + δ₂ ≤ 1 / 2)
    (hcomparison : seed.centered = true →
      seed.scale₁ true * seed.scale₂ true = seed.scale₁ false * seed.scale₂ false)
    (hcentered : rightTable.centered = seed.centered)
    (hbase : (v.literalRightOriginal rightAtoms).base = seed.base)
    (hfirst₁ : ∀ r, (v.literalRightOriginal rightAtoms).scale₁ r = (seed.extract first).scale₁ r)
    (hfirst₂ : ∀ r, (v.literalRightOriginal rightAtoms).scale₂ r = (seed.extract first).scale₂ r)
    (hbound : rightComputed.bound = fun r => originalBound + originalBound *
      CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ orders *
        (1 + CanonicalLiteralBalancedSchwartz.factor seed first δ₁ δ₂ r)) :
    ∀ analyticLeft analyticRight heightLeft heightRight,
    ∀ rs : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ,
      rightCoefficient rs.val ≤
        CanonicalLiteralRadiusBound.fixedCoefficient originalBound lo hi hlo δ₁ δ₂ (-firstSign) orders := by
  intro analyticLeft analyticRight heightLeft heightRight rs
  let family := production analyticLeft analyticRight heightLeft heightRight
  have hactive : ¬ ∀ ξ, (CanonicalLiteralPassiveFrames.frame rightTests rightAllocation A rightPaid
      C ordinaryRows .right (choice.mask extra) rs.val.2.1.val (-firstSign) rs.val.2.2).source.energy
        (σ := σ) ξ = 0 := (Finset.mem_filter.mp rs.property).2.2
  have hwhich := CanonicalLiteralPassiveFrames.active_rectangle rightTests rightAllocation A rightPaid
    C ordinaryRows .right (choice.mask extra) rs.val.2.1.val (-firstSign) rs.val.2.2 hactive
  have hproduct : seed.scale₁ rs.val.2.2 * seed.scale₂ rs.val.2.2 =
      seed.scale₁ false * seed.scale₂ false := by
    rcases hwhich with hr | hc
    · rw [hr]
    · cases hr : rs.val.2.2 with
      | false => simp only [hr]
      | true => simpa only [hr] using hcomparison (hcentered.symm.trans hc)
  have hB : 0 ≤ originalBound :=
    (show 0 ≤ originalOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (original.leftRep reference time) by positivity).trans
      (original.left_bound reference hreference time htime)
  have hf := CanonicalLiteralPassiveActiveRadius.coefficient_le_fixed_of_source_active
    seed first (v.literalRightOriginal rightAtoms) v.literalRightBranch
    v.literalRightResidualAtlas rfl rightScalar⁻¹ rightBalance rightTests rightAllocation rightPaid
    (choice.mask extra) rs.val.2.1.val rightComputed rs.val.2.2 m q a.κ δ₁ δ₂ (-firstSign) true
    hB hlo hhi hδlo hδhi' hproduct hbase (hfirst₁ rs.val.2.2) (hfirst₂ rs.val.2.2)
    (congrFun hbound rs.val.2.2)
    (family.rightSource rs.val) (family.rightCalibration rs.val)
    hbase rfl (fun _ => rfl) (fun _ => rfl) hactive
  have hb : (family.rightSource rs.val).base = Z := hbaseRight
  simpa only [hb] using hf

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_leftParameters
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_rightParameters
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_leftRadius
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_rightRadius
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_leftPrimeBound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_rightPrimeBound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_leftActiveCoefficient_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_rightActiveCoefficient_le
