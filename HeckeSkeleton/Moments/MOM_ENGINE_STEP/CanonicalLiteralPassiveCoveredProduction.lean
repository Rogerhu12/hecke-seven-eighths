import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormalizedLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSideProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNormalizedFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyBase

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

/-- Each side is constructed on the same physical ordinary row class.
No finished side normalization is an input to this producer. -/
def literalPassiveNormalizedFamily :=
  have hp : v.chart.NonunitLabelStable :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  have hs : v.chart.SectorLabelStable P :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_sectorLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  have hmaskL : (v.literalLeftOriginal leftAtoms).characters.MaskIndicator := by
    change (v.literalLeftAtoms leftAtoms).characters.MaskIndicator
    rw [leftRecipe.characters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra leftRecipe.slots.index
  have hmaskR : (v.literalRightOriginal rightAtoms).characters.MaskIndicator := by
    change (v.literalRightAtoms rightAtoms).characters.MaskIndicator
    rw [rightRecipe.characters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra rightRecipe.slots.index
  let mass := ((v.literalSupportedRowMass leftAtoms rightAtoms hmaskL hmaskR hp
    profileBound hprofileBound hprofile).withColumnConstants leftScalar rightScalar).restrictRows
      (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
  have hordinary : (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h) =
      fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).literalCharacter C P Rchar F
        oldMoving correction pattern sector h ∉ parent.theta := by
    rw [hexceptional]
  have hk : geometry.skeleton.Krow = Real.log retainedScale / Real.log Z := by
    change Real.log geometry.retainedScale / Real.log Z = _
    rw [hretained]
  have hg : geometry.skeleton.g = g := henlargement
  have hw := geometry.literalParameters_secondWidth columnLoss cutoffExponent rootLength
  rw [hk, hg, hsecond, hopposite, hunit, hnonunit] at hw
  let leftGeometry := geometry.atBase leftTable.base hbaseLeft
  let rightGeometry := geometry.swapSecond.atBase rightTable.base hbaseRight
  have hpaidCutoff : 0 ≤ paidCutoff := by positivity
  have hlm : leftGeometry.literalRowParameter paidCutoff = m :=
    geometry.atBase_literalRowParameter leftTable.base hbaseLeft paidCutoff
  have hrm : rightGeometry.literalRowParameter paidCutoff = m := by
    rw [OriginalNominalGeometry.atBase_literalRowParameter,
      geometry.swapSecond_literalRowParameter]
  have hrootL : idealLogLength leftTable.base
      (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity
        v.block.rightMultiplicity).val = rootLength := by rw [hbaseLeft]
  have hrootR : idealLogLength rightTable.base
      (secondSixthRootIdeal v.block.primes v.block.rightMultiplicity
        v.block.leftMultiplicity).val = rootLength := by
    have he : secondSixthRootIdeal v.block.primes v.block.rightMultiplicity
        v.block.leftMultiplicity =
        secondSixthRootIdeal v.block.primes v.block.leftMultiplicity
          v.block.rightMultiplicity := by
      unfold secondSixthRootIdeal
      apply congrArg (primePowerProduct v.block.primes)
      funext i
      rw [min_comm]
    rw [he, hbaseRight]
  have hlq : leftGeometry.literalSupportParameter (idealLogLength leftTable.base
      (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity
        v.block.rightMultiplicity).val) = q := by
    rw [hrootL]
    exact geometry.atBase_literalSupportParameter leftTable.base hbaseLeft rootLength
  have hrq : rightGeometry.literalSupportParameter (idealLogLength rightTable.base
      (secondSixthRootIdeal v.block.primes v.block.rightMultiplicity
        v.block.leftMultiplicity).val) = q := by
    rw [hrootR, OriginalNominalGeometry.atBase_literalSupportParameter,
      geometry.swapSecond_literalSupportParameter]
  have hunitR : rightGeometry.ideals.unitPart.val =
      (secondPatternUnitIdeal v.block.primes v.block.rightMultiplicity
        v.block.leftMultiplicity pattern).val := by
    rw [secondPatternUnitIdeal_swap]
    exact hunit
  have hdomainL : PairedEngineDomain centered parent a leftTable.base Y₁ Y₂ floor padding := by
    simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
      CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using domain
  have hdomainR : PairedEngineDomain centered parent a rightTable.base Y₁ Y₂ floor padding := by
    simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
      CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using domain
  let leftProducer := fun (aL : CanonicalLiteralPassiveNonzero.nonzeroLabels leftTests
      leftAllocation A (choice.mask extra)) (r : Bool) =>
    v.chart.literalPassiveSideNormalization
      (P := P) (Rchar := Rchar) (hclass := hp) (hsector := hs)
      (X := cutoff) (hX := hcutoff) (label := v.rowLabel)
      (weight := ((v.literalRows leftAtoms rightAtoms).withColumnConstants
        leftScalar rightScalar).weight)
      (keep₁ := fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).correlation h ≠ 0)
      (keep₂ := fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
      (rowMass := mass) (d := leftTable) (W := leftTests) (B := leftAllocation)
      (F := F) (choice := choice) (parent := parent) (oldMoving := oldMoving)
      (correction := correction) (hcorr := hcorr) (remaining := remaining) (extra := extra)
      (slots := leftRecipe.slots) (a := aL.val) (ha := aL.property)
      (retainedScale := retainedScale) (g := g)
      (a₀ := geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss)
      (oldq := geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E)
      (wo := geometry.skeleton.wo) (cutoffExponent := cutoffExponent) (hscale := hscale)
      (hradius := by
        change _ = CanonicalRowBall.gaussRadius retainedScale leftTable.base g hscale _
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
      (m := m) (q := q) (κ := a.κ)
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
  let rightProducer := fun (aR : CanonicalLiteralPassiveNonzero.nonzeroLabels rightTests
      rightAllocation A (choice.mask extra)) (r : Bool) =>
    v.chart.literalPassiveSideNormalization
      (P := P) (Rchar := Rchar) (hclass := hp) (hsector := hs)
      (X := cutoff) (hX := hcutoff) (label := v.rowLabel)
      (weight := ((v.literalRows leftAtoms rightAtoms).withColumnConstants
        leftScalar rightScalar).weight)
      (keep₁ := fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).correlation h ≠ 0)
      (keep₂ := fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
      (rowMass := mass) (d := rightTable) (W := rightTests) (B := rightAllocation)
      (F := F) (choice := choice) (parent := parent) (oldMoving := oldMoving)
      (correction := correction) (hcorr := hcorr) (remaining := remaining) (extra := extra)
      (slots := rightRecipe.slots) (a := aR.val) (ha := aR.property)
      (retainedScale := retainedScale) (g := g)
      (a₀ := geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss)
      (oldq := geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E)
      (wo := geometry.skeleton.wo) (cutoffExponent := cutoffExponent) (hscale := hscale)
      (hradius := by
        change _ = CanonicalRowBall.gaussRadius retainedScale rightTable.base g hscale _
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
      (m := m) (q := q) (κ := a.κ)
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
  fun analyticLeft analyticRight heightLeft heightRight =>
    let result := CanonicalLiteralPassiveNormalizedFamily.family C ordinaryRows leftTests rightTests
      leftAllocation rightAllocation leftPaid rightPaid (choice.mask extra) (choice.mask extra)
      firstSign (-firstSign)
      (fun b => leftProducer b.1 b.2 (analyticLeft b.1 b.2) (heightLeft b.1 b.2))
      (fun b => rightProducer b.1 b.2 (analyticRight b.1 b.2) (heightRight b.1 b.2))
      (hbaseRight.trans hbaseLeft.symm)
    result.atBase Z hbaseLeft

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily
