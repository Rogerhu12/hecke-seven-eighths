import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSideProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSideProductionAll
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStrippedCovered
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalPairAllowance

/-!
# The actual covered literal leaf produces its normalization data

The original source constructors supply the atom tables, original-slot
recipes, original profile certificates and exact constant extraction.
This assembly calculates the common row/support endpoint parameters,
calibrates the same four rectangles and constructs both normalized
sides from the original finite seminorm and single-character inputs.

The complete root and the physical column/cutoff errors remain in the
chosen parameters. The right capacity dictionary uses the swapped
second common ideals; its source, rows and two kernels stay original.
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

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

theorem atBase_literalRowParameter (base : ℝ) (hbase : base = Z) (cutoff : ℝ) :
    (G.atBase base hbase).literalRowParameter cutoff = G.literalRowParameter cutoff := by
  subst base
  rfl

theorem atBase_literalSupportParameter (base : ℝ) (hbase : base = Z) (root : ℝ) :
    (G.atBase base hbase).literalSupportParameter root = G.literalSupportParameter root := by
  subst base
  rfl

theorem swapSecond_literalRowParameter (cutoff : ℝ) :
    G.swapSecond.literalRowParameter cutoff = G.literalRowParameter cutoff := by
  simp only [literalRowParameter, frequencyCenter, G.swapSecond_skeleton]

theorem swapSecond_literalSupportParameter (root : ℝ) :
    G.swapSecond.literalSupportParameter root = G.literalSupportParameter root := by
  simp only [literalSupportParameter, supportCenter, G.swapSecond_skeleton]

end OriginalNominalGeometry

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

local instance canonicalLiteralNormalizedLeafCircleCharacterFintype :
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
variable (hold : A.exteriorNorm ((F.moving P Rchar oldMoving).effectiveFullSupport
  (remaining * extra)) ≤
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

/-- The actual endpoint parameters are chosen here. The calibration
uses the proved physical window, including the original column loss,
and the original complete moving-support norm window. -/
def computedLiteralCalibrations :
    (∀ r : Bool, ((rectangles).leftFrame C r).source.Calibration (σ := σ) ω ψ) ×
    (∀ r : Bool, ((rectangles).rightFrame C r).source.Calibration (σ := σ) ω ψ) := by
  have hk : geometry.skeleton.Krow = Real.log retainedScale / Real.log Z := by
    change Real.log geometry.retainedScale / Real.log Z = _
    rw [hretained]
  have hg : geometry.skeleton.g = g := henlargement
  have hw := geometry.literalParameters_secondWidth columnLoss cutoffExponent rootLength
  rw [hk, hg, hsecond, hopposite, hunit, hnonunit] at hw
  exact v.literalStrippedCoveredCalibrationsActive P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g
    hscale hZ cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe.slots.index
    rightRecipe.slots.index leftRecipe.characters rightRecipe.characters profileBound hprofileBound
    hprofile (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss)
    (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E) geometry.skeleton.wo
    cutoffExponent hcutoffPower hactiveColumns hold m q a.κ hw
    (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
    hone hroot hemb hbackground hslot hexceptional

local notation "calibrations" =>
  v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional

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

/-- Both side normalizations are constructed on the original stored
leaf before the ordinary activity test. The logarithmic raw error is
computed from each actual rectangle; on an active source the original
scale calculation identifies it with the preselected small error.
Thus an absent ordinary comparison rectangle imposes no condition on
its otherwise unused comparison scales.

`X`, `binding`, the recipes and computed profile values in this internal
assembly are the outputs of the original literal source constructors.
No normalized side, finished profile window, width bound or final
ordinary source inequality is an input. -/
def literalNormalizationData
    (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
    (binding : X.leaf.OrdinaryBinding rectangles)
    (analyticLeft : ∀ r : Bool, ∀ _hκ : (calibrations.1 r).parameters.κ < 1, ∀ ξ,
      ∀ u, u ∈ pairedRows ((calibrations.1 r).data ξ) (calibrations.1 r).parameters
        ((rectangles).leftFrame C r).source.base →
      ∀ i : Fin ((rectangles).leftFrame C r).source.allocation.keep.card,
        ZeroFreeData (heckeContinuation K (((calibrations.1 r).data ξ).rowCharacter u *
          ((calibrations.1 r).data ξ).slotCoefficient
            (lengthSlot ((calibrations.1 r).data ξ)
              ((rectangles).leftFrame C r).source.allocation.keep.card
              ((calibrations.1 r).count ξ) i))) (((calibrations.1 r).parameters.κ + 1) / 2))
    (analyticRight : ∀ r : Bool, ∀ _hκ : (calibrations.2 r).parameters.κ < 1, ∀ ξ,
      ∀ u, u ∈ pairedRows ((calibrations.2 r).data ξ) (calibrations.2 r).parameters
        ((rectangles).rightFrame C r).source.base →
      ∀ i : Fin ((rectangles).rightFrame C r).source.allocation.keep.card,
        ZeroFreeData (heckeContinuation K (((calibrations.2 r).data ξ).rowCharacter u *
          ((calibrations.2 r).data ξ).slotCoefficient
            (lengthSlot ((calibrations.2 r).data ξ)
              ((rectangles).rightFrame C r).source.allocation.keep.card
              ((calibrations.2 r).count ξ) i))) (((calibrations.2 r).parameters.κ + 1) / 2))
    (hanalyticLeft : ∀ r : Bool, ∀ hκ : (calibrations.1 r).parameters.κ < 1, ∀ ξ,
      ∀ u, ∀ hu : u ∈ pairedRows ((calibrations.1 r).data ξ) (calibrations.1 r).parameters
        ((rectangles).leftFrame C r).source.base,
      ∀ i : Fin ((rectangles).leftFrame C r).source.allocation.keep.card,
        heightConstant (analyticLeft r hκ ξ u hu i) +
          3 * ((analyticLeft r hκ ξ u hu i).k : ℝ) ≤ analyticHeight)
    (hanalyticRight : ∀ r : Bool, ∀ hκ : (calibrations.2 r).parameters.κ < 1, ∀ ξ,
      ∀ u, ∀ hu : u ∈ pairedRows ((calibrations.2 r).data ξ) (calibrations.2 r).parameters
        ((rectangles).rightFrame C r).source.base,
      ∀ i : Fin ((rectangles).rightFrame C r).source.allocation.keep.card,
        heightConstant (analyticRight r hκ ξ u hu i) +
          3 * ((analyticRight r hκ ξ u hu i).k : ℝ) ≤ analyticHeight) :
    X.leaf.NormalizationData (ι := Fin v.block.primeCount) C PUnit.{1} ω ψ Z
      Set.univ Set.univ (Set.Icc 0 hi) orders := by
  let cals := calibrations
  let leftGeometry := geometry.atBase (leftTable).base hbaseLeft
  let rightGeometry := geometry.swapSecond.atBase (rightTable).base hbaseRight
  have hpaid : 0 ≤ paidCutoff := by positivity
  have hlm : leftGeometry.literalRowParameter paidCutoff = m :=
    geometry.atBase_literalRowParameter (leftTable).base hbaseLeft paidCutoff
  have hrm : rightGeometry.literalRowParameter paidCutoff = m := by
    rw [OriginalNominalGeometry.atBase_literalRowParameter,
      geometry.swapSecond_literalRowParameter]
  have hrootL : idealLogLength (leftTable).base
      (secondSixthRootIdeal (ordinaryRows).primes
        (SecondColumnSide.left.literalMultiplicity ordinaryRows)
        (SecondColumnSide.left.literalOppositeMultiplicity ordinaryRows)).val = rootLength := by
    change idealLogLength (v.literalLeftAtoms leftAtoms).base
      (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity).val = _
    rw [hbaseLeft]
  have hrootR : idealLogLength (rightTable).base
      (secondSixthRootIdeal (ordinaryRows).primes
        (SecondColumnSide.right.literalMultiplicity ordinaryRows)
        (SecondColumnSide.right.literalOppositeMultiplicity ordinaryRows)).val = rootLength := by
    rw [SecondColumnSide.literal_root]
    change idealLogLength (v.literalRightAtoms rightAtoms).base
      (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity).val = _
    rw [hbaseRight]
  have hlq : leftGeometry.literalSupportParameter
      (idealLogLength (leftTable).base
        (secondSixthRootIdeal (ordinaryRows).primes
          (SecondColumnSide.left.literalMultiplicity ordinaryRows)
          (SecondColumnSide.left.literalOppositeMultiplicity ordinaryRows)).val) = q := by
    rw [hrootL]
    exact geometry.atBase_literalSupportParameter (leftTable).base hbaseLeft rootLength
  have hrq : rightGeometry.literalSupportParameter
      (idealLogLength (rightTable).base
        (secondSixthRootIdeal (ordinaryRows).primes
          (SecondColumnSide.right.literalMultiplicity ordinaryRows)
          (SecondColumnSide.right.literalOppositeMultiplicity ordinaryRows)).val) = q := by
    rw [hrootR, OriginalNominalGeometry.atBase_literalSupportParameter,
      geometry.swapSecond_literalSupportParameter]
  have hdomainL : PairedEngineDomain centered parent a (leftTable).base Y₁ Y₂ floor padding := by
    simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
      CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using domain
  have hdomainR : PairedEngineDomain centered parent a (rightTable).base Y₁ Y₂ floor padding := by
    simpa only [CanonicalLiteralRectangles.Atoms.balancePlain,
      CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using domain
  have hunitR : rightGeometry.ideals.unitPart.val =
      (secondPatternUnitIdeal (ordinaryRows).primes (ordinaryRows).rightMultiplicity
        (ordinaryRows).leftMultiplicity pattern).val := by
    rw [secondPatternUnitIdeal_swap]
    exact hunit
  let left : ∀ r : Bool, SecondSideNormalization ((rectangles).leftFrame C r)
      ω ψ Set.univ Set.univ (Set.Icc 0 hi) orders := fun r =>
    (leftTable).produceLiteralSideAll leftTests ordinaryRows .left j.2.1
      (fun i => v.block.leftResidual (v.leftReindex.index i)) v.leftReindex.ideal_product
      firstSign r j.1.val j.2.2.1.val (Finset.mem_filter.mp (allocation).property).2.2.1
      (cals.1 r) P Rchar F parent oldMoving correction hcorr remaining extra a step leftGeometry
      pattern sector leftRecipe.slots paidCutoff reference time
      (by intro ξ; rw [hlm, hlq]; rfl) (by rw [hlm, hlq]; rfl)
      hdomainL direct hpaid hsmall error herror v.block.left_positive v.block.right_positive
      hsecond hopposite hunit hstep mesh hmesh hfit lo hi hlo hhi orders original
      hreference htime horders leftComputed hprimeOrders δ analyticHeight hδ hδhi
      (analyticLeft r) (hanalyticLeft r)
  let right : ∀ r : Bool, SecondSideNormalization ((rectangles).rightFrame C r)
      ω ψ Set.univ Set.univ (Set.Icc 0 hi) orders := fun r =>
    (rightTable).produceLiteralSideAll rightTests ordinaryRows .right j.2.1
      (fun i => v.block.rightResidual (v.rightReindex.index i)) v.rightReindex.ideal_product
      (-firstSign) r j.1.val j.2.2.2.val (Finset.mem_filter.mp (allocation).property).2.2.2
      (cals.2 r) P Rchar F parent oldMoving correction hcorr remaining extra a step rightGeometry
      pattern sector rightRecipe.slots paidCutoff reference time
      (by intro ξ; rw [hrm, hrq]; rfl) (by rw [hrm, hrq]; rfl)
      hdomainR direct hpaid hsmall error herror v.block.left_positive v.block.right_positive
      hopposite hsecond hunitR hstep mesh hmesh hfit lo hi hlo hhi orders original
      hreference htime horders rightComputed hprimeOrders δ analyticHeight hδ hδhi
      (analyticRight r) (hanalyticRight r)
  exact
    { rows := normalizationRows
      leftPlain₁ := (v.literalLeftAtoms leftAtoms).plain₁
      leftPlain₂ := (v.literalLeftAtoms leftAtoms).plain₂
      leftPrimes := (v.literalLeftAtoms leftAtoms).slots
      rightPlain₁ := (v.literalRightAtoms rightAtoms).plain₁
      rightPlain₂ := (v.literalRightAtoms rightAtoms).plain₂
      rightPrimes := (v.literalRightAtoms rightAtoms).slots
      leftIdeal := fun i => v.block.leftResidual (v.leftReindex.index i)
      rightIdeal := fun i => v.block.rightResidual (v.rightReindex.index i)
      leftRay := fun _ => PUnit.unit
      rightRay := fun _ => PUnit.unit
      leftWhole := ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).whole
      rightWhole := ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).whole
      leftPoint := fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.plain firstSign) (CanonicalLiteralLocations.prime firstSign)
      rightPoint := fun _ => rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
        (CanonicalLiteralLocations.plain (-firstSign)) (CanonicalLiteralLocations.prime (-firstSign))
      branch := allocation
      «rectangles» := rectangles
      binding := binding
      left := left
      right := right
      left_base := fun _ => hbaseLeft
      right_base := fun _ => hbaseRight
      left_height := fun _ _ => Set.mem_univ _
      right_height := fun _ _ => Set.mem_univ _ }

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.computedLiteralCalibrations
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationData
