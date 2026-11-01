import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormalizedLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSideRadius
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveRadius
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralInactiveRectangle
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralKernelConstants

/-!
# Radii of the same constructed normalized covered family

The two coefficients below are computed from the original profile
certificates and the actual allocation parameters. These equalities
expose their exact use by `literalNormalizationData.family`; no second
normalization, child or removed set is chosen. Activity is subsequently
used only to bound these already computed coefficients.
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

local instance canonicalLiteralNormalizedRadiiCircleCharacterFintype :
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

variable
    (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
    (binding : X.leaf.OrdinaryBinding (v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance))
    (analyticLeft : ∀ r : Bool, ∀ _hκ : ((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).parameters.κ < 1, ∀ ξ,
      ∀ u, u ∈ pairedRows (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).data ξ) ((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).parameters
        ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).leftFrame C r).source.base →
      ∀ i : Fin ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).leftFrame C r).source.allocation.keep.card,
        ZeroFreeData (heckeContinuation K ((((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).data ξ).rowCharacter u *
          (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).data ξ).slotCoefficient
            (lengthSlot (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).data ξ)
              ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).leftFrame C r).source.allocation.keep.card
              (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).count ξ) i))) ((((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).parameters.κ + 1) / 2))
    (analyticRight : ∀ r : Bool, ∀ _hκ : ((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).parameters.κ < 1, ∀ ξ,
      ∀ u, u ∈ pairedRows (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).data ξ) ((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).parameters
        ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).rightFrame C r).source.base →
      ∀ i : Fin ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).rightFrame C r).source.allocation.keep.card,
        ZeroFreeData (heckeContinuation K ((((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).data ξ).rowCharacter u *
          (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).data ξ).slotCoefficient
            (lengthSlot (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).data ξ)
              ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).rightFrame C r).source.allocation.keep.card
              (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).count ξ) i))) ((((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).parameters.κ + 1) / 2))
    (hanalyticLeft : ∀ r : Bool, ∀ hκ : ((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).parameters.κ < 1, ∀ ξ,
      ∀ u, ∀ hu : u ∈ pairedRows (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).data ξ) ((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).1 r).parameters
        ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).leftFrame C r).source.base,
      ∀ i : Fin ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).leftFrame C r).source.allocation.keep.card,
        heightConstant (analyticLeft r hκ ξ u hu i) +
          3 * ((analyticLeft r hκ ξ u hu i).k : ℝ) ≤ analyticHeight)
    (hanalyticRight : ∀ r : Bool, ∀ hκ : ((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).parameters.κ < 1, ∀ ξ,
      ∀ u, ∀ hu : u ∈ pairedRows (((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).data ξ) ((v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional).2 r).parameters
        ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).rightFrame C r).source.base,
      ∀ i : Fin ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).rightFrame C r).source.allocation.keep.card,
        heightConstant (analyticRight r hκ ξ u hu i) +
          3 * ((analyticRight r hκ ξ u hu i).k : ℝ) ≤ analyticHeight)

local notation "normalization" =>
  v.literalNormalizationData
    (P := P)
    (Rchar := Rchar)
    (δ₂ := δ₂)
    (hδ₂ := hδ₂)
    (hδ₂half := hδ₂half)
    (G := G)
    (retainedScale := retainedScale)
    (Z := Z)
    (g := g)
    (hscale := hscale)
    (hZ := hZ)
    (cutoff := cutoff)
    (hcutoff := hcutoff)
    (hnorm := hnorm)
    (dimension := dimension)
    (width := width)
    (character := character)
    (dyad := dyad)
    (LC := LC)
    (RC := RC)
    (exceptional := exceptional)
    (firstKernel := firstKernel)
    (x := x)
    (j := j)
    (hlive := hlive)
    (firstSign := firstSign)
    (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms)
    (leftScalar := leftScalar)
    (rightScalar := rightScalar)
    (leftBalance := leftBalance)
    (rightBalance := rightBalance)
    (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance)
    (firstSupport := firstSupport)
    (hfirst := hfirst)
    (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles)
    (hbaseLeft := hbaseLeft)
    (hbaseRight := hbaseRight)
    (F := F)
    (parent := parent)
    (oldMoving := oldMoving)
    (correction := correction)
    (hcorr := hcorr)
    (remaining := remaining)
    (extra := extra)
    (hextra := hextra)
    (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe)
    (profileBound := profileBound)
    (hprofileBound := hprofileBound)
    (hprofile := hprofile)
    (a := a)
    (step := step)
    (geometry := geometry)
    (hretained := hretained)
    (henlargement := henlargement)
    (hsecond := hsecond)
    (hopposite := hopposite)
    (hunit := hunit)
    (hnonunit := hnonunit)
    (columnLoss := columnLoss)
    (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss)
    (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns)
    (hold := hold)
    (reference := reference)
    (time := time)
    (hone := hone)
    (hroot := hroot)
    (hemb := hemb)
    (hbackground := hbackground)
    (hslot := hslot)
    (hexceptional := hexceptional)
    (domain := domain)
    (direct := direct)
    (hsmall := hsmall)
    (error := error)
    (herror := herror)
    (hstep := hstep)
    (mesh := mesh)
    (hmesh := hmesh)
    (hfit := hfit)
    (lo := lo)
    (hi := hi)
    (hlo := hlo)
    (hhi := hhi)
    (orders := orders)
    (original := original)
    (hreference := hreference)
    (htime := htime)
    (horders := horders)
    (leftComputed := leftComputed)
    (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders)
    (δ := δ)
    (analyticHeight := analyticHeight)
    (hδ := hδ)
    (hδhi := hδhi)
    (X := X)
    (binding := binding)
    (analyticLeft := analyticLeft)
    (analyticRight := analyticRight)
    (hanalyticLeft := hanalyticLeft)
    (hanalyticRight := hanalyticRight)

/-- The original computed left coefficient, before the independent
single-prime analytic enlargement. -/
def literalLeftProfileCoefficient (r : Bool) : ℝ :=
  leftComputed.coefficient Z (calibrations.1 r).parameters isCompact_Icc
    (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign r

/-- The right sign is the original Fourier orientation. -/
def literalRightProfileCoefficient (r : Bool) : ℝ :=
  rightComputed.coefficient Z (calibrations.2 r).parameters isCompact_Icc
    (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) r

@[simp] theorem literalNormalizationData_leftCalibration (rs : Bool × Bool) :
    normalization.family.leftCalibration rs = calibrations.1 rs.1 := rfl

@[simp] theorem literalNormalizationData_rightCalibration (rs : Bool × Bool) :
    normalization.family.rightCalibration rs = calibrations.2 rs.2 := rfl

@[simp] theorem literalNormalizationData_leftRadius (rs : Bool × Bool) (z : ℝ × ℝ) :
    (normalization.family.leftCapacity rs).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius
        (CanonicalFullKappaPrime.enlargedCoefficient
          (leftComputed.coefficient Z (calibrations.1 rs.1).parameters isCompact_Icc
            (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign rs.1)
          (CanonicalFullKappaPrime.radiusFactor K Z δ mesh
            (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
            (CompleteMovingRowRecipe.primeMaskLogBound A Z (m + q))))
        (orders.sup Prod.snd) (orders.sup Prod.snd) z := by
  let «GL» := geometry.atBase leftTable.base hbaseLeft
  have hmL : «GL».literalRowParameter paidCutoff = m :=
    geometry.atBase_literalRowParameter leftTable.base hbaseLeft paidCutoff
  have hrootL : idealLogLength leftTable.base
      (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.leftMultiplicity
        ordinaryRows.rightMultiplicity).val = rootLength := by
    change idealLogLength (v.literalLeftAtoms leftAtoms).base
      (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity).val = _
    rw [hbaseLeft]
  have hqL : «GL».literalSupportParameter
      (idealLogLength leftTable.base
        (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.leftMultiplicity
          ordinaryRows.rightMultiplicity).val) = q := by
    rw [hrootL]
    exact geometry.atBase_literalSupportParameter leftTable.base hbaseLeft rootLength
  change polynomialProfileRadius
    (CanonicalFullKappaPrime.enlargedCoefficient
      (leftComputed.coefficient leftTable.base (calibrations.1 rs.1).parameters isCompact_Icc
        (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign rs.1)
      (CanonicalFullKappaPrime.radiusFactor K leftTable.base δ mesh
        (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
        (CompleteMovingRowRecipe.primeMaskLogBound A leftTable.base
          («GL».literalRowParameter paidCutoff + «GL».literalSupportParameter
            (idealLogLength leftTable.base
              (secondSixthRootIdeal ordinaryRows.primes ordinaryRows.leftMultiplicity
                ordinaryRows.rightMultiplicity).val)))))
    (orders.sup Prod.snd) (orders.sup Prod.snd) z = _
  rw [hmL, hqL]
  have hb : leftTable.base = Z := hbaseLeft
  rw [hb]

@[simp] theorem literalNormalizationData_rightRadius (rs : Bool × Bool) (z : ℝ × ℝ) :
    (normalization.family.rightCapacity rs).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius
        (CanonicalFullKappaPrime.enlargedCoefficient
          (rightComputed.coefficient Z (calibrations.2 rs.2).parameters isCompact_Icc
            (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) rs.2)
          (CanonicalFullKappaPrime.radiusFactor K Z δ mesh
            (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
            (CompleteMovingRowRecipe.primeMaskLogBound A Z (m + q))))
        (orders.sup Prod.snd) (orders.sup Prod.snd) z := by
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
      (rightComputed.coefficient rightTable.base (calibrations.2 rs.2).parameters isCompact_Icc
        (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) rs.2)
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

/-- The coefficient bound uses the actual left source activity and the
original first-branch identities. The displayed `hbound` is the exact
formula returned by the six original computed-profile constructors,
not an estimate of the descendant or its radius. -/
theorem literalNormalizationData_leftActiveCoefficient_le
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
        (1 + CanonicalLiteralBalancedSchwartz.factor seed first δ₁ δ₂ r))
    (rs : normalization.family.active Finset.univ) :
    leftComputed.coefficient Z (calibrations.1 rs.val.1).parameters isCompact_Icc
      (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign rs.val.1 ≤
        CanonicalLiteralRadiusBound.fixedCoefficient originalBound lo hi hlo δ₁ δ₂ firstSign orders := by
  have hactive : ¬ ∀ ξ, (rectangles.leftFrame C rs.val.1).source.energy (σ := σ) ξ = 0 :=
    (Finset.mem_filter.mp rs.property).2.1
  have hwhich := leftTable.active_rectangle C ordinaryRows .left j.2.1
    (fun i => v.block.leftResidual (v.leftReindex.index i)) v.leftReindex.ideal_product
    firstSign j.1.val j.2.2.1.val (Finset.mem_filter.mp allocation.property).2.2.1
    rs.val.1 hactive
  have hproduct : seed.scale₁ rs.val.1 * seed.scale₂ rs.val.1 =
      seed.scale₁ false * seed.scale₂ false := by
    rcases hwhich with hr | hc
    · rw [hr]
    · cases hr : rs.val.1 with
      | false => simp only [hr]
      | true => simpa only [hr] using hcomparison (hcentered.symm.trans hc)
  have hB : 0 ≤ originalBound :=
    (show 0 ≤ originalOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (original.leftRep reference time) by positivity).trans
      (original.left_bound reference hreference time htime)
  have hfixed := CanonicalLiteralActiveRadius.coefficient_le_fixed_of_source_active
    seed first (v.literalLeftOriginal leftAtoms) v.literalLeftBranch
    v.literalLeftResidualAtlas rfl leftScalar⁻¹ leftBalance leftTests
    (rectangles.leftFrame C rs.val.1).allocation leftComputed
    rs.val.1 m q a.κ δ₁ δ₂ firstSign false hB hlo hhi hδlo hδhi'
    hproduct hbase (hfirst₁ rs.val.1) (hfirst₂ rs.val.1) (congrFun hbound rs.val.1)
    (rectangles.leftFrame C rs.val.1).source (calibrations.1 rs.val.1)
    hbase rfl (fun _ => rfl) (fun _ => rfl) hactive
  have hb : (rectangles.leftFrame C rs.val.1).source.base = Z := hbaseLeft
  simpa only [hb] using hfixed

/-- The right source retains its original negative Fourier orientation.
Both tests and all allocation divisors are the actual right ones. -/
theorem literalNormalizationData_rightActiveCoefficient_le
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
        (1 + CanonicalLiteralBalancedSchwartz.factor seed first δ₁ δ₂ r))
    (rs : normalization.family.active Finset.univ) :
    rightComputed.coefficient Z (calibrations.2 rs.val.2).parameters isCompact_Icc
      (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) rs.val.2 ≤
        CanonicalLiteralRadiusBound.fixedCoefficient originalBound lo hi hlo δ₁ δ₂ (-firstSign) orders := by
  have hactive : ¬ ∀ ξ, (rectangles.rightFrame C rs.val.2).source.energy (σ := σ) ξ = 0 :=
    (Finset.mem_filter.mp rs.property).2.2
  have hwhich := rightTable.active_rectangle C ordinaryRows .right j.2.1
    (fun i => v.block.rightResidual (v.rightReindex.index i)) v.rightReindex.ideal_product
    (-firstSign) j.1.val j.2.2.2.val (Finset.mem_filter.mp allocation.property).2.2.2
    rs.val.2 hactive
  have hproduct : seed.scale₁ rs.val.2 * seed.scale₂ rs.val.2 =
      seed.scale₁ false * seed.scale₂ false := by
    rcases hwhich with hr | hc
    · rw [hr]
    · cases hr : rs.val.2 with
      | false => simp only [hr]
      | true => simpa only [hr] using hcomparison (hcentered.symm.trans hc)
  have hB : 0 ≤ originalBound :=
    (show 0 ≤ originalOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (original.leftRep reference time) by positivity).trans
      (original.left_bound reference hreference time htime)
  have hfixed := CanonicalLiteralActiveRadius.coefficient_le_fixed_of_source_active
    seed first (v.literalRightOriginal rightAtoms) v.literalRightBranch
    v.literalRightResidualAtlas rfl rightScalar⁻¹ rightBalance rightTests
    (rectangles.rightFrame C rs.val.2).allocation rightComputed
    rs.val.2 m q a.κ δ₁ δ₂ (-firstSign) true hB hlo hhi hδlo hδhi'
    hproduct hbase (hfirst₁ rs.val.2) (hfirst₂ rs.val.2) (congrFun hbound rs.val.2)
    (rectangles.rightFrame C rs.val.2).source (calibrations.2 rs.val.2)
    hbase rfl (fun _ => rfl) (fun _ => rfl) hactive
  have hb : (rectangles.rightFrame C rs.val.2).source.base = Z := hbaseRight
  simpa only [hb] using hfixed


local notation "leftRadiusProof" =>
  v.literalNormalizationData_leftRadius
    (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂)
    (hδ₂half := hδ₂half) (G := G) (retainedScale := retainedScale) (Z := Z)
    (g := g) (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension) (width := width)
    (character := character) (dyad := dyad) (LC := LC) (RC := RC)
    (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar) (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hleftBalance) (hrightBalance := hrightBalance) (firstSupport := firstSupport) (hfirst := hfirst)
    (leftProfiles := leftProfiles) (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
    (hcorr := hcorr) (remaining := remaining) (extra := extra) (hextra := hextra)
    (leftRecipe := leftRecipe) (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step) (geometry := geometry)
    (hretained := hretained) (henlargement := henlargement) (hsecond := hsecond) (hopposite := hopposite)
    (hunit := hunit) (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns)
    (hold := hold) (reference := reference) (time := time) (hone := hone)
    (hroot := hroot) (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct) (hsmall := hsmall)
    (error := error) (herror := herror) (hstep := hstep) (mesh := mesh)
    (hmesh := hmesh) (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders) (original := original)
    (hreference := hreference) (htime := htime) (horders := horders) (leftComputed := leftComputed)
    (rightComputed := rightComputed) (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi) (X := X) (binding := binding)
    (analyticLeft := analyticLeft) (analyticRight := analyticRight) (hanalyticLeft := hanalyticLeft) (hanalyticRight := hanalyticRight)

local notation "rightRadiusProof" =>
  v.literalNormalizationData_rightRadius
    (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂)
    (hδ₂half := hδ₂half) (G := G) (retainedScale := retainedScale) (Z := Z)
    (g := g) (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension) (width := width)
    (character := character) (dyad := dyad) (LC := LC) (RC := RC)
    (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar) (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hleftBalance) (hrightBalance := hrightBalance) (firstSupport := firstSupport) (hfirst := hfirst)
    (leftProfiles := leftProfiles) (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
    (hcorr := hcorr) (remaining := remaining) (extra := extra) (hextra := hextra)
    (leftRecipe := leftRecipe) (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step) (geometry := geometry)
    (hretained := hretained) (henlargement := henlargement) (hsecond := hsecond) (hopposite := hopposite)
    (hunit := hunit) (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns)
    (hold := hold) (reference := reference) (time := time) (hone := hone)
    (hroot := hroot) (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct) (hsmall := hsmall)
    (error := error) (herror := herror) (hstep := hstep) (mesh := mesh)
    (hmesh := hmesh) (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders) (original := original)
    (hreference := hreference) (htime := htime) (horders := horders) (leftComputed := leftComputed)
    (rightComputed := rightComputed) (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi) (X := X) (binding := binding)
    (analyticLeft := analyticLeft) (analyticRight := analyticRight) (hanalyticLeft := hanalyticLeft) (hanalyticRight := hanalyticRight)

local notation "leftActiveBound" =>
  v.literalNormalizationData_leftActiveCoefficient_le
    (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂)
    (hδ₂half := hδ₂half) (G := G) (retainedScale := retainedScale) (Z := Z)
    (g := g) (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension) (width := width)
    (character := character) (dyad := dyad) (LC := LC) (RC := RC)
    (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar) (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hleftBalance) (hrightBalance := hrightBalance) (firstSupport := firstSupport) (hfirst := hfirst)
    (leftProfiles := leftProfiles) (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
    (hcorr := hcorr) (remaining := remaining) (extra := extra) (hextra := hextra)
    (leftRecipe := leftRecipe) (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step) (geometry := geometry)
    (hretained := hretained) (henlargement := henlargement) (hsecond := hsecond) (hopposite := hopposite)
    (hunit := hunit) (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns)
    (hold := hold) (reference := reference) (time := time) (hone := hone)
    (hroot := hroot) (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct) (hsmall := hsmall)
    (error := error) (herror := herror) (hstep := hstep) (mesh := mesh)
    (hmesh := hmesh) (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders) (original := original)
    (hreference := hreference) (htime := htime) (horders := horders) (leftComputed := leftComputed)
    (rightComputed := rightComputed) (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi) (X := X) (binding := binding)
    (analyticLeft := analyticLeft) (analyticRight := analyticRight) (hanalyticLeft := hanalyticLeft) (hanalyticRight := hanalyticRight)

local notation "rightActiveBound" =>
  v.literalNormalizationData_rightActiveCoefficient_le
    (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂)
    (hδ₂half := hδ₂half) (G := G) (retainedScale := retainedScale) (Z := Z)
    (g := g) (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension) (width := width)
    (character := character) (dyad := dyad) (LC := LC) (RC := RC)
    (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar) (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hleftBalance) (hrightBalance := hrightBalance) (firstSupport := firstSupport) (hfirst := hfirst)
    (leftProfiles := leftProfiles) (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
    (hcorr := hcorr) (remaining := remaining) (extra := extra) (hextra := hextra)
    (leftRecipe := leftRecipe) (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step) (geometry := geometry)
    (hretained := hretained) (henlargement := henlargement) (hsecond := hsecond) (hopposite := hopposite)
    (hunit := hunit) (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns)
    (hold := hold) (reference := reference) (time := time) (hone := hone)
    (hroot := hroot) (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct) (hsmall := hsmall)
    (error := error) (herror := herror) (hstep := hstep) (mesh := mesh)
    (hmesh := hmesh) (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders) (original := original)
    (hreference := hreference) (htime := htime) (horders := horders) (leftComputed := leftComputed)
    (rightComputed := rightComputed) (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi) (X := X) (binding := binding)
    (analyticLeft := analyticLeft) (analyticRight := analyticRight) (hanalyticLeft := hanalyticLeft) (hanalyticRight := hanalyticRight)

/-- The remaining cap is inherited from the actual original slot
embedding, before capacity removal or the activity test. -/
theorem literalNormalizationData_leftSlots_le (cap : ℕ)
    (hcap : parent.geometry.slotCount ≤ cap) (rs : Bool × Bool) :
    (normalization.family.leftSource rs).allocation.keep.card ≤ cap := by
  have hf : normalization.family.leftSlots rs ≤ parent.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective leftRecipe.slots.index leftRecipe.slots.index.injective
  have hk : (normalization.family.leftSource rs).allocation.keep.card ≤
      normalization.family.leftSlots rs := by
    simpa only [Fintype.card_fin] using
      Finset.card_le_univ (normalization.family.leftSource rs).allocation.keep
  exact hk.trans (hf.trans hcap)

theorem literalNormalizationData_rightSlots_le (cap : ℕ)
    (hcap : parent.geometry.slotCount ≤ cap) (rs : Bool × Bool) :
    (normalization.family.rightSource rs).allocation.keep.card ≤ cap := by
  have hf : normalization.family.rightSlots rs ≤ parent.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective rightRecipe.slots.index rightRecipe.slots.index.injective
  have hk : (normalization.family.rightSource rs).allocation.keep.card ≤
      normalization.family.rightSlots rs := by
    simpa only [Fintype.card_fin] using
      Finset.card_le_univ (normalization.family.rightSource rs).allocation.keep
  exact hk.trans (hf.trans hcap)

/-- The actual normalized kernels are integrated over their existing
active carrier. Both original Fourier kernels and the exact remaining
arithmetic weight sum are retained. The constant and Fourier orders
are chosen by `CanonicalLiteralKernelConstants` before every source;
the full single-prime factor is paid to both complete pre-removal
profile counts. The final small-power absorption is the previously
proved `exists_complete_profile_radius_bound` on this explicit factor.

The identities relating the two first branches to the actual table are
the computed constructor projections. In particular `hboundL/R` are
literal formulas, not profile estimates or mass hypotheses. -/
theorem literalNormalizationData_kernelMass
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
    let family := normalization.family
    let labels := (Finset.univ : Finset (Bool × Bool))
    let μ := actualNestedLabelMeasure (fun _ : Bool × Bool => X.leaf.firstKernel)
      (fun _ : Bool × Bool => X.leaf.secondKernel) (fun _ : Bool × Bool => X.leaf.weight)
    let factor := CanonicalFullKappaPrime.radiusFactor K Z δ mesh
      (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
      (CompleteMovingRowRecipe.primeMaskLogBound A Z (m + q))
    let fixed := CanonicalLiteralActiveRadius.twoSignsCoefficient
      originalBound lo hi hlo δ₁ δ₂ orders
    (∀ rs : family.active labels,
      IsFiniteMeasure (family.kernel labels μ (a.m + a.q) rs)) ∧
      (∑ rs : family.active labels, (family.kernel labels μ (a.m + a.q) rs).real Set.univ) ≤
        CanonicalLiteralKernelConstants.constant K A σ ω ψ cap (orders.sup Prod.snd) *
          (2 * factor) ^ ((cap + 2) + (cap + 2)) *
            (1 + fixed) ^ ((cap + 2) + (cap + 2)) *
              (CanonicalLiteralKernelConstants.firstOrders K A σ ω ψ cap (orders.sup Prod.snd)).sup
                (schwartzSeminormFamily ℝ ℝ ℂ) X.leaf.firstKernel *
              (CanonicalLiteralKernelConstants.secondOrders K A σ ω ψ cap (orders.sup Prod.snd)).sup
                (schwartzSeminormFamily ℝ ℝ ℂ) X.leaf.secondKernel *
                ∑ rs : family.active labels,
                  X.leaf.weight * family.weight labels (a.m + a.q) rs := by
  dsimp only
  let family := normalization.family
  let L := fun rs : Bool × Bool => leftComputed.coefficient Z (calibrations.1 rs.1).parameters
    isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign rs.1
  let R := fun rs : Bool × Bool => rightComputed.coefficient Z (calibrations.2 rs.2).parameters
    isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) rs.2
  let factor := CanonicalFullKappaPrime.radiusFactor K Z δ mesh
    (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
    (CompleteMovingRowRecipe.primeMaskLogBound A Z (m + q))
  let fixed := CanonicalLiteralActiveRadius.twoSignsCoefficient originalBound lo hi hlo δ₁ δ₂ orders
  let s₁ := CanonicalLiteralKernelConstants.firstOrders K A σ ω ψ cap (orders.sup Prod.snd)
  let s₂ := CanonicalLiteralKernelConstants.secondOrders K A σ ω ψ cap (orders.sup Prod.snd)
  let S₁ := s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) X.leaf.firstKernel
  let S₂ := s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) X.leaf.secondKernel
  have hL (rs : Bool × Bool) : 0 ≤ L rs :=
    leftComputed.coefficient_nonneg Z _ domain.scale.le isCompact_Icc
      (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign rs.1
  have hR (rs : Bool × Bool) : 0 ≤ R rs :=
    rightComputed.coefficient_nonneg Z _ domain.scale.le isCompact_Icc
      (CanonicalLogProfiles.positiveAnnulus lo hi hlo) (-firstSign) rs.2
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
      hbaseL hfirstL₁ hfirstL₂ hboundL rs).trans
      (CanonicalLiteralActiveRadius.fixedCoefficient_le_twoSigns
        originalBound lo hi hlo δ₁ δ₂ firstSign orders hfirstSign)
  have hnegativeSign : -firstSign = 1 ∨ -firstSign = -1 := by
    rcases hfirstSign with h | h
    · right; rw [h]
    · left; rw [h]; norm_num
  have hRfixed (rs : family.active Finset.univ) : R rs.val ≤ fixed :=
    (rightActiveBound rightSeed rightFirst δ₁ hδlo hδhi' hcomparisonR hcenteredR
      hbaseR hfirstR₁ hfirstR₂ hboundR rs).trans
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
  have hcapL (rs : Bool × Bool) : (family.leftSource rs).allocation.keep.card ≤ cap := by
    have hf : family.leftSlots rs ≤ parent.geometry.slotCount := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective leftRecipe.slots.index leftRecipe.slots.index.injective
    have hk : (family.leftSource rs).allocation.keep.card ≤ family.leftSlots rs := by
      simpa only [Fintype.card_fin] using
        Finset.card_le_univ (family.leftSource rs).allocation.keep
    exact hk.trans (hf.trans hcap)
  have hcapR (rs : Bool × Bool) : (family.rightSource rs).allocation.keep.card ≤ cap := by
    have hf : family.rightSlots rs ≤ parent.geometry.slotCount := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective rightRecipe.slots.index rightRecipe.slots.index.injective
    have hk : (family.rightSource rs).allocation.keep.card ≤ family.rightSlots rs := by
      simpa only [Fintype.card_fin] using
        Finset.card_le_univ (family.rightSource rs).allocation.keep
    exact hk.trans (hf.trans hcap)
  have hm := (actual_finite_normalized_kernel_mass_active
    (F := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := ℝ) (E := ℝ)
    cap (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd))
      .choose_spec.choose_spec.choose_spec.2
  have hout := hm Z hZ family Finset.univ
    (fun _ : Bool × Bool => X.leaf.firstKernel) (fun _ : Bool × Bool => X.leaf.secondKernel)
    (fun _ : Bool × Bool => X.leaf.weight)
    (fun rs => CanonicalFullKappaPrime.enlargedCoefficient (L rs) factor)
    (fun rs => CanonicalFullKappaPrime.enlargedCoefficient (R rs) factor)
    (a.m + a.q) control (fun _ _ => X.leaf.weight_nonneg)
    (fun rs _ => CanonicalFullKappaPrime.enlargedCoefficient_nonneg
      (hL rs) (zero_le_one.trans hfactor))
    (fun rs _ => CanonicalFullKappaPrime.enlargedCoefficient_nonneg
      (hR rs) (zero_le_one.trans hfactor))
    (fun rs _ => hcapL rs) (fun rs _ => hcapR rs)
    (fun rs _ z => leftRadiusProof rs z) (fun rs _ z => rightRadiusProof rs z)
    hprofiles
  refine ⟨hout.1, hout.2.trans_eq ?_⟩
  dsimp only [control, S₁, S₂, s₁, s₂, CanonicalLiteralKernelConstants.constant]
  ring

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationData_leftRadius
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationData_rightRadius

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationData_leftActiveCoefficient_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationData_rightActiveCoefficient_le

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationData_kernelMass
