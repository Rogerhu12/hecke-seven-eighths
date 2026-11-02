import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormalizationCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveCapacityWindow
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtomCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredGaussScale
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionSeparateMass

set_option linter.unusedSectionVars false

/-!
# Original windows bound the same literal normalized pairs

The original source activity is used only to justify its computed small
raw-scale error. Both capacities, all profile radii, both chosen children
and their removed sets remain those produced before this restriction.
The original Gauss normalization, empty-mask radius, and individual
occurrence costs are evaluated on those same stored objects.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open CommonSupportMass

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralActualProfiles PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]

namespace OriginalNominalGeometry

/-- The lower radius appearing in the row scalar is the actual
canonical row-ball radius, with its original retained endpoint. -/
theorem literalInverseRadius {a : RealParameters} {Z step : ℝ}
    (G : OriginalNominalGeometry (K := K) a Z step) (hZ : 1 < Z) :
    Z ^ (-G.skeleton.Krow - G.skeleton.g) =
      (G.retainedScale * Z ^ G.enlargement)⁻¹ := by
  sorry

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

local instance canonicalLiteralNormalizedWeightsCircleCharacterFintype :
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

local notation "leftLengths" =>
  v.literalNormalizationLeftLengthBinding
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

local notation "leftCapacityAtoms" =>
  v.literalNormalizationLeftCapacityAtoms
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

local notation "rightLengths" =>
  v.literalNormalizationRightLengthBinding
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

local notation "rightCapacityAtoms" =>
  v.literalNormalizationRightCapacityAtoms
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

local notation "leftCapacityProof" =>
  v.literalNormalizationData_leftCapacity_actual
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

local notation "rightCapacityProof" =>
  v.literalNormalizationData_rightCapacity_actual
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

local notation "arithmetic" =>
  v.literalNormalizationArithmeticInput
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
/-- These are original per-occurrence windows and the original first
extraction/Gauss bounds, supplied by the six direct/main/pool literal
constructors. The result is the weight of this exact already selected
normalized pair. All second extraction, active-error, radius and
capacity identities are proved inside the theorem. -/
theorem literalNormalizationData_allowance_from_original_atoms
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
    (b : (normalization).family.active Finset.univ) :
    (normalization).family.weight Finset.univ 0 b / firstNormalization ≤
      ((Γ.index : ℝ) * (profileBound * ‖leftScalar‖ * ‖rightScalar‖) *
        atomBound ^ (2 * cap) * orbitalFieldFactor K) *
        Z ^ (geometry.skeleton.wo + geometry.tag.poolLength step + 5 * error / 3 + mesh) *
          (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
            (Ideal.absNorm j.1.val : ℝ) := by
  sorry

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.literalInverseRadius
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationData_allowance_from_original_atoms
