import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrameCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPreparedBinding

/-!
# Calibrations on the actual two rectangle families of a covered leaf

The physical stage is the canonical empty-row-mask stage with the
original extracted sector included in its finite label. The two table
certificates are the outputs of the original direct/main/pool profile
constructors. Common atom bounds, row fibres, both actual allocations
and both frozen scalar costs are constructed inside this theorem.

The returned calibrations belong literally to `literalRectangles` on
the stored leaf. Their ordinary row predicate is the original common
character predicate, fixed before either Fourier variable. All inputs
which identify arithmetic fields are individual character, slot-index
or scale identities of the already constructed tables.
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
open CanonicalLiteralActualProfiles

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

local instance canonicalLiteralCoveredCalibrationCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
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
  P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoveredClassKey LC RC)
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)
variable (hlive : (v.leaf exceptional firstKernel x j).Live) (firstSign : ℝ)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
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
variable (leftIndex : Fin v.leftSlots → Fin parent.geometry.slotCount)
variable (rightIndex : Fin v.literalRightBranch.keep.card → Fin parent.geometry.slotCount)
variable (hcharactersLeft : (v.literalLeftAtoms leftAtoms).characters =
  CanonicalLiteralPhaseCalibration.sourceCharacters P Rchar F parent oldMoving correction
    remaining extra leftIndex)
variable (hcharactersRight : (v.literalRightAtoms rightAtoms).characters =
  CanonicalLiteralPhaseCalibration.sourceCharacters P Rchar F parent oldMoving correction
    remaining extra rightIndex)
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ h ∈ (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).rows,
  ‖v.chart.weight h‖ ≤ bound)
variable (a₀ oldq wo cutoffExponent : ℝ)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)
variable (hcolumns : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ a₀)
variable (hactiveColumns : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
  A.exteriorNorm (G.ideal i) ≤ Z ^ a₀)
variable (hold : A.exteriorNorm ((F.moving P Rchar oldMoving).effectiveFullSupport
  (remaining * extra)) ≤ Z ^ (oldq + wo))
variable (m q κ : ℝ)
variable (hwidth : m + q =
  secondCommonChildWidth Z a₀ oldq wo (Real.log retainedScale / Real.log Z) g
    (primePowerProduct v.block.primes v.block.leftMultiplicity).val
    (primePowerProduct v.block.primes v.block.rightMultiplicity).val
    (secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity
      (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)).val
    (secondPatternNonunitIdeal v.block.primes
      (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)).val +
    idealLogLength Z
      (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity).val +
    cutoffExponent)
variable (inverse : IdealTest K)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
  ¬ FiniteOrder parent.plainBackground)
variable (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
variable (hexceptional : (v.leaf exceptional firstKernel x j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).literalCharacter C P Rchar F oldMoving
    correction (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)
    (v.chart.originalSector P ∅ cutoff hcutoff v.rowLabel) h ∈ parent.theta)

/-- Both actual Boolean rectangle families are calibrated together.
The common-row mass is constructed once from the original witnesses,
then restricted to this same ordinary predicate. The second-divisor
scalar is independently calculated on each stored allocation. -/
def literalCoveredCalibrationsActive :
    (∀ r : Bool, ((v.literalRectangles leftAtoms rightAtoms exceptional firstKernel x j
      firstSign hlive).leftFrame C r).source.Calibration (σ := σ) ω ψ) ×
    (∀ r : Bool, ((v.literalRectangles leftAtoms rightAtoms exceptional firstKernel x j
      firstSign hlive).rightFrame C r).source.Calibration (σ := σ) ω ψ) := by
  have hp : v.chart.NonunitLabelStable :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  have hs : v.chart.SectorLabelStable P :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_sectorLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  have hmaskL : (v.literalLeftOriginal leftAtoms).characters.MaskIndicator := by
    change (v.literalLeftAtoms leftAtoms).characters.MaskIndicator
    rw [hcharactersLeft]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra leftIndex
  have hmaskR : (v.literalRightOriginal rightAtoms).characters.MaskIndicator := by
    change (v.literalRightAtoms rightAtoms).characters.MaskIndicator
    rw [hcharactersRight]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra rightIndex
  let mass := (v.literalSupportedRowMass leftAtoms rightAtoms hmaskL hmaskR hp bound hbound
    hprofile).restrictRows (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
  let branch := v.literalAllocation exceptional firstKernel x j hlive
  have hL := (Finset.mem_filter.mp branch.property).2.1
  have hordinary : (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h) =
      fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).literalCharacter C P Rchar F
        oldMoving correction (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)
        (v.chart.originalSector P ∅ cutoff hcutoff v.rowLabel) h ∉ parent.theta := by
    rw [hexceptional]
  refine ⟨fun r => ?_, fun r => ?_⟩
  · have support : (v.literalLeftAtoms leftAtoms).SupportData
        ((primeSupport A.cS ∪ firstSupport) ∪
          primeSupport (primePowerProduct v.block.primes v.block.leftMultiplicity).val) := by
      rw [v.block.common_left]
      exact leftProfiles.support
    exact v.chart.literalFrameCalibrationActive P Rchar hp hs cutoff hcutoff v.rowLabel
      (v.literalRows leftAtoms rightAtoms).weight
      (fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).correlation h ≠ 0)
      (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
      mass (v.literalLeftAtoms leftAtoms) leftProfiles.profiles F parent oldMoving correction
      hcorr remaining extra leftIndex hcharactersLeft firstSupport hfirst hextra support
      retainedScale g a₀ oldq wo cutoffExponent hscale (by rw [hbaseLeft]; rfl)
      (by simpa only [hbaseLeft] using hcutoffPower)
      (by
        intro i hi j hj hpair
        have he := ActualGaussSource.active_gram_pair_norm_le C G _ Z a₀ hZ
          hactiveColumns i hi j hj hpair
        simpa only [hbaseLeft] using he)
      (by simpa only [hbaseLeft] using hold)
      m q κ (by simpa only [hbaseLeft] using hwidth) inverse hone hroot hemb hbackground hslot
      .left j.2.1 (fun i => v.block.leftResidual (v.leftReindex.index i))
      v.leftReindex.ideal_product firstSign r j.1.val j.2.2.1.val
      (Finset.mem_filter.mp branch.property).2.2.1 hL j.2.2.1.property hordinary
  · have support : (v.literalRightAtoms rightAtoms).SupportData
        ((primeSupport A.cS ∪ firstSupport) ∪
          primeSupport (primePowerProduct v.block.primes v.block.leftMultiplicity).val) := by
      rw [v.block.common_left]
      exact rightProfiles.support
    exact v.chart.literalFrameCalibrationActive P Rchar hp hs cutoff hcutoff v.rowLabel
      (v.literalRows leftAtoms rightAtoms).weight
      (fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).correlation h ≠ 0)
      (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
      mass (v.literalRightAtoms rightAtoms) rightProfiles.profiles F parent oldMoving correction
      hcorr remaining extra rightIndex hcharactersRight firstSupport hfirst hextra support
      retainedScale g a₀ oldq wo cutoffExponent hscale (by rw [hbaseRight]; rfl)
      (by simpa only [hbaseRight] using hcutoffPower)
      (by
        intro i hi j hj hpair
        have he := ActualGaussSource.active_gram_pair_norm_le C G _ Z a₀ hZ
          hactiveColumns i hi j hj hpair
        simpa only [hbaseRight] using he)
      (by simpa only [hbaseRight] using hold)
      m q κ (by simpa only [hbaseRight] using hwidth) inverse hone hroot hemb hbackground hslot
      .right j.2.1 (fun i => v.block.rightResidual (v.rightReindex.index i))
      v.rightReindex.ideal_product (-firstSign) r j.1.val j.2.2.2.val
      (Finset.mem_filter.mp branch.property).2.2.2 hL j.2.2.2.property hordinary

/-- The earlier all-column constructor is retained as a specialization.
The actual canonical centered entrance uses the active constructor
above, whose sharp window follows from its complete original coefficient. -/
def literalCoveredCalibrations :
    (∀ r : Bool, ((v.literalRectangles leftAtoms rightAtoms exceptional firstKernel x j
      firstSign hlive).leftFrame C r).source.Calibration (σ := σ) ω ψ) ×
    (∀ r : Bool, ((v.literalRectangles leftAtoms rightAtoms exceptional firstKernel x j
      firstSign hlive).rightFrame C r).source.Calibration (σ := σ) ω ψ) :=
  literalCoveredCalibrationsActive P Rchar δ hδ hδhalf G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC v exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms firstSupport hfirst leftProfiles rightProfiles
    hbaseLeft hbaseRight F parent oldMoving correction hcorr remaining extra hextra
    leftIndex rightIndex hcharactersLeft hcharactersRight bound hbound hprofile
    a₀ oldq wo cutoffExponent hcutoffPower (fun i hi _ => hcolumns i hi) hold
    m q κ hwidth inverse hone hroot hemb hbackground hslot hexceptional

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalCoveredCalibrations
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalCoveredCalibrationsActive
