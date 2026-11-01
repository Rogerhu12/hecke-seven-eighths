import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralBalancedCovered
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectScalars
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolScalars
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantProfileExtraction

/-!
# One payment of the actual constant factors on the stored leaf

The exact first common and pool constants are extracted from both
complete columns before their profiles are normalized. The six source
constructors imported here prove their atom-table normal forms from
the original data. A nonzero coefficient of the original live leaf
then proves that its relevant scalar is nonzero; no nonempty ordinary
row assumption or final child estimate is used.

The inverse-scaled, reciprocally balanced profiles are the actual
individual tests. Their original scalar factors enter the same row
weight once. The second common scalar, divisor, allocation, kernels
and original Fourier locations are all retained.
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

local instance canonicalLiteralStrippedCoveredCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

section StoredLeaf

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (exceptional : s.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)
variable (leftCoefficient : ∀ i ∈ (LC.branch v.2.2.1).reindex.cartesian,
  (LC.branch v.2.2.1).reindex.index i ∈ v.block.leftColumns G.columns →
    v.chart.sourceLeftCoefficient ((LC.branch v.2.2.1).reindex.index i) = leftAtoms.whole i)
variable (rightCoefficient : ∀ i ∈ (RC.branch v.2.2.2.1).reindex.cartesian,
  (RC.branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns G.columns →
    v.chart.sourceRightCoefficient ((RC.branch v.2.2.2.1).reindex.index i) = rightAtoms.whole i)

include leftCoefficient rightCoefficient in
/-- The witness is a column of this original live leaf, before the
ordinary/exceptional split. -/
theorem literal_left_whole_present (hlive : (v.leaf exceptional firstKernel x j).Live) :
    ∃ i ∈ (v.leaf exceptional firstKernel x j).left,
      (v.literalLeftAtoms leftAtoms).whole i ≠ 0 := by
  let X := v.literalExtraction leftAtoms rightAtoms exceptional firstKernel x j
    leftCoefficient rightCoefficient
  obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.1
  rw [X.left h hh i hi] at hc
  have hr := right_ne_zero_of_mul hc
  change (v.literalLeftAtoms leftAtoms).whole i * _ * _ ≠ 0 at hr
  exact ⟨i, hi, left_ne_zero_of_mul (left_ne_zero_of_mul hr)⟩

include leftCoefficient rightCoefficient in
theorem literal_right_whole_present (hlive : (v.leaf exceptional firstKernel x j).Live) :
    ∃ i ∈ (v.leaf exceptional firstKernel x j).right,
      (v.literalRightAtoms rightAtoms).whole i ≠ 0 := by
  let X := v.literalExtraction leftAtoms rightAtoms exceptional firstKernel x j
    leftCoefficient rightCoefficient
  obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.2
  rw [X.right h hh i hi] at hc
  have hr := right_ne_zero_of_mul hc
  change star (star ((v.literalRightAtoms rightAtoms).whole i * _ * _)) ≠ 0 at hr
  rw [star_star] at hr
  exact ⟨i, hi, left_ne_zero_of_mul (left_ne_zero_of_mul hr)⟩

theorem literalLeftAtoms_scale (c : ℂ) :
    v.literalLeftAtoms (leftAtoms.scale c) = (v.literalLeftAtoms leftAtoms).scale c := by
  unfold literalLeftAtoms literalLeftOriginal
  rw [CanonicalLiteralRectangles.Atoms.scale_onAtlas,
    CanonicalLiteralRectangles.Atoms.scale_extract,
    CanonicalLiteralRectangles.Atoms.scale_onAtlas]

theorem literalRightAtoms_scale (c : ℂ) :
    v.literalRightAtoms (rightAtoms.scale c) = (v.literalRightAtoms rightAtoms).scale c := by
  unfold literalRightAtoms literalRightOriginal
  rw [CanonicalLiteralRectangles.Atoms.scale_onAtlas,
    CanonicalLiteralRectangles.Atoms.scale_extract,
    CanonicalLiteralRectangles.Atoms.scale_onAtlas]

include leftCoefficient rightCoefficient in
/-- The equality argument is the already proved atom-table normal form
of one of the six original source constructors, not a new source bound. -/
theorem literal_left_scalar_nonzero
    (core : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
    (c : ℂ) (hform : leftAtoms = core.scale c)
    (hlive : (v.leaf exceptional firstKernel x j).Live) : c ≠ 0 := by
  obtain ⟨i, _, hi⟩ := v.literal_left_whole_present leftAtoms rightAtoms
    exceptional firstKernel x j leftCoefficient rightCoefficient hlive
  rw [hform, v.literalLeftAtoms_scale core c,
    CanonicalLiteralRectangles.Atoms.scale_whole] at hi
  exact left_ne_zero_of_mul hi

include leftCoefficient rightCoefficient in
theorem literal_right_scalar_nonzero
    (core : CanonicalLiteralRectangles.Atoms (K := K) (RC.branch v.2.2.2.1).slotCount)
    (c : ℂ) (hform : rightAtoms = core.scale c)
    (hlive : (v.leaf exceptional firstKernel x j).Live) : c ≠ 0 := by
  obtain ⟨i, _, hi⟩ := v.literal_right_whole_present leftAtoms rightAtoms
    exceptional firstKernel x j leftCoefficient rightCoefficient hlive
  rw [hform, v.literalRightAtoms_scale core c,
    CanonicalLiteralRectangles.Atoms.scale_whole] at hi
  exact left_ne_zero_of_mul hi

variable (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
variable (hrightScalar : rightScalar ≠ 0)
variable (firstSign : ℝ) (hlive : (v.leaf exceptional firstKernel x j).Live)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)

/-- The two successive exact extractions are one extraction from the
stored original leaf. Both original continuous kernels are retained. -/
def literalStripExtraction : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction :=
  let X := v.literalExtraction leftAtoms rightAtoms exceptional firstKernel x j
    leftCoefficient rightCoefficient
  X.trans (X.leaf.stripColumnConstants leftScalar rightScalar hleftScalar hrightScalar)

def literalStrippedRectangles :=
  CanonicalLiteralRectangles.balancedRectangles
    ((v.literalSupportedRows leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar)
    ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹)
    ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹)
    leftBalance rightBalance hleftBalance hrightBalance
    (fun i => v.block.leftResidual (v.leftReindex.index i))
    (fun i => v.block.rightResidual (v.rightReindex.index i))
    v.leftReindex.ideal_product v.rightReindex.ideal_product
    (v.literalAllocation exceptional firstKernel x j hlive)
    (v.leaf exceptional firstKernel x j).exceptional firstSign (-firstSign)

variable (leftPoint : ∀ h ∈ (v.leaf exceptional firstKernel x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ (v.leaf exceptional firstKernel x j).left,
    WithLp.toLp 2 ((v.leaf exceptional firstKernel x j).leftFirst h i,
      (v.leaf exceptional firstKernel x j).leftSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.prime firstSign) i)
variable (rightPoint : ∀ h ∈ (v.leaf exceptional firstKernel x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ (v.leaf exceptional firstKernel x j).right,
    WithLp.toLp 2 (-(v.leaf exceptional firstKernel x j).rightFirst h i,
      (v.leaf exceptional firstKernel x j).rightSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.prime (-firstSign)) i)

/-- The new dictionary is proved on the same original rows and columns;
only the two proved constant multipliers move into the common row. -/
def literalStrippedOrdinaryBinding :
    (v.literalStripExtraction leftAtoms rightAtoms exceptional firstKernel x j
      leftCoefficient rightCoefficient leftScalar rightScalar hleftScalar hrightScalar).leaf.OrdinaryBinding
        (v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
          leftScalar rightScalar firstSign hlive leftBalance rightBalance
          hleftBalance hrightBalance) := by
  let B := v.literalOrdinaryBinding leftAtoms rightAtoms exceptional firstKernel x j
    leftCoefficient rightCoefficient firstSign hlive leftPoint rightPoint
  refine
    { rows := B.rows
      rows_zero := ?_
      left := B.left
      right := B.right
      exceptional := B.exceptional
      rowWeight := ?_
      leftCoefficient := ?_
      rightCoefficient := ?_
      leftPoint := B.leftPoint
      rightPoint := B.rightPoint }
  · intro h hh hn
    have hz := B.rows_zero h hh hn
    calc
      _ = (v.literalExtraction leftAtoms rightAtoms exceptional firstKernel x j
          leftCoefficient rightCoefficient).leaf.rowWeight h * leftScalar * star rightScalar := by
        dsimp only [literalStripExtraction, ActualHybridLeaf.ConstantAtomExtraction.trans,
          ActualHybridLeaf.stripColumnConstants, literalExtraction,
          ActualHybridLeaf.ConstantAtomExtraction.leaf, ActualHybridLeaf.withConstantAtoms]
        simp only [star_mul']
        ring
      _ = 0 := by rw [hz, zero_mul, zero_mul]
  · intro h hh
    calc
      _ = (v.literalExtraction leftAtoms rightAtoms exceptional firstKernel x j
          leftCoefficient rightCoefficient).leaf.rowWeight h * leftScalar * star rightScalar := by
        dsimp only [literalStripExtraction, ActualHybridLeaf.ConstantAtomExtraction.trans,
          ActualHybridLeaf.stripColumnConstants, literalExtraction,
          ActualHybridLeaf.ConstantAtomExtraction.leaf, ActualHybridLeaf.withConstantAtoms]
        simp only [star_mul']
        ring
      _ = ((v.literalSupportedRows leftAtoms rightAtoms).weight h *
          (v.literalSupportedRows leftAtoms rightAtoms).correlation h) * leftScalar *
            star rightScalar := by rw [B.rowWeight h hh]
      _ = _ := by
        change ((_ * _) * leftScalar) * star rightScalar =
          (((v.literalSupportedRows leftAtoms rightAtoms).weight h * leftScalar) *
            star rightScalar) * (v.literalSupportedRows leftAtoms rightAtoms).correlation h
        ring
  · intro h hh i hi
    have hc := B.leftCoefficient h hh i hi
    change leftScalar⁻¹ * _ = _
    rw [hc]
    unfold secondAllocatedLeftCoefficient
    rw [CanonicalLiteralRectangles.Atoms.scale_whole]
    ring
  · intro h hh i hi
    have hc := B.rightCoefficient h hh i hi
    change star (rightScalar⁻¹ * _) = _
    rw [star_mul', hc]
    simp only [secondAllocatedRightCoefficient,
      CanonicalLiteralRectangles.Atoms.scale_whole, star_mul']
    ring

end StoredLeaf

section ActualCalibration

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
def literalStrippedCoveredCalibrationsActive :
    (∀ r : Bool, ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
      leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).leftFrame C r).source.Calibration (σ := σ) ω ψ) ×
    (∀ r : Bool, ((v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
      leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance).rightFrame C r).source.Calibration (σ := σ) ω ψ) := by
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
  let mass := ((v.literalSupportedRowMass leftAtoms rightAtoms hmaskL hmaskR hp bound hbound
    hprofile).withColumnConstants leftScalar rightScalar).restrictRows
      (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
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
      ((v.literalRows leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar).weight
      (fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).correlation h ≠ 0)
      (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
      mass (((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).balancePlain leftBalance)
      ((leftProfiles.profiles.scale leftScalar⁻¹).balancePlain leftBalance) F parent oldMoving correction
      hcorr remaining extra leftIndex hcharactersLeft firstSupport hfirst hextra
      ((support.scale leftScalar⁻¹).balancePlain leftBalance)
      retainedScale g a₀ oldq wo cutoffExponent hscale (by change _ = CanonicalRowBall.gaussRadius retainedScale
        (v.literalLeftAtoms leftAtoms).base g hscale _; rw [hbaseLeft]; rfl)
      (by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain, CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using hcutoffPower)
      (by
        intro i hi j hj hpair
        have he := ActualGaussSource.active_gram_pair_norm_le C G _ Z a₀ hZ
          hactiveColumns i hi j hj hpair
        simpa only [CanonicalLiteralRectangles.Atoms.balancePlain, CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using he)
      (by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain, CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using hold)
      m q κ (by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain, CanonicalLiteralRectangles.Atoms.scale, hbaseLeft] using hwidth) inverse hone hroot hemb hbackground hslot
      .left j.2.1 (fun i => v.block.leftResidual (v.leftReindex.index i))
      v.leftReindex.ideal_product firstSign r j.1.val j.2.2.1.val
      (Finset.mem_filter.mp branch.property).2.2.1 hL j.2.2.1.property hordinary
  · have support : (v.literalRightAtoms rightAtoms).SupportData
        ((primeSupport A.cS ∪ firstSupport) ∪
          primeSupport (primePowerProduct v.block.primes v.block.leftMultiplicity).val) := by
      rw [v.block.common_left]
      exact rightProfiles.support
    exact v.chart.literalFrameCalibrationActive P Rchar hp hs cutoff hcutoff v.rowLabel
      ((v.literalRows leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar).weight
      (fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).correlation h ≠ 0)
      (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
      mass (((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).balancePlain rightBalance)
      ((rightProfiles.profiles.scale rightScalar⁻¹).balancePlain rightBalance) F parent oldMoving correction
      hcorr remaining extra rightIndex hcharactersRight firstSupport hfirst hextra
      ((support.scale rightScalar⁻¹).balancePlain rightBalance)
      retainedScale g a₀ oldq wo cutoffExponent hscale (by change _ = CanonicalRowBall.gaussRadius retainedScale
        (v.literalRightAtoms rightAtoms).base g hscale _; rw [hbaseRight]; rfl)
      (by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain, CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using hcutoffPower)
      (by
        intro i hi j hj hpair
        have he := ActualGaussSource.active_gram_pair_norm_le C G _ Z a₀ hZ
          hactiveColumns i hi j hj hpair
        simpa only [CanonicalLiteralRectangles.Atoms.balancePlain, CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using he)
      (by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain, CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using hold)
      m q κ (by simpa only [CanonicalLiteralRectangles.Atoms.balancePlain, CanonicalLiteralRectangles.Atoms.scale, hbaseRight] using hwidth) inverse hone hroot hemb hbackground hslot
      .right j.2.1 (fun i => v.block.rightResidual (v.rightReindex.index i))
      v.rightReindex.ideal_product (-firstSign) r j.1.val j.2.2.2.val
      (Finset.mem_filter.mp branch.property).2.2.2 hL j.2.2.2.property hordinary

end ActualCalibration

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literal_left_scalar_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literal_right_scalar_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalStripExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalStrippedOrdinaryBinding
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalStrippedCoveredCalibrationsActive
