import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralCovered
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantProfileExtraction

set_option linter.unusedSectionVars false

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

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

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
variable (v : (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey s) LC RC)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (exceptional : s.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.AllocationKey v))
variable (leftCoefficient : ∀ i ∈ (LC.branch v.2.2.1).reindex.cartesian,
  (LC.branch v.2.2.1).reindex.index i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftColumns G.columns →
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).sourceLeftCoefficient ((LC.branch v.2.2.1).reindex.index i) = leftAtoms.whole i)
variable (rightCoefficient : ∀ i ∈ (RC.branch v.2.2.2.1).reindex.cartesian,
  (RC.branch v.2.2.2.1).reindex.index i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightColumns G.columns →
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).sourceRightCoefficient ((RC.branch v.2.2.2.1).reindex.index i) = rightAtoms.whole i)

include leftCoefficient rightCoefficient in
/-- The witness is a column of this original live leaf, before the
ordinary/exceptional split. -/
theorem literal_left_whole_present (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).Live) :
    ∃ i ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).left,
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).whole i ≠ 0 := by
  sorry

include leftCoefficient rightCoefficient in
theorem literal_right_whole_present (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).Live) :
    ∃ i ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).right,
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).whole i ≠ 0 := by
  sorry

theorem literalLeftAtoms_scale (c : ℂ) :
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) (leftAtoms.scale c) = ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).scale c := by
  sorry

theorem literalRightAtoms_scale (c : ℂ) :
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) (rightAtoms.scale c) = ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).scale c := by
  sorry

include leftCoefficient rightCoefficient in
/-- The equality argument is the already proved atom-table normal form
of one of the six original source constructors, not a new source bound. -/
theorem literal_left_scalar_nonzero
    (core : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
    (c : ℂ) (hform : leftAtoms = core.scale c)
    (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).Live) : c ≠ 0 := by
  sorry

include leftCoefficient rightCoefficient in
theorem literal_right_scalar_nonzero
    (core : CanonicalLiteralRectangles.Atoms (K := K) (RC.branch v.2.2.2.1).slotCount)
    (c : ℂ) (hform : rightAtoms = core.scale c)
    (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).Live) : c ≠ 0 := by
  sorry

variable (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
variable (hrightScalar : rightScalar ≠ 0)
variable (firstSign : ℝ) (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).Live)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)

/-- The two successive exact extractions are one extraction from the
stored original leaf. Both original continuous kernels are retained. -/
def literalStripExtraction : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).ConstantAtomExtraction :=
  let X := (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalExtraction v) leftAtoms rightAtoms exceptional firstKernel x j
    leftCoefficient rightCoefficient
  X.trans (X.leaf.stripColumnConstants leftScalar rightScalar hleftScalar hrightScalar)

def literalStrippedRectangles :=
  CanonicalLiteralRectangles.balancedRectangles
    (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRows v) leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar)
    (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).scale leftScalar⁻¹)
    (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).scale rightScalar⁻¹)
    leftBalance rightBalance hleftBalance hrightBalance
    (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).index i))
    (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i))
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).ideal_product (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).ideal_product
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalAllocation v) exceptional firstKernel x j hlive)
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).exceptional firstSign (-firstSign)

variable (leftPoint : ∀ h ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).left,
    WithLp.toLp 2 (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).leftFirst h i,
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).leftSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.prime firstSign) i)
variable (rightPoint : ∀ h ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).right,
    WithLp.toLp 2 (-((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).rightFirst h i,
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional firstKernel x j).rightSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.prime (-firstSign)) i)

/-- The new dictionary is proved on the same original rows and columns;
only the two proved constant multipliers move into the common row. -/
def literalStrippedOrdinaryBinding :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalStripExtraction v) leftAtoms rightAtoms exceptional firstKernel x j
      leftCoefficient rightCoefficient leftScalar rightScalar hleftScalar hrightScalar).leaf.OrdinaryBinding
        ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalStrippedRectangles v) leftAtoms rightAtoms exceptional firstKernel x j
          leftScalar rightScalar firstSign hlive leftBalance rightBalance
          hleftBalance hrightBalance) := by
  let B := (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalOrdinaryBinding v) leftAtoms rightAtoms exceptional firstKernel x j
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
      _ = ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalExtraction v) leftAtoms rightAtoms exceptional firstKernel x j
          leftCoefficient rightCoefficient).leaf.rowWeight h * leftScalar * star rightScalar := by
        dsimp only [literalStripExtraction, ActualHybridLeaf.ConstantAtomExtraction.trans,
          ActualHybridLeaf.stripColumnConstants, literalExtraction,
          ActualHybridLeaf.ConstantAtomExtraction.leaf, ActualHybridLeaf.withConstantAtoms]
        simp only [star_mul']
        ring
      _ = 0 := by rw [hz, zero_mul, zero_mul]
  · intro h hh
    calc
      _ = ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalExtraction v) leftAtoms rightAtoms exceptional firstKernel x j
          leftCoefficient rightCoefficient).leaf.rowWeight h * leftScalar * star rightScalar := by
        dsimp only [literalStripExtraction, ActualHybridLeaf.ConstantAtomExtraction.trans,
          ActualHybridLeaf.stripColumnConstants, literalExtraction,
          ActualHybridLeaf.ConstantAtomExtraction.leaf, ActualHybridLeaf.withConstantAtoms]
        simp only [star_mul']
        ring
      _ = (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRows v) leftAtoms rightAtoms).weight h *
          ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRows v) leftAtoms rightAtoms).correlation h) * leftScalar *
            star rightScalar := by rw [B.rowWeight h hh]
      _ = _ := by
        change ((_ * _) * leftScalar) * star rightScalar =
          ((((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRows v) leftAtoms rightAtoms).weight h * leftScalar) *
            star rightScalar) * ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRows v) leftAtoms rightAtoms).correlation h
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


end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStepV2

