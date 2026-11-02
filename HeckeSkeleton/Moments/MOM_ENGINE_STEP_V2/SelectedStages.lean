import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalPoolStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.DirectPreparation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourcePredicates

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# The actual direct and one-pool second stages

The same original first common and complementary divisor determine
each retained row endpoint before the second common label is formed.
The main branch pays its sixth-power prime insertion, while the three
valuation branches retain their literal original error rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  selectedPrincipal selectedComplex selectedNormOneSpace selectedNormOneBorel
  selectedInfinityUnitSpace selectedInfinityUnitBorel selectedLocalUnitSpace selectedLocalUnitBorel

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

namespace SelectedSource

variable (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)

def supportError : ℝ := (selectedBox c frame).error

def leftDirectGeometry (DE : (firstSource request frequency).CommonLabel)
    (D : (((firstSource request frequency).block DE).mask
      (firstSource request frequency).mask).powerset) :
    OriginalNominalGeometry (K := K) (parameters request frequency) request.base
      (recipeInductionSigma c) :=
  OriginalNominalGeometry.canonicalDirect
    (((firstSource request frequency).block DE).literalLeftCoordinates D.val)
    (selectedBox c frame).error (zero_lt_one.trans (base_gt_one request))
    (selectedBox c frame).error_pos.le

def rightDirectGeometry (DE : (firstSource request frequency).CommonLabel)
    (D : (((firstSource request frequency).block DE).mask
      (firstSource request frequency).mask).powerset) :
    OriginalNominalGeometry (K := K) (parameters request frequency) request.base
      (recipeInductionSigma c) :=
  OriginalNominalGeometry.canonicalDirect
    (((firstSource request frequency).block DE).literalRightCoordinates D.val)
    (selectedBox c frame).error (zero_lt_one.trans (base_gt_one request))
    (selectedBox c frame).error_pos.le

theorem directRows
    (DE : (firstSource request frequency).CommonLabel)
    (D : (((firstSource request frequency).block DE).mask
      (firstSource request frequency).mask).powerset) :
    (∀ h ∈ ((firstSource request frequency).pieces DE D).leftData.rows,
      (TargetArithmetic.arithmetic c).exteriorNorm (originalFrequencyIdeal h) ≤
        (leftDirectGeometry request frequency DE D).retainedScale *
          request.base ^ (leftDirectGeometry request frequency DE D).enlargement) ∧
    (∀ h ∈ ((firstSource request frequency).pieces DE D).rightData.rows,
      (TargetArithmetic.arithmetic c).exteriorNorm (originalFrequencyIdeal h) ≤
        (rightDirectGeometry request frequency DE D).retainedScale *
          request.base ^ (rightDirectGeometry request frequency DE D).enlargement) := by
  sorry

/-- Both independent first divisor/phase sums are retained by this
actual second transform. All kernels are the original row-ball kernels. -/
def directStages : (firstSource request frequency).SecondStages
    (E := ℝ) (hDiff := TargetArithmetic.different c) := fun DE D => {
  left := fun S χ => ActualGaussStage.literalSectorStage
    (hΓ := actualSixthUnits_are_sixth (places K c))
    (μv := TargetArithmetic.localMeasures (K := K))
    (hDiff := TargetArithmetic.different c) (ν := TargetArithmetic.finiteMeasure (K := K))
    (probeData K c) (selectedBox c frame).delta (selectedBox c frame).tilt_pos
    (selectedBox c frame).tilt_le_half
    (((firstSource request frequency).pieces DE D).leftData.directSource
      (((firstSource request frequency).pieces DE D).leftDivisorCoefficient S χ))
    (leftDirectGeometry request frequency DE D).retainedScale request.base
    (leftDirectGeometry request frequency DE D).enlargement
    (leftDirectGeometry request frequency DE D).retainedScale_pos
    (zero_lt_one.trans (base_gt_one request))
    ((selectedBox c frame).secondCutoff request.base)
    ((selectedBox c frame).secondCutoff_ge_one (base_gt_one request).le)
    (directRows request frequency DE D).1
  right := fun S χ => ActualGaussStage.literalSectorStage
    (hΓ := actualSixthUnits_are_sixth (places K c))
    (μv := TargetArithmetic.localMeasures (K := K))
    (hDiff := TargetArithmetic.different c) (ν := TargetArithmetic.finiteMeasure (K := K))
    (probeData K c) (selectedBox c frame).delta (selectedBox c frame).tilt_pos
    (selectedBox c frame).tilt_le_half
    (((firstSource request frequency).pieces DE D).rightData.directSource
      (((firstSource request frequency).pieces DE D).rightDivisorCoefficient S χ))
    (rightDirectGeometry request frequency DE D).retainedScale request.base
    (rightDirectGeometry request frequency DE D).enlargement
    (rightDirectGeometry request frequency DE D).retainedScale_pos
    (zero_lt_one.trans (base_gt_one request))
    ((selectedBox c frame).secondCutoff request.base)
    ((selectedBox c frame).secondCutoff_ge_one (base_gt_one request).le)
    (directRows request frequency DE D).2 }

theorem pooledRows
    (DE : (pooledSource request frequency).CommonLabel)
    (D : (((pooledSource request frequency).block DE).mask
      (pooledSource request frequency).mask).powerset)
    (S : divisorPool ((pooledSource request frequency).pools DE D).rightData.columns
      (fun j => (((pooledSource request frequency).pools DE D).rightData.ideal j).val)) :
    (∀ h ∈ (((pooledSource request frequency).pools DE D).divisorPools.leftData S).rows,
      (TargetArithmetic.arithmetic c).exteriorNorm (originalFrequencyIdeal h) ≤
        (((pooledSource request frequency).block DE).literalLeftCoordinates D.val).canonicalRetainedScale
          (parameters request frequency) request.base (selectedBox c frame).error) ∧
    (∀ h ∈ (((pooledSource request frequency).pools DE D).divisorPools.rightData S).rows,
      (TargetArithmetic.arithmetic c).exteriorNorm (originalFrequencyIdeal h) ≤
        (((pooledSource request frequency).block DE).literalRightCoordinates D.val).canonicalRetainedScale
          (parameters request frequency) request.base (selectedBox c frame).error) := by
  sorry

/-- One pool supplies main, valuation-one, valuation-six and
valuation-seven sources on each independent side. -/
def pooledStages : (pooledSource request frequency).SecondStages
    (E := ℝ) (hDiff := TargetArithmetic.different c) := fun DE D => {
  left := fun S χ =>
    (((pooledSource request frequency).pools DE D).divisorPools.leftData S).literalCanonicalStages
      (hΓ := actualSixthUnits_are_sixth (places K c))
      (μv := TargetArithmetic.localMeasures (K := K))
      (hDiff := TargetArithmetic.different c) (ν := TargetArithmetic.finiteMeasure (K := K))
      (((pooledSource request frequency).pools DE D).leftDivisorCoefficient S χ)
      (probeData K c) (parameters request frequency)
      (((pooledSource request frequency).block DE).literalLeftCoordinates D.val)
      (selectedBox c frame).error (selectedBox c frame).error_pos.le
      (selectedBox c frame).step_pos (pooledRows request frequency DE D S).1
      (selectedBox c frame).delta (selectedBox c frame).tilt_pos (selectedBox c frame).tilt_le_half
      ((selectedBox c frame).secondCutoff request.base)
      ((selectedBox c frame).secondCutoff_ge_one (base_gt_one request).le)
  right := fun S χ =>
    (((pooledSource request frequency).pools DE D).divisorPools.rightData S).literalCanonicalStages
      (hΓ := actualSixthUnits_are_sixth (places K c))
      (μv := TargetArithmetic.localMeasures (K := K))
      (hDiff := TargetArithmetic.different c) (ν := TargetArithmetic.finiteMeasure (K := K))
      (((pooledSource request frequency).pools DE D).rightDivisorCoefficient S χ)
      (probeData K c) (parameters request frequency)
      (((pooledSource request frequency).block DE).literalRightCoordinates D.val)
      (selectedBox c frame).error (selectedBox c frame).error_pos.le
      (selectedBox c frame).step_pos (pooledRows request frequency DE D S).2
      (selectedBox c frame).delta (selectedBox c frame).tilt_pos (selectedBox c frame).tilt_le_half
      ((selectedBox c frame).secondCutoff request.base)
      ((selectedBox c frame).secondCutoff_ge_one (base_gt_one request).le) }

def directPrepared := (directStages request frequency).prepared
def pooledPrepared := (pooledStages request frequency).supported.gated

end SelectedSource
end HeckeSkeleton.Moments.EngineStepV2
