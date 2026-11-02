import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedLiteralInputs
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralCoveredProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceProduction

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# Physical coordinates shared by every normalized source branch

The packet stores the original source, first nominal coordinates and
covered allocation. The second stage is computed from these coordinates,
using the same canonical classifier as the source expansion. The two
literal occurrence descriptors retain their original atlas branches.
No normalized child, capacity choice or moment inequality is a field.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

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

local instance packetCircleFintype : Fintype ((PUnit × PUnit) →* Circle) :=
  Fintype.ofFinite _

structure SelectedStageMetadata (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) where
  Column : Type
  source : ActualGaussSource (TargetArithmetic.context c) Column
  firstGeometry : OriginalNominalGeometry (K := K)
    (SelectedSource.parameters request frequency) request.base (recipeInductionSigma c)
  row_bound : ∀ h ∈ source.rows,
    (TargetArithmetic.arithmetic c).exteriorNorm (originalFrequencyIdeal h) ≤
      firstGeometry.retainedScale * request.base ^ firstGeometry.enlargement

namespace SelectedStageMetadata

variable {request : Request c frame Cp Hp hCp hminimum hHp} {frequency : ℝ × ℝ}

def stage (p : SelectedStageMetadata request frequency) :=
  ActualGaussStage.gated (ActualGaussStage.supported
    (ActualGaussStage.literalSectorStage
      (hΓ := actualSixthUnits_are_sixth (places K c))
      (μv := TargetArithmetic.localMeasures (K := K))
      (hDiff := TargetArithmetic.different c) (ν := TargetArithmetic.finiteMeasure (K := K))
      (probeData K c) (selectedBox c frame).delta (selectedBox c frame).tilt_pos
      (selectedBox c frame).tilt_le_half p.source p.firstGeometry.retainedScale
      request.base p.firstGeometry.enlargement p.firstGeometry.retainedScale_pos
      (zero_lt_one.trans (SelectedSource.base_gt_one request))
      ((selectedBox c frame).secondCutoff request.base)
      ((selectedBox c frame).secondCutoff_ge_one (SelectedSource.base_gt_one request).le)
      p.row_bound))

end SelectedStageMetadata

structure SelectedLeafPacket (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (leaf : ActualHybridLeaf K (ActualSIntegerOrbit K (places K c)) ℝ ℝ) where
  physical : SelectedStageMetadata request frequency
  cover : SourceCartesianCover physical.source.columns physical.source.ideal
  key : ActualGaussStage.CoveredClassKey physical.stage cover cover
  exceptional : physical.stage.CoverHybridPredicates cover cover
  firstKernel : SchwartzMap ℝ ℂ
  location : physical.Column → ℝ
  allocation : ActualGaussStage.CoveredClassKey.AllocationKey key
  live : (ActualGaussStage.CoveredClassKey.leaf key exceptional firstKernel location allocation).Live
  firstSign : ℝ
  leftInput : LiteralInput (SelectedSource.seed request frequency) (cover.branch key.2.2.1)
  rightInput : LiteralInput (SelectedSource.seed request frequency) (cover.branch key.2.2.2.1)
  phase_eq : leftInput.phases = rightInput.phases
  choice : CanonicalLiteralPassiveSource.PhaseChoice leftInput.phases (TargetArithmetic.context c)
  firstKernel_eq : firstKernel = leaf.firstKernel
  secondKernel_eq : (ActualGaussStage.CoveredClassKey.chart key).kernel = leaf.secondKernel

namespace SelectedLeafPacket

variable {request : Request c frame Cp Hp hCp hminimum hHp} {frequency : ℝ × ℝ}
variable {leaf : ActualHybridLeaf K (ActualSIntegerOrbit K (places K c)) ℝ ℝ}
variable (p : SelectedLeafPacket request frequency leaf)

/-- The actual second common ideals and divided-frequency pattern are
inserted into the original first geometry without changing its scale. -/
def geometry : OriginalNominalGeometry (K := K)
    (SelectedSource.parameters request frequency) request.base (recipeInductionSigma c) :=
  let block := ActualGaussStage.CoveredClassKey.block p.key
  let chart := ActualGaussStage.CoveredClassKey.chart p.key
  OriginalNominalGeometry.atSecondPattern p.physical.firstGeometry
    block.primes block.leftMultiplicity block.rightMultiplicity
    block.left_positive block.right_positive
    (SecondBlockProfileChart.originalNonunitPattern chart ∅
      ((selectedBox c frame).secondCutoff request.base)
      ((selectedBox c frame).secondCutoff_ge_one (SelectedSource.base_gt_one request).le)
      (ActualGaussStage.CoveredClassKey.rowLabel p.key))

/-- These are the actual stored Fourier kernels and full physical
weight. All first/divisor/pool/fibre factors have already been included
by the source expansion, and enter the normalized measure once. -/
def firstMeasureKernel := leaf.firstKernel
def secondMeasureKernel := leaf.secondKernel
def outerWeight : ℝ := leaf.weight

end SelectedLeafPacket
end HeckeSkeleton.Moments.EngineStepV2
