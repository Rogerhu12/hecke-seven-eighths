import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The same original leaf after its two residual mask expansions

The two passive keys and the two original comparison bits occur exactly
once. Every source has the original physical row type and the actual
allocation computed on its restored smooth carrier. The contracts
separately fix its single coefficients, original scalars and global
profiles; this record supplies neither capacity nor a mass estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}

structure RefinementData (O : OrdinaryData packet) (input : ProfileInput call) where
  support : O.PassiveSupport input
  source : ∀ side, support.labels side → Bool →
    ActualAllocatedSource (Arithmetic.data c) EngineParameter
      O.rows.live (O.residualSlotCount side)
  allocation : ∀ side a rectangle, (source side a rectangle).allocation =
    PassiveAllocation.allocation (support.carrier side) O.passiveMask a
  base_eq : ∀ side a rectangle, (source side a rectangle).base = call.base
  normalizer : ∀ side, support.labels side → Bool → ℂ

namespace RefinementData

variable {O : OrdinaryData packet} (R : RefinementData O input)

abbrev Label := R.support.Label

def leftSource (b : R.Label) := R.source false b.1 b.2.2.1

def rightSource (b : R.Label) := R.source true b.2.1 b.2.2.2

def leftNormalizer (b : R.Label) : ℂ := R.normalizer false b.1 b.2.2.1

def rightNormalizer (b : R.Label) : ℂ := R.normalizer true b.2.1 b.2.2.2

def outer (b : R.Label) : ℝ := R.support.outer b

theorem outer_nonneg (b : R.Label) : 0 ≤ R.outer b := R.support.outer_nonneg b

/-- Pointwise source pairs retain the original parent normalization.
The ordinary domination contract uses this exact finite collection. -/
def sourcePair (b : R.Label) (ξ : EngineParameter) : ℝ :=
  (Real.sqrt (‖R.leftNormalizer b‖ ^ 2 *
      (R.leftSource b).energy (σ := Arithmetic.embedding c) ξ) *
    Real.sqrt (‖R.rightNormalizer b‖ ^ 2 *
      (R.rightSource b).energy (σ := Arithmetic.embedding c) ξ)) /
    call.base ^ (call.node.parameters.m + call.node.parameters.q)

/-- N3 supplies actual single-atom arithmetic calibrations on the same
sources. No independently selected child data occur in this record. -/
structure Calibrations where
  side : ∀ s a r, OriginalCalibration call (R.source s a r)

namespace Calibrations

variable {R} (C : R.Calibrations)

/-- This is only an assembly input. N4 and N6 construct each entry by
`SideGeometryData.normalization` from the original length ledger and
its individual profile/prime estimates. No task chooses this record as
a final normalized-output oracle. -/
structure Capacities where
  side : ∀ s a r, (C.side s a r).calibration.NormalizedCapacityData

end Calibrations
end RefinementData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
