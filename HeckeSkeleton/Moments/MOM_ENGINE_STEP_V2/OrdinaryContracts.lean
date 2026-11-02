import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinarySeedAtomBinding

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N1: the original individual atom and occurrence dictionaries

The statement concerns one actual raw leaf, its two original centered
rectangles and their genuine two support extractions. It selects no
child or capacity. The plain quotient scales and surviving lengths are
fixed to the original occurrences, not merely to an equivalent whole
polynomial. Paper: lines 2800--2820 and 2908--2925.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

structure OrdinarySeed (packet : RawLeafPacket call p) where
  ordinary : OrdinaryData packet
  phases : OriginalPhaseData packet
  occurrences : OriginalOccurrenceData ordinary
  atoms : OriginalAtomBinding ordinary phases occurrences
  reference : NonzeroIdeal K
  reference_mem : reference ∈ pairedRows call.node.data call.node.parameters call.base
  plain_scales : ∀ side rectangle plain,
    ordinary.quotientScale side rectangle plain =
      occurrences.plainScale side rectangle plain
  residual_count : ∀ side,
    (ordinary.originalAllocation side).keep.card = ordinary.residualSlotCount side
  lengths : ∀ side (i : Fin (ordinary.originalAllocation side).keep.card),
    ordinary.residualLength side (Fin.cast (residual_count side) i) = occurrences.length side i

/-- N1 supplies only the original single-column dictionary and its
literal occurrence/scalar metadata. The independent residual mask
expansion is the next statement. -/
def OriginalAtomTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (packet : RawLeafPacket call p), packet.Realizes →
    Nonempty (OrdinarySeed packet)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
