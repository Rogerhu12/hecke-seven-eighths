import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalPhaseData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual two occurrence extractions and their original scalars

Only the atlas count equality is supplied. Every surviving occurrence
map, every quotient scale and each frozen scalar is then computed from
those same original support branches. The independent inner divisor
allocation is the one already stored in the ordinary leaf.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def firstColumns : Bool → Finset packet.second.physical.Column
  | false => packet.leftCover.fibre packet.key.2.2.1.val
  | true => packet.rightCover.fibre packet.key.2.2.2.1.val

def firstAtlas : (side : Bool) →
    SourceCartesianAtlas (packet.firstColumns side) packet.second.physical.source.ideal
  | false => packet.leftCover.branch packet.key.2.2.1
  | true => packet.rightCover.branch packet.key.2.2.2.1

def secondIdeal (side : Bool) : Ideal (𝓞 K) :=
  if side then packet.key.1.val.2 else packet.key.1.val.1

def secondSupportKey : (side : Bool) →
    (packet.firstAtlas side).labels (primeSupport packet.key.1.val.1)
      (packet.secondIdeal side)
  | false => packet.key.2.2.2.2.2.1
  | true => packet.key.2.2.2.2.2.2

def secondBranch (side : Bool) :=
  (packet.firstAtlas side).branch (primeSupport packet.key.1.val.1)
    (packet.secondIdeal side) (packet.secondSupportKey side)

end RawLeafPacket

namespace OrdinaryData

variable {packet : RawLeafPacket call p} (O : OrdinaryData packet)

def originalSlotCount (_O : OrdinaryData packet) : Bool → ℕ
  | false => packet.leaf.leftSlots
  | true => packet.leaf.rightSlots

def originalAllocation : (side : Bool) → ActualColumnAllocation K (O.originalSlotCount side)
  | false => (O.leftFrame false).source.allocation
  | true => (O.rightFrame false).source.allocation

end OrdinaryData

/-- These equalities merely identify the original finite occurrence
counts; all surviving index maps are computed below from actual keeps. -/
structure OriginalOccurrenceData {packet : RawLeafPacket call p} (O : OrdinaryData packet) where
  first_count : ∀ side, (packet.firstBranch side).keep.card =
    (packet.firstAtlas side).slotCount
  second_count : ∀ side, (packet.secondBranch side).keep.card = O.originalSlotCount side

namespace OriginalOccurrenceData

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (D : OriginalOccurrenceData O)

def firstIndex (side : Bool) (i : Fin (packet.firstAtlas side).slotCount) :
    Fin call.localizedData.geometry.slotCount :=
  SlotRestriction.index (packet.firstBranch side).keep (Fin.cast (D.first_count side).symm i)

def secondIndex (side : Bool) (i : Fin (O.originalSlotCount side)) :
    Fin call.localizedData.geometry.slotCount :=
  D.firstIndex side (SlotRestriction.index (packet.secondBranch side).keep
    (Fin.cast (D.second_count side).symm i))

def remainingIndex (side : Bool) (i : Fin (O.originalAllocation side).keep.card) :
    Fin call.localizedData.geometry.slotCount :=
  D.secondIndex side (SlotRestriction.index (O.originalAllocation side).keep i)

def beforeLength (side : Bool) (i : Fin (O.originalSlotCount side)) : ℝ :=
  call.originalLength (D.secondIndex side i)

def length (side : Bool) (i : Fin (O.originalAllocation side).keep.card) : ℝ :=
  call.originalLength (D.remainingIndex side i)

def beforePlainScale (_D : OriginalOccurrenceData O) (side rectangle plain : Bool) : ℝ :=
  packet.firstPlainScale side rectangle plain /
    idealNorm K (if plain then (packet.secondBranch side).plainDivisor₂
      else (packet.secondBranch side).plainDivisor₁)

def plainScale (side rectangle plain : Bool) : ℝ :=
  D.beforePlainScale side rectangle plain /
    idealNorm K ((O.originalAllocation side).plainDivisor
      (if plain then Fin.succ 0 else 0))

/-- The canonical unscaled profile has the exact two-tilt norm power.
Its original scale dependence is kept in the explicit external scalar. -/
def normPower (_D : OriginalOccurrenceData O) : ℝ := -1 + 2 * p.tilt

def firstSlotWeight (side : Bool) (i : Fin (packet.firstAtlas side).slotCount)
    (q : HeightOneSpectrum (𝓞 K)) : ℂ :=
  let original := D.firstIndex side i
  let x := (Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength original
  call.originalSlotWeight original q * ((x ^ D.normPower : ℝ) : ℂ)

def beforeSlotWeight (side : Bool) (i : Fin (O.originalSlotCount side))
    (q : HeightOneSpectrum (𝓞 K)) : ℂ :=
  let original := D.secondIndex side i
  let x := (Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength original
  call.originalSlotWeight original q * ((x ^ D.normPower : ℝ) : ℂ)

/-- This is the second actual frozen common product, before the
independent inner allocation and before residual mask expansion. -/
def secondCommonScalar (phases : OriginalPhaseData packet) (side : Bool) : ℂ :=
  (packet.secondBranch side).bareCommonScalar
    (phases.characters false (D.firstIndex side)) call.base
    (fun i => call.originalLength (D.firstIndex side i)) (D.firstSlotWeight side)

/-- The same explicit normalizer is shared by every passive label and
both comparison rectangles. Their new finite scalars remain in the
source row weight and in the actual allocation's frozen scalar. -/
def normalizer (phases : OriginalPhaseData packet) (side : Bool) : ℂ :=
  packet.firstExternalScalar side * D.secondCommonScalar phases side

end OriginalOccurrenceData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
