module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual surviving original occurrences of a raw leaf

The count equalities follow from the source trace. They give the
literal composition of the first extraction, the second extraction
and the independent allocation. No new slot is selected, including
when either extraction leaves an empty list.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem realizes_originalRows (hpacket : packet.Realizes) : call.Active := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact htrace.first.active

theorem realizes_firstCount (hpacket : packet.Realizes) (side : Bool) :
    (packet.firstBranch side).keep.card = (packet.firstAtlas side).slotCount := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  cases side with
  | false => exact (hraw (raw.index j).val.1.1).1.count (raw.index j).val.1.2.2.2.1
  | true => exact (hraw (raw.index j).val.1.1).2.count (raw.index j).val.1.2.2.2.2.1

/-- The ordinary occurrence dictionary only fills the two exact count
proofs; all its index and scalar functions are the public definitions. -/
def ordinaryOccurrences (hpacket : packet.Realizes) (O : OrdinaryData packet) :
    OriginalOccurrenceData O where
  first_count := packet.realizes_firstCount hpacket
  second_count side := by cases side <;> rfl

/-- One original paired row, used only to identify the original
row-independent plain profiles. -/
def originalReference (hpacket : packet.Realizes) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  (packet.realizes_originalRows hpacket).choose

theorem originalReference_mem (hpacket : packet.Realizes) :
    packet.originalReference hpacket ∈ pairedRows call.node.data call.node.parameters call.base :=
  (packet.realizes_originalRows hpacket).choose_spec

end RawLeafPacket

namespace OriginalOccurrenceData

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (D : OriginalOccurrenceData O)

private theorem slotIndex_injective {k : ℕ} (keep : Finset (Fin k)) :
    Function.Injective (SlotRestriction.index keep) := by
  intro i j hij
  apply keep.equivFin.symm.injective
  exact Subtype.ext hij

theorem firstIndex_injective (side : Bool) : Function.Injective (D.firstIndex side) := by
  intro i j hij
  have h := slotIndex_injective (packet.firstBranch side).keep hij
  have hval := congrArg (fun x : Fin (packet.firstBranch side).keep.card => x.val) h
  exact Fin.ext hval

theorem secondIndex_injective (side : Bool) : Function.Injective (D.secondIndex side) := by
  intro i j hij
  have hfirst := D.firstIndex_injective side hij
  have hsecond := slotIndex_injective (packet.secondBranch side).keep hfirst
  have hval := congrArg (fun x : Fin (packet.secondBranch side).keep.card => x.val) hsecond
  exact Fin.ext hval

theorem remainingIndex_injective (side : Bool) :
    Function.Injective (D.remainingIndex side) := by
  intro i j hij
  exact slotIndex_injective (O.originalAllocation side).keep
    (D.secondIndex_injective side hij)

theorem beforeLength_pos (side : Bool) (i : Fin (O.originalSlotCount side)) :
    0 < D.beforeLength side i :=
  (call.localizedData.geometry.slots (D.secondIndex side i)).length_pos

theorem length_pos (side : Bool) (i : Fin (O.originalAllocation side).keep.card) :
    0 < D.length side i :=
  (call.localizedData.geometry.slots (D.remainingIndex side i)).length_pos

theorem beforePlainScale_pos (side rectangle plain : Bool) :
    0 < D.beforePlainScale side rectangle plain := by
  have horiginal : 0 < call.originalPlainScale rectangle plain := by
    unfold Call.originalPlainScale
    split_ifs <;> exact Real.rpow_pos_of_pos call.base_pos _
  exact div_pos (div_pos horiginal (idealNorm_pos K _)) (idealNorm_pos K _)

theorem plainScale_pos (side rectangle plain : Bool) :
    0 < D.plainScale side rectangle plain :=
  div_pos (D.beforePlainScale_pos side rectangle plain) (idealNorm_pos K _)

end OriginalOccurrenceData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryOccurrences
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.remainingIndex_injective
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.plainScale_pos
