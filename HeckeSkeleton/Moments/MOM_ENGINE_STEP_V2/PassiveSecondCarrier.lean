import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCanonicalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCoverOrigin

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The literal second residual carriers and surviving occurrences

The finite-carrier transports in the base atlas constructor affect only
its proof fields. Their projections retain the actual plain residuals
and prime-live supports. Composing those projections with the first
cover and the old inner keep gives the exact original child carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace PassiveSecondCarrier

section Generic

variable {A : SArithmeticData K} {ι : Type*} {k : ℕ}
variable {columns otherColumns : Finset ι} {ideal : ι → A.Exterior}

private theorem carrier_cast_plain₁ (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k = CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).plain₁ = R.plain₁ := by
  cases h
  rfl

private theorem carrier_cast_plain₂ (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k = CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).plain₂ = R.plain₂ := by
  cases h
  rfl

private theorem carrier_cast_slots (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k = CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).slots = R.slots := by
  cases h
  rfl

private theorem label_plain₁ (R : CartesianSourceReindex columns ideal k)
    (P : Finset (Ideal (𝓞 K))) (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P)
    (J : ι → A.Exterior)
    (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P) :
    (R.supportResidualLabelBranch P b J hJ).plain₁ =
      SupportCartesian.plainResidual R.plain₁ P b.plainExtract₁ := by
  unfold CartesianSourceReindex.supportResidualLabelBranch
  exact carrier_cast_plain₁ (R.supportExtractionLabel_fibre P b).symm _ _

private theorem label_plain₂ (R : CartesianSourceReindex columns ideal k)
    (P : Finset (Ideal (𝓞 K))) (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P)
    (J : ι → A.Exterior)
    (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P) :
    (R.supportResidualLabelBranch P b J hJ).plain₂ =
      SupportCartesian.plainResidual R.plain₂ P b.plainExtract₂ := by
  unfold CartesianSourceReindex.supportResidualLabelBranch
  exact carrier_cast_plain₂ (R.supportExtractionLabel_fibre P b).symm _ _

private theorem label_slots (R : CartesianSourceReindex columns ideal k)
    (P : Finset (Ideal (𝓞 K))) (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P)
    (J : ι → A.Exterior)
    (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P) :
    (R.supportResidualLabelBranch P b J hJ).slots =
      fun j => SupportCartesian.primeLive (R.slots (SlotRestriction.index b.keep j)) P := by
  unfold CartesianSourceReindex.supportResidualLabelBranch
  exact carrier_cast_slots (R.supportExtractionLabel_fibre P b).symm _ _

variable (T : SourceCartesianAtlas columns ideal)
variable (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (J : ι → A.Exterior)
variable (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P)
variable (a : T.labels P D)

theorem residualReindex_plain₁ :
    (T.residualReindex P D J hJ a).plain₁ =
      SupportCartesian.plainResidual T.reindex.plain₁ P (T.branch P D a).plainExtract₁ := by
  unfold SourceCartesianAtlas.residualReindex
  exact (carrier_cast_plain₁ (T.commonFibre_eq_full P D a).symm _ _).trans
    ((carrier_cast_plain₁ (congrArg (fun key => columns.filter
      (fun i => T.reindex.supportExtractionLabel P i = key)) (T.branch_key P D a)) _ _).trans
        (label_plain₁ T.reindex P (T.branch P D a) J hJ))

theorem residualReindex_plain₂ :
    (T.residualReindex P D J hJ a).plain₂ =
      SupportCartesian.plainResidual T.reindex.plain₂ P (T.branch P D a).plainExtract₂ := by
  unfold SourceCartesianAtlas.residualReindex
  exact (carrier_cast_plain₂ (T.commonFibre_eq_full P D a).symm _ _).trans
    ((carrier_cast_plain₂ (congrArg (fun key => columns.filter
      (fun i => T.reindex.supportExtractionLabel P i = key)) (T.branch_key P D a)) _ _).trans
        (label_plain₂ T.reindex P (T.branch P D a) J hJ))

theorem residualReindex_slots :
    (T.residualReindex P D J hJ a).slots = fun j =>
      SupportCartesian.primeLive
        (T.reindex.slots (SlotRestriction.index (T.branch P D a).keep j)) P := by
  unfold SourceCartesianAtlas.residualReindex
  exact (carrier_cast_slots (T.commonFibre_eq_full P D a).symm _ _).trans
    ((carrier_cast_slots (congrArg (fun key => columns.filter
      (fun i => T.reindex.supportExtractionLabel P i = key)) (T.branch_key P D a)) _ _).trans
        (label_slots T.reindex P (T.branch P D a) J hJ))

end Generic
end PassiveSecondCarrier

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

namespace OrdinaryData

variable (O : OrdinaryData packet)

theorem originalAllocation_plain₁ (side : Bool) :
    (O.originalAllocation side).plain₁ =
      SupportCartesian.plainResidual (packet.firstAtlas side).reindex.plain₁
        (primeSupport packet.key.1.val.1) (packet.secondBranch side).plainExtract₁ := by
  cases side
  · change packet.leftReindex.plain₁ = _
    exact PassiveSecondCarrier.residualReindex_plain₁ _ _ _ _ _ _
  · change packet.rightReindex.plain₁ = _
    exact PassiveSecondCarrier.residualReindex_plain₁ _ _ _ _ _ _

theorem originalAllocation_plain₂ (side : Bool) :
    (O.originalAllocation side).plain₂ =
      SupportCartesian.plainResidual (packet.firstAtlas side).reindex.plain₂
        (primeSupport packet.key.1.val.1) (packet.secondBranch side).plainExtract₂ := by
  cases side
  · change packet.leftReindex.plain₂ = _
    exact PassiveSecondCarrier.residualReindex_plain₂ _ _ _ _ _ _
  · change packet.rightReindex.plain₂ = _
    exact PassiveSecondCarrier.residualReindex_plain₂ _ _ _ _ _ _

theorem originalAllocation_plain (side plain : Bool) :
    (if plain then (O.originalAllocation side).plain₂ else (O.originalAllocation side).plain₁) =
      SupportCartesian.plainResidual
        (if plain then (packet.firstAtlas side).reindex.plain₂
         else (packet.firstAtlas side).reindex.plain₁)
        (primeSupport packet.key.1.val.1)
        (if plain then (packet.secondBranch side).plainExtract₂
         else (packet.secondBranch side).plainExtract₁) := by
  cases plain
  · exact O.originalAllocation_plain₁ side
  · exact O.originalAllocation_plain₂ side

end OrdinaryData

namespace OriginalOccurrenceData

variable {O : OrdinaryData packet} (D : OriginalOccurrenceData O)

theorem originalAllocation_slots_atlas (side : Bool) (i : Fin (O.originalSlotCount side)) :
    (O.originalAllocation side).slots i =
      SupportCartesian.primeLive
        ((packet.firstAtlas side).reindex.slots
          (SlotRestriction.index (packet.secondBranch side).keep
            (Fin.cast (D.second_count side).symm i)))
        (primeSupport packet.key.1.val.1) := by
  cases side
  · change packet.leftReindex.slots i = _
    exact congrFun (PassiveSecondCarrier.residualReindex_slots _ _ _ _ _ _) i
  · change packet.rightReindex.slots i = _
    exact congrFun (PassiveSecondCarrier.residualReindex_slots _ _ _ _ _ _) i

theorem originalAllocation_slots (hpacket : packet.Realizes) (side : Bool)
    (i : Fin (O.originalSlotCount side)) :
    (O.originalAllocation side).slots i =
      SupportCartesian.primeLive
        (SupportCartesian.primeLive
          (call.workingRaw.exteriorSlots (D.secondIndex side i))
          packet.second.physical.first.fullDeletion)
        (primeSupport packet.key.1.val.1) := by
  calc
    _ = SupportCartesian.primeLive
        ((packet.firstAtlas side).reindex.slots
          (SlotRestriction.index (packet.secondBranch side).keep
            (Fin.cast (D.second_count side).symm i)))
        (primeSupport packet.key.1.val.1) := D.originalAllocation_slots_atlas side i
    _ = _ := congrArg (fun S => SupportCartesian.primeLive S (primeSupport packet.key.1.val.1))
      (D.firstAtlas_slots hpacket side
        (SlotRestriction.index (packet.secondBranch side).keep
          (Fin.cast (D.second_count side).symm i)))

end OriginalOccurrenceData

namespace OrdinarySeed

variable (seed : OrdinarySeed packet)

theorem originalChildCarrier_plain (side plain : Bool) :
    (seed.originalChildCarrier side).plain plain =
      nonzeroQuotientMomentSupport
        ((seed.ordinary.originalAllocation side).plainDivisor
          (if plain then Fin.succ 0 else 0)).val
        (if plain then (seed.ordinary.originalAllocation side).plain₂
         else (seed.ordinary.originalAllocation side).plain₁) := by
  cases side <;> cases plain <;> rfl

theorem originalChildCarrier_slots (hpacket : packet.Realizes) (side : Bool)
    (i : Fin (seed.ordinary.residualSlotCount side)) :
    (seed.originalChildCarrier side).slots i =
      SupportCartesian.primeLive
        (SupportCartesian.primeLive
          (call.workingRaw.exteriorSlots (seed.slotIndex side i))
          packet.second.physical.first.fullDeletion)
        (primeSupport packet.key.1.val.1) := by
  cases side
  · exact seed.occurrences.originalAllocation_slots hpacket false
      (SlotRestriction.index (seed.ordinary.originalAllocation false).keep
        (Fin.cast (seed.residual_count false).symm i))
  · exact seed.occurrences.originalAllocation_slots hpacket true
      (SlotRestriction.index (seed.ordinary.originalAllocation true).keep
        (Fin.cast (seed.residual_count true).symm i))

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSecondCarrier.residualReindex_slots
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.originalAllocation_plain
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.originalAllocation_slots
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.originalChildCarrier_slots

