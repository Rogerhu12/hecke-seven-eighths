import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalOccurrenceData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two actual first cover dictionaries

The genuine source trace makes every full-deletion entry a prime ideal.
The same raw-family cover then identifies the first atlas with the
original plain residuals and original prime occurrences. These are
finite-carrier identities, before a coefficient or calibration estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments.Support

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem fullDeletion_prime (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) (P : Ideal (𝓞 K))
    (hP : P ∈ (expansion.source i).first.fullDeletion) : Prime P := by
  cases expansion with
  | direct =>
    change P ∈ (family.source i).first.fullDeletion at hP
    rw [hfamily.deletion i] at hP
    exact support_prime hP
  | pooled pool count index source =>
    obtain ⟨_, _, horigin⟩ := hexpansion
    change P ∈ (source i).first.fullDeletion at hP
    cases hindex : (index i).2 with
    | inl u =>
      have hm : pool.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases hm with ⟨_, _, _, _, _, _, _, hfirst⟩
      rw [hfirst, hfamily.deletion (index i).1] at hP
      exact support_prime hP
    | inr qe =>
      rcases qe with ⟨q, e⟩
      have he : pool.ErrorOrigin (index i).1 q e (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdelete, _⟩
      rw [hdelete] at hP
      rcases Finset.mem_union.mp hP with hP | hP
      · rw [hfamily.deletion (index i).1] at hP
        exact support_prime hP
      · have heq : P = q.val.val.asIdeal := Finset.mem_singleton.mp hP
        rw [heq]
        exact Ideal.prime_of_isPrime q.val.val.ne_bot inferInstance

end PoolExpansion

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem fullDeletion_prime (hpacket : packet.Realizes) (P : Ideal (𝓞 K))
    (hP : P ∈ packet.second.physical.first.fullDeletion) : Prime P := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  let i : Fin trace.expansion.count := (raw.index j).val.1.1
  have hphysical := htrace.second.physical i
  change P ∈ (trace.second.source i).physical.first.fullDeletion at hP
  rw [hphysical] at hP
  exact trace.expansion.fullDeletion_prime htrace.cauchy htrace.expansion i P hP

theorem firstAtlas_plain₁ (hpacket : packet.Realizes) (side : Bool) :
    (packet.firstAtlas side).reindex.plain₁ =
      SupportCartesian.plainResidual call.workingRaw.originalPlain₁
        packet.second.physical.first.fullDeletion (packet.firstBranch side).plainExtract₁ := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, _, hraw, rfl⟩
  cases side
  · exact (hraw (raw.index j).val.1.1).1.plain₁ _
  · exact (hraw (raw.index j).val.1.1).2.plain₁ _

theorem firstAtlas_plain₂ (hpacket : packet.Realizes) (side : Bool) :
    (packet.firstAtlas side).reindex.plain₂ =
      SupportCartesian.plainResidual call.workingRaw.originalPlain₂
        packet.second.physical.first.fullDeletion (packet.firstBranch side).plainExtract₂ := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, _, hraw, rfl⟩
  cases side
  · exact (hraw (raw.index j).val.1.1).1.plain₂ _
  · exact (hraw (raw.index j).val.1.1).2.plain₂ _

theorem firstAtlas_slots_heq (hpacket : packet.Realizes) (side : Bool) :
    HEq (packet.firstAtlas side).reindex.slots
      (fun j : Fin (packet.firstBranch side).keep.card =>
        SupportCartesian.primeLive
          (call.workingRaw.exteriorSlots (SlotRestriction.index (packet.firstBranch side).keep j))
          packet.second.physical.first.fullDeletion) := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, _, hraw, rfl⟩
  cases side
  · exact (hraw (raw.index j).val.1.1).1.slots _
  · exact (hraw (raw.index j).val.1.1).2.slots _

end RawLeafPacket

namespace OriginalOccurrenceData

private theorem heq_fun_apply_cast {m n : ℕ} {α : Type*} (h : m = n)
    (f : Fin n → α) (g : Fin m → α) (he : HEq f g) (i : Fin n) :
    f i = g (Fin.cast h.symm i) := by
  subst n
  exact congrFun (eq_of_heq he) i

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (D : OriginalOccurrenceData O)

/-- The supplied count proof only transports the actual occurrence;
the carrier is fixed by the original source cover. -/
theorem firstAtlas_slots (hpacket : packet.Realizes) (side : Bool)
    (i : Fin (packet.firstAtlas side).slotCount) :
    (packet.firstAtlas side).reindex.slots i =
      SupportCartesian.primeLive (call.workingRaw.exteriorSlots (D.firstIndex side i))
        packet.second.physical.first.fullDeletion :=
  heq_fun_apply_cast (D.first_count side) _ _ (packet.firstAtlas_slots_heq hpacket side) i

end OriginalOccurrenceData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.fullDeletion_prime
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.firstAtlas_plain₁
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.firstAtlas_slots

