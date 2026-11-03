import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The canonical restored smooth support

Both rectangles use the original profiles and their actual quotient
scales. The remaining occurrence map is the composition of the two
physical support extractions and the original inner allocation. Every
map is injective; no new occurrence or independent scale is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

namespace PassiveCanonicalSupport

theorem slotRestriction_index_injective {k : ℕ} (keep : Finset (Fin k)) :
    Function.Injective (SlotRestriction.index keep) := by
  intro i j h
  apply keep.equivFin.symm.injective
  exact Subtype.ext h

theorem finCast_injective {m n : ℕ} (h : m = n) :
    Function.Injective (Fin.cast h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin n => x.val) hij)

end PassiveCanonicalSupport

namespace OriginalOccurrenceData

variable {O : OrdinaryData packet} (D : OriginalOccurrenceData O)

theorem firstIndex_injective (side : Bool) : Function.Injective (D.firstIndex side) :=
  (PassiveCanonicalSupport.slotRestriction_index_injective _).comp
    (PassiveCanonicalSupport.finCast_injective _)

theorem secondIndex_injective (side : Bool) : Function.Injective (D.secondIndex side) :=
  (D.firstIndex_injective side).comp
    ((PassiveCanonicalSupport.slotRestriction_index_injective _).comp
      (PassiveCanonicalSupport.finCast_injective _))

theorem remainingIndex_injective (side : Bool) :
    Function.Injective (D.remainingIndex side) :=
  (D.secondIndex_injective side).comp
    (PassiveCanonicalSupport.slotRestriction_index_injective _)

theorem plainScale_pos (side rectangle plain : Bool) :
    0 < D.plainScale side rectangle plain := by
  apply div_pos
  · apply div_pos
    · apply div_pos
      · unfold Call.originalPlainScale
        split <;> exact Real.rpow_pos_of_pos call.base_pos _
      · exact idealNorm_pos K _
    · exact idealNorm_pos K _
  · exact idealNorm_pos K _

end OriginalOccurrenceData

namespace OrdinarySeed

variable (seed : OrdinarySeed packet) (input : ProfileInput call)

theorem slotIndex_injective (side : Bool) : Function.Injective (seed.slotIndex side) :=
  (seed.occurrences.remainingIndex_injective side).comp
    (PassiveCanonicalSupport.finCast_injective _)

def canonicalSmoothSupport (side : Bool) :
    SmoothSideSupport input (seed.ordinary.residualSlotCount side) where
  slotEmbedding := seed.slotIndex side
  slotEmbedding_injective := seed.slotIndex_injective side
  plain := seed.plainProfile input side
  plain_kind := fun _ _ => rfl
  plainScale := seed.occurrences.plainScale side
  plainScale_pos := seed.occurrences.plainScale_pos side
  prime := seed.primeProfile input side
  prime_kind := fun _ => rfl
  prime_dilation := fun _ => rfl

def canonicalSupport : seed.ordinary.PassiveSupport input where
  side := seed.canonicalSmoothSupport input
  scale_eq := fun side rectangle plain => (seed.plain_scales side rectangle plain).symm
  length_eq := by
    intro side i
    have hi := seed.lengths side (Fin.cast (seed.residual_count side).symm i)
    have hcast :
        Fin.cast (seed.residual_count side)
          (Fin.cast (seed.residual_count side).symm i) = i := by
      apply Fin.ext
      rfl
    rw [hcast] at hi
    exact hi.symm

theorem canonicalSupport_spec : seed.CanonicalSupport input (seed.canonicalSupport input) where
  slots := fun _ => rfl
  plain := fun _ _ _ => rfl
  prime := fun _ _ => rfl

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSupport_spec
