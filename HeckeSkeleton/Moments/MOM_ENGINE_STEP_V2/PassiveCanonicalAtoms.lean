import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCanonicalProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSourceReindex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalJointAllocatedSource

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The canonical atoms after the actual inner allocation

The original inner scalar becomes the unchanged row weight. The old
plain divisors shift the two logarithmic locations by constants; their
phases disappear in each row norm. Every remaining scale, weight and
occurrence is the canonical global original formula.
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

namespace OrdinarySeed

variable (seed : OrdinarySeed packet) (input : ProfileInput call)

theorem originalSource_allocation (side rectangle : Bool) :
    (seed.ordinary.originalSource side rectangle).allocation =
      seed.ordinary.originalAllocation side := by
  cases side <;> rfl

theorem originalSource_rows (side rectangle : Bool) :
    (seed.ordinary.originalSource side rectangle).rows =
      (seed.ordinary.originalSource side false).rows := by
  cases side <;> rfl

theorem originalSource_weight (side rectangle : Bool) :
    (seed.ordinary.originalSource side rectangle).weight =
      (seed.ordinary.originalSource side false).weight := by
  cases side <;> rfl

theorem unscaledOriginal_frozenScalar (side rectangle : Bool)
    (h : seed.ordinary.rows.live) :
    (seed.unscaledOriginal side rectangle).frozenScalar (σ := Arithmetic.embedding c) h =
      seed.innerScalar side h := by
  change (seed.ordinary.originalSource side rectangle).frozenScalar
    (σ := Arithmetic.embedding c) h = _
  unfold ActualAllocatedSource.frozenScalar
  rw [seed.atoms.characters, seed.atoms.base]
  rw [show (seed.ordinary.originalSource side rectangle).length =
      seed.occurrences.beforeLength side from funext (seed.atoms.length side rectangle)]
  rw [show (seed.ordinary.originalSource side rectangle).slotWeight h =
      seed.occurrences.beforeSlotWeight side from
        funext fun i => funext fun q => seed.atoms.slotWeight side rectangle h i q]
  cases side <;> rfl

def canonicalWeight (side : Bool) (h : seed.ordinary.rows.live) : ℂ :=
  (seed.ordinary.originalSource side false).weight h * seed.innerScalar side h *
    star (seed.innerScalar side h)

theorem unscaledOriginal_childWeight (side rectangle : Bool)
    (h : seed.ordinary.rows.live) :
    (seed.unscaledOriginal side rectangle).childWeight (σ := Arithmetic.embedding c) h =
      seed.canonicalWeight side h := by
  unfold ActualAllocatedSource.childWeight
  rw [seed.unscaledOriginal_frozenScalar]
  change (seed.ordinary.originalSource side rectangle).weight h * _ * _ = _
  rw [seed.originalSource_weight]
  rfl

def canonicalCoefficient (paid side rectangle : Bool) (h : seed.ordinary.rows.live) :
    AllocationColumn K (seed.ordinary.residualSlotCount side) → ℂ :=
  rawSourceCoefficient (σ := Arithmetic.embedding c)
    (seed.phases.characters paid (seed.slotIndex side))
    ((seed.ordinary.originalSource side false).extractedFactor h)
    ((seed.ordinary.originalSource side false).row h).element
    (seed.occurrences.plainScale side rectangle false)
    (seed.occurrences.plainScale side rectangle true) call.base
    (fun i => (call.node.data.geometry.slots (seed.slotIndex side i)).length)
    (fun I => (seed.plainProfile input side rectangle false).formula.value 0
      (idealNorm K I / seed.occurrences.plainScale side rectangle false))
    (fun I => (seed.plainProfile input side rectangle true).formula.value 0
      (idealNorm K I / seed.occurrences.plainScale side rectangle true))
    (fun i q => (seed.primeProfile input side i).formula.value 0
      ((Ideal.absNorm q.asIdeal : ℝ) /
        call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length))

def canonicalLocation (side : Bool) :
    AllocationColumn K (seed.ordinary.residualSlotCount side) → EngineParameter :=
  rawSourceLocation
    (fun I => seed.location side (idealNorm K I))
    (fun I => seed.location side (idealNorm K I))
    (fun _ q => seed.location side (Ideal.absNorm q.asIdeal : ℝ))

theorem canonicalSource_energy (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool) (ξ : EngineParameter) :
    (seed.canonicalSource input support side a rectangle).energy
      (σ := Arithmetic.embedding c) ξ =
    jointColumnEnergy (seed.ordinary.originalSource side false).rows
      (PassiveAllocation.columns (support.carrier side) a.val)
      (seed.canonicalWeight side) (seed.canonicalCoefficient input true side rectangle)
      (fun _ => seed.canonicalLocation side) ξ := rfl

/-- The exact old quotient carrier before restoring smooth support. -/
def originalChildCarrier : (side : Bool) →
    PassiveAllocation.Carrier K (seed.ordinary.residualSlotCount side)
  | false => PassiveSource.oldCarrier (seed.unscaledOriginal false false)
  | true => PassiveSource.oldCarrier (seed.unscaledOriginal true false)

def plainDivisorTranslation (side plain : Bool) : EngineParameter :=
  seed.location side (idealNorm K ((seed.ordinary.originalAllocation side).plainDivisor
    (if plain then Fin.succ 0 else 0)))

def oldExtractedCoefficient (paid : Bool) : (side rectangle : Bool) →
    seed.ordinary.rows.live → AllocationColumn K (seed.ordinary.residualSlotCount side) → ℂ
  | false, rectangle =>
    PassiveSource.paidCoefficient (σ := Arithmetic.embedding c)
      (seed.unscaledOriginal false rectangle)
      (fun _ => seed.phases.characters paid (seed.slotIndex false))
  | true, rectangle =>
    PassiveSource.paidCoefficient (σ := Arithmetic.embedding c)
      (seed.unscaledOriginal true rectangle)
      (fun _ => seed.phases.characters paid (seed.slotIndex true))

def oldExtractedLocation : (side rectangle : Bool) →
    seed.ordinary.rows.live → AllocationColumn K (seed.ordinary.residualSlotCount side) →
      EngineParameter
  | false, rectangle => PassiveSource.paidLocation (seed.unscaledOriginal false rectangle)
  | true, rectangle => PassiveSource.paidLocation (seed.unscaledOriginal true rectangle)

theorem oldExtractedCoefficient_eq (paid side rectangle : Bool) :
    seed.oldExtractedCoefficient paid side rectangle =
      seed.canonicalCoefficient input paid side rectangle := by
  funext h i
  cases side <;>
    simp only [oldExtractedCoefficient, PassiveSource.paidCoefficient,
      unscaledOriginal, PassiveSource.withLeftWeight, canonicalCoefficient,
      seed.atoms.scale₁, seed.atoms.scale₂, seed.atoms.base,
      ActualAllocatedSource.childLength, seed.atoms.length,
      seed.atoms.rightWeight, seed.atoms.slotWeight,
      seed.originalSource_allocation, seed.beforePlainWeight_quotient input,
      seed.beforeSlotWeight_remaining input, OriginalOccurrenceData.plainScale,
      OriginalOccurrenceData.beforeLength, OriginalOccurrenceData.remainingIndex,
      slotIndex, Fin.cast_refl]
  all_goals rfl

theorem oldExtractedLocation_eq (side rectangle : Bool) :
    seed.oldExtractedLocation side rectangle = fun _ i =>
      (seed.plainDivisorTranslation side false + seed.plainDivisorTranslation side true) +
        seed.canonicalLocation side i := by
  funext h i
  cases side <;>
    simp only [oldExtractedLocation, PassiveSource.paidLocation,
      unscaledOriginal, PassiveSource.withLeftWeight, canonicalLocation,
      rawSourceLocation, childCartesianLocation,
      seed.original_leftLocation, seed.original_rightLocation, seed.original_slotLocation,
      seed.originalSource_allocation, seed.location_mul, plainDivisorTranslation]
  all_goals abel

/-- Exact extraction, still on the old finite quotient carrier. -/
theorem unscaledOriginal_energy_old (side rectangle : Bool) (ξ : EngineParameter) :
    (seed.unscaledOriginal side rectangle).energy (σ := Arithmetic.embedding c) ξ =
      jointColumnEnergy (seed.ordinary.originalSource side false).rows
        (PassiveAllocation.carrierColumns (seed.originalChildCarrier side))
        (seed.canonicalWeight side) (seed.oldExtractedCoefficient false side rectangle)
        (seed.oldExtractedLocation side rectangle) ξ := by
  have hw (s r : Bool) :
      (seed.unscaledOriginal s r).childWeight (σ := Arithmetic.embedding c) =
        seed.canonicalWeight s :=
    funext (seed.unscaledOriginal_childWeight s r)
  cases side
  · have he := PassiveSource.energy_eq_oldCarrier (σ := Arithmetic.embedding c)
      (seed.unscaledOriginal false rectangle) ξ
    rw [hw] at he
    simpa only [originalChildCarrier, oldExtractedCoefficient, oldExtractedLocation,
      PassiveSource.paidCoefficient, unscaledOriginal, PassiveSource.withLeftWeight,
      seed.atoms.characters, OriginalOccurrenceData.originalCharacters,
      OriginalPhaseData.characters,
      CanonicalOriginalPhaseCalibration.sourceCharacters_restrictSlots,
      slotIndex, OriginalOccurrenceData.remainingIndex, Fin.cast_refl] using he
  · have he := PassiveSource.energy_eq_oldCarrier (σ := Arithmetic.embedding c)
      (seed.unscaledOriginal true rectangle) ξ
    rw [hw] at he
    simpa only [originalChildCarrier, oldExtractedCoefficient, oldExtractedLocation,
      PassiveSource.paidCoefficient, unscaledOriginal, PassiveSource.withLeftWeight,
      seed.atoms.characters, OriginalOccurrenceData.originalCharacters,
      OriginalPhaseData.characters,
      CanonicalOriginalPhaseCalibration.sourceCharacters_restrictSlots,
      slotIndex, OriginalOccurrenceData.remainingIndex, Fin.cast_refl] using he

/-- The old exact carrier now has the canonical global atoms. The two
constant plain-divisor translations cost precisely one in norm. -/
theorem unscaledOriginal_energy_canonicalOld (side rectangle : Bool) (ξ : EngineParameter) :
    (seed.unscaledOriginal side rectangle).energy (σ := Arithmetic.embedding c) ξ =
      jointColumnEnergy (seed.ordinary.originalSource side false).rows
        (PassiveAllocation.carrierColumns (seed.originalChildCarrier side))
        (seed.canonicalWeight side) (seed.canonicalCoefficient input false side rectangle)
        (fun _ => seed.canonicalLocation side) ξ := by
  rw [seed.unscaledOriginal_energy_old, seed.oldExtractedCoefficient_eq input,
    seed.oldExtractedLocation_eq]
  exact jointColumnEnergy_rowTranslation _ _ _ _ _ _ ξ

/-- The same old source transformed by the exact extraction constructor. -/
def extractedPassiveSource (support : seed.ordinary.PassiveSupport input) :
    (side : Bool) → support.labels side → Bool →
      ActualAllocatedSource (Arithmetic.data c) EngineParameter seed.ordinary.rows.live
        (seed.ordinary.residualSlotCount side)
  | false, a, rectangle =>
    PassiveSource.source (σ := Arithmetic.embedding c) (seed.unscaledOriginal false rectangle)
      (support.carrier false) seed.ordinary.passiveMask
      (fun _ => seed.phases.characters true (seed.slotIndex false)) a
  | true, a, rectangle =>
    PassiveSource.source (σ := Arithmetic.embedding c) (seed.unscaledOriginal true rectangle)
      (support.carrier true) seed.ordinary.passiveMask
      (fun _ => seed.phases.characters true (seed.slotIndex true)) a

theorem extractedPassiveSource_eq (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    seed.extractedPassiveSource input support side a rectangle =
      CanonicalJointAllocatedSource.translateLocations
        (seed.canonicalSource input support side a rectangle)
        (fun _ => seed.plainDivisorTranslation side false)
        (fun _ => seed.plainDivisorTranslation side true)
        (fun _ _ => 0) := by
  have hl (s r : Bool) : (seed.ordinary.originalSource s r).length =
      seed.occurrences.beforeLength s := funext (seed.atoms.length s r)
  have hr (s r : Bool) (h : seed.ordinary.rows.live) :
      (seed.ordinary.originalSource s r).rightWeight h =
        seed.occurrences.beforePlainWeight s r true :=
    funext (seed.atoms.rightWeight s r h)
  have hs (s r : Bool) (h : seed.ordinary.rows.live) :
      (seed.ordinary.originalSource s r).slotWeight h =
        seed.occurrences.beforeSlotWeight s :=
    funext fun i => funext fun q => seed.atoms.slotWeight s r h i q
  have hx (s r : Bool) (h : seed.ordinary.rows.live) :
      (seed.ordinary.originalSource s r).leftLocation h =
        (fun I => seed.location s (idealNorm K I)) :=
    funext (seed.original_leftLocation s r h)
  have hy (s r : Bool) (h : seed.ordinary.rows.live) :
      (seed.ordinary.originalSource s r).rightLocation h =
        (fun I => seed.location s (idealNorm K I)) :=
    funext (seed.original_rightLocation s r h)
  have hz (s r : Bool) (h : seed.ordinary.rows.live) :
      (seed.ordinary.originalSource s r).slotLocation h =
        (fun _ q => seed.location s (Ideal.absNorm q.asIdeal : ℝ)) :=
    funext fun i => funext fun q => seed.original_slotLocation s r h i q
  cases side <;>
    simp only [extractedPassiveSource, PassiveSource.source,
      seed.unscaledOriginal_childWeight, canonicalWeight,
      unscaledOriginal, PassiveSource.withLeftWeight,
      canonicalSource, CanonicalJointAllocatedSource.translateLocations,
      seed.atoms.scale₁, seed.atoms.scale₂, seed.atoms.base,
      ActualAllocatedSource.childLength, hl, hr, hs, hx, hy, hz,
      seed.beforePlainWeight_quotient input,
      seed.beforeSlotWeight_remaining input, seed.location_mul, zero_add,
      OriginalOccurrenceData.plainScale, plainDivisorTranslation,
      OriginalOccurrenceData.beforeLength, OriginalOccurrenceData.remainingIndex,
      slotIndex, Fin.cast_refl, seed.originalSource_allocation]
  all_goals rfl

theorem extractedPassiveSource_energy (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool) (ξ : EngineParameter) :
    (seed.extractedPassiveSource input support side a rectangle).energy
      (σ := Arithmetic.embedding c) ξ =
    (seed.canonicalSource input support side a rectangle).energy
      (σ := Arithmetic.embedding c) ξ := by
  rw [seed.extractedPassiveSource_eq]
  exact CanonicalJointAllocatedSource.translateLocations_energy _ _ _ _ ξ

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.unscaledOriginal_childWeight
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.extractedPassiveSource_energy
