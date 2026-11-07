module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCanonicalProfiles
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSourceReindex
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalJointAllocatedSource

@[expose] public section

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

set_option maxHeartbeats 1000000 in
theorem oldExtractedCoefficient_eq (paid side rectangle : Bool) :
    seed.oldExtractedCoefficient paid side rectangle =
      seed.canonicalCoefficient input paid side rectangle := by
  have hr (s : Bool) (h : seed.ordinary.rows.live) :
      (seed.ordinary.originalSource s rectangle).rightWeight h =
        seed.occurrences.beforePlainWeight s rectangle true :=
    funext (seed.atoms.rightWeight s rectangle h)
  have hf (s : Bool) : (seed.ordinary.originalSource s rectangle).extractedFactor =
      (seed.ordinary.originalSource s false).extractedFactor := by
    cases s <;> rfl
  have he (s : Bool) (h : seed.ordinary.rows.live) :
      ((seed.ordinary.originalSource s rectangle).row h).element =
        ((seed.ordinary.originalSource s false).row h).element := by
    cases s <;> rfl
  have hleft (s : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      seed.occurrences.beforePlainWeight s rectangle false
          ((seed.ordinary.originalAllocation s).plainDivisor 0 * I) =
        (seed.plainProfile input s rectangle false).formula.value 0
          (idealNorm K I / seed.occurrences.plainScale s rectangle false) :=
    seed.beforePlainWeight_quotient input s rectangle false I
  have hright (s : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      seed.occurrences.beforePlainWeight s rectangle true
          ((seed.ordinary.originalAllocation s).plainDivisor (Fin.succ 0) * I) =
        (seed.plainProfile input s rectangle true).formula.value 0
          (idealNorm K I / seed.occurrences.plainScale s rectangle true) :=
    seed.beforePlainWeight_quotient input s rectangle true I
  have indexFalse (r : Bool) (j : Fin (seed.ordinary.residualSlotCount false)) :
      SlotRestriction.index (seed.ordinary.originalSource false r).allocation.keep j =
        SlotRestriction.index (seed.ordinary.originalAllocation false).keep
          (Fin.cast (seed.residual_count false).symm j) := rfl
  have indexTrue (r : Bool) (j : Fin (seed.ordinary.residualSlotCount true)) :
      SlotRestriction.index (seed.ordinary.originalSource true r).allocation.keep j =
        SlotRestriction.index (seed.ordinary.originalAllocation true).keep
          (Fin.cast (seed.residual_count true).symm j) := rfl
  have hlengthFalse : (seed.unscaledOriginal false rectangle).childLength =
      (fun j => (call.node.data.geometry.slots (seed.slotIndex false j)).length) := by
    funext j
    change (seed.ordinary.originalSource false rectangle).length
      (SlotRestriction.index (seed.ordinary.originalSource false rectangle).allocation.keep j) = _
    exact (seed.atoms.length false rectangle _).trans
      ((congrArg (seed.occurrences.beforeLength false) (indexFalse rectangle j)).trans rfl)
  have hlengthTrue : (seed.unscaledOriginal true rectangle).childLength =
      (fun j => (call.node.data.geometry.slots (seed.slotIndex true j)).length) := by
    funext j
    change (seed.ordinary.originalSource true rectangle).length
      (SlotRestriction.index (seed.ordinary.originalSource true rectangle).allocation.keep j) = _
    exact (seed.atoms.length true rectangle _).trans
      ((congrArg (seed.occurrences.beforeLength true) (indexTrue rectangle j)).trans rfl)
  have hslotFalse (h : seed.ordinary.rows.live) :
      (fun j => (seed.unscaledOriginal false rectangle).slotWeight h
        (SlotRestriction.index (seed.unscaledOriginal false rectangle).allocation.keep j)) =
      (fun j q => (seed.primeProfile input false j).formula.value 0
        ((Ideal.absNorm q.asIdeal : ℝ) /
          call.base ^ (call.node.data.geometry.slots (seed.slotIndex false j)).length)) := by
    funext j q
    change (seed.ordinary.originalSource false rectangle).slotWeight h
      (SlotRestriction.index (seed.ordinary.originalSource false rectangle).allocation.keep j) q = _
    exact (seed.atoms.slotWeight false rectangle h _ q).trans
      ((congrArg (fun index => seed.occurrences.beforeSlotWeight false index q)
        (indexFalse rectangle j)).trans (seed.beforeSlotWeight_remaining input false j q))
  have hslotTrue (h : seed.ordinary.rows.live) :
      (fun j => (seed.unscaledOriginal true rectangle).slotWeight h
        (SlotRestriction.index (seed.unscaledOriginal true rectangle).allocation.keep j)) =
      (fun j q => (seed.primeProfile input true j).formula.value 0
        ((Ideal.absNorm q.asIdeal : ℝ) /
          call.base ^ (call.node.data.geometry.slots (seed.slotIndex true j)).length)) := by
    funext j q
    change (seed.ordinary.originalSource true rectangle).slotWeight h
      (SlotRestriction.index (seed.ordinary.originalSource true rectangle).allocation.keep j) q = _
    exact (seed.atoms.slotWeight true rectangle h _ q).trans
      ((congrArg (fun index => seed.occurrences.beforeSlotWeight true index q)
        (indexTrue rectangle j)).trans (seed.beforeSlotWeight_remaining input true j q))
  funext h i
  cases side <;>
    dsimp only [oldExtractedCoefficient, PassiveSource.paidCoefficient,
      canonicalCoefficient]
  · rw [hlengthFalse, hslotFalse]
    dsimp only [unscaledOriginal, PassiveSource.withLeftWeight]
    simp only [seed.atoms.scale₁, seed.atoms.scale₂, seed.atoms.base,
      hr, hf, he, seed.originalSource_allocation, hleft, hright,
      OriginalOccurrenceData.plainScale, Bool.false_eq_true, ite_false, ite_true]
    all_goals rfl
  · rw [hlengthTrue, hslotTrue]
    dsimp only [unscaledOriginal, PassiveSource.withLeftWeight]
    simp only [seed.atoms.scale₁, seed.atoms.scale₂, seed.atoms.base,
      hr, hf, he, seed.originalSource_allocation, hleft, hright,
      OriginalOccurrenceData.plainScale, Bool.false_eq_true, ite_false, ite_true]
    all_goals rfl

theorem oldExtractedLocation_eq (side rectangle : Bool) :
    seed.oldExtractedLocation side rectangle = fun _ i =>
      (seed.plainDivisorTranslation side false + seed.plainDivisorTranslation side true) +
        seed.canonicalLocation side i := by
  have rearrange (a b c d e : EngineParameter) :
      (a + b + (c + d)) + e = (a + c) + (b + d + e) := by
    abel
  funext h i
  cases side <;>
    simp only [oldExtractedLocation, PassiveSource.paidLocation,
      unscaledOriginal, PassiveSource.withLeftWeight, canonicalLocation,
      rawSourceLocation, childCartesianLocation,
      seed.original_leftLocation, seed.original_rightLocation, seed.original_slotLocation,
      seed.originalSource_allocation, seed.location_mul, plainDivisorTranslation]
  all_goals exact rearrange _ _ _ _ _

set_option maxHeartbeats 500000 in
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
    have hcarrier : PassiveSource.oldCarrier (seed.unscaledOriginal false rectangle) =
        seed.originalChildCarrier false := rfl
    have hrows : (seed.unscaledOriginal false rectangle).rows =
        (seed.ordinary.originalSource false false).rows :=
      seed.originalSource_rows false rectangle
    have hindex :
        (fun i : Fin (seed.ordinary.residualSlotCount false) =>
          seed.occurrences.secondIndex false
            (SlotRestriction.index (seed.ordinary.originalSource false rectangle).allocation.keep i)) =
          seed.slotIndex false := by
      funext i
      rfl
    have hcharacters :
        (fun h : seed.ordinary.rows.live =>
          ((seed.unscaledOriginal false rectangle).characters h).restrictSlots
            (seed.unscaledOriginal false rectangle).allocation.keep) =
          (fun _ => seed.phases.characters false (seed.slotIndex false)) := by
      funext h
      change ((seed.ordinary.originalSource false rectangle).characters h).restrictSlots
        (seed.ordinary.originalSource false rectangle).allocation.keep = _
      rw [seed.atoms.characters]
      change (seed.phases.characters false (seed.occurrences.secondIndex false)).restrictSlots
        (seed.ordinary.originalSource false rectangle).allocation.keep = _
      unfold OriginalPhaseData.characters
      rw [CanonicalOriginalPhaseCalibration.sourceCharacters_restrictSlots]
      exact congrArg (CanonicalOriginalPhaseCalibration.sourceCharacters call.localizedData
        (call.localizedSource.source.recipe.correction * (seed.phases.moving false).character)
        (seed.phases.mask false)) hindex
    rw [hw, hcarrier, hrows, hcharacters] at he
    exact he
  · have he := PassiveSource.energy_eq_oldCarrier (σ := Arithmetic.embedding c)
      (seed.unscaledOriginal true rectangle) ξ
    have hcarrier : PassiveSource.oldCarrier (seed.unscaledOriginal true rectangle) =
        seed.originalChildCarrier true := rfl
    have hrows : (seed.unscaledOriginal true rectangle).rows =
        (seed.ordinary.originalSource true false).rows :=
      seed.originalSource_rows true rectangle
    have hindex :
        (fun i : Fin (seed.ordinary.residualSlotCount true) =>
          seed.occurrences.secondIndex true
            (SlotRestriction.index (seed.ordinary.originalSource true rectangle).allocation.keep i)) =
          seed.slotIndex true := by
      funext i
      rfl
    have hcharacters :
        (fun h : seed.ordinary.rows.live =>
          ((seed.unscaledOriginal true rectangle).characters h).restrictSlots
            (seed.unscaledOriginal true rectangle).allocation.keep) =
          (fun _ => seed.phases.characters false (seed.slotIndex true)) := by
      funext h
      change ((seed.ordinary.originalSource true rectangle).characters h).restrictSlots
        (seed.ordinary.originalSource true rectangle).allocation.keep = _
      rw [seed.atoms.characters]
      change (seed.phases.characters false (seed.occurrences.secondIndex true)).restrictSlots
        (seed.ordinary.originalSource true rectangle).allocation.keep = _
      unfold OriginalPhaseData.characters
      rw [CanonicalOriginalPhaseCalibration.sourceCharacters_restrictSlots]
      exact congrArg (CanonicalOriginalPhaseCalibration.sourceCharacters call.localizedData
        (call.localizedSource.source.recipe.correction * (seed.phases.moving false).character)
        (seed.phases.mask false)) hindex
    rw [hw, hcarrier, hrows, hcharacters] at he
    exact he

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

private theorem allocatedSource_fields_ext
    {A : DedekindZetaZeroFree.SArithmeticData K} {V H : Type*} {k : ℕ}
    {s t : ActualAllocatedSource A V H k}
    (allocation : s.allocation = t.allocation) (rows : s.rows = t.rows)
    (weight : s.weight = t.weight) (originalIdeal : s.originalIdeal = t.originalIdeal)
    (frequency : s.frequency = t.frequency)
    (extractedFactor : s.extractedFactor = t.extractedFactor)
    (normFactor : s.normFactor = t.normFactor) (row : HEq s.row t.row)
    (characters : s.characters = t.characters)
    (scale₁ : s.scale₁ = t.scale₁) (scale₂ : s.scale₂ = t.scale₂)
    (base : s.base = t.base) (length : s.length = t.length)
    (leftWeight : s.leftWeight = t.leftWeight) (rightWeight : s.rightWeight = t.rightWeight)
    (slotWeight : s.slotWeight = t.slotWeight)
    (leftLocation : s.leftLocation = t.leftLocation)
    (rightLocation : s.rightLocation = t.rightLocation)
    (slotLocation : s.slotLocation = t.slotLocation) : s = t := by
  cases s
  cases t
  cases allocation
  cases rows
  cases weight
  cases originalIdeal
  cases frequency
  cases extractedFactor
  cases normFactor
  cases row
  cases characters
  cases scale₁
  cases scale₂
  cases base
  cases length
  cases leftWeight
  cases rightWeight
  cases slotWeight
  cases leftLocation
  cases rightLocation
  cases slotLocation
  rfl

set_option maxHeartbeats 2000000 in
theorem extractedPassiveSource_eq (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    seed.extractedPassiveSource input support side a rectangle =
      CanonicalJointAllocatedSource.translateLocations
        (seed.canonicalSource input support side a rectangle)
        (fun _ => seed.plainDivisorTranslation side false)
        (fun _ => seed.plainDivisorTranslation side true)
        (fun _ _ => 0) := by
  have plainWeight₁ (s r : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      seed.occurrences.beforePlainWeight s r false
          ((seed.ordinary.originalAllocation s).plainDivisor 0 * I) =
        (seed.plainProfile input s r false).formula.value 0
          (idealNorm K I / seed.occurrences.plainScale s r false) :=
    seed.beforePlainWeight_quotient input s r false I
  have plainWeight₂ (s r : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      seed.occurrences.beforePlainWeight s r true
          ((seed.ordinary.originalAllocation s).plainDivisor (Fin.succ 0) * I) =
        (seed.plainProfile input s r true).formula.value 0
          (idealNorm K I / seed.occurrences.plainScale s r true) :=
    seed.beforePlainWeight_quotient input s r true I
  have indexFalse (r : Bool) (i : Fin (seed.ordinary.residualSlotCount false)) :
      SlotRestriction.index (seed.ordinary.originalSource false r).allocation.keep i =
        SlotRestriction.index (seed.ordinary.originalAllocation false).keep
          (Fin.cast (seed.residual_count false).symm i) := by
    rfl
  have indexTrue (r : Bool) (i : Fin (seed.ordinary.residualSlotCount true)) :
      SlotRestriction.index (seed.ordinary.originalSource true r).allocation.keep i =
        SlotRestriction.index (seed.ordinary.originalAllocation true).keep
          (Fin.cast (seed.residual_count true).symm i) := by
    rfl
  apply allocatedSource_fields_ext
  · cases side <;> rfl
  · cases side <;> rfl
  · funext h
    cases side with
    | false => exact seed.unscaledOriginal_childWeight false rectangle h
    | true => exact seed.unscaledOriginal_childWeight true rectangle h
  · cases side <;> rfl
  · cases side <;> rfl
  · cases side <;> rfl
  · cases side <;> rfl
  · cases side <;> rfl
  · cases side <;> rfl
  · cases side <;>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations] <;>
      simp only [seed.atoms.scale₁, seed.originalSource_allocation,
        OriginalOccurrenceData.plainScale, Bool.false_eq_true, ite_false]
  · cases side <;>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations] <;>
      simp only [seed.atoms.scale₂, seed.originalSource_allocation,
        OriginalOccurrenceData.plainScale, ite_true]
  · cases side with
    | false => exact seed.atoms.base false rectangle
    | true => exact seed.atoms.base true rectangle
  · funext i
    cases side <;>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations, ActualAllocatedSource.childLength] <;>
      simp only [seed.atoms.length, seed.originalSource_allocation,
        OriginalOccurrenceData.beforeLength, OriginalOccurrenceData.remainingIndex,
        Call.originalLength, slotIndex, indexFalse, indexTrue, Fin.cast_refl]
    all_goals rfl
  · funext h I
    cases side <;>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations] <;>
      simp only [seed.originalSource_allocation, plainWeight₁]
  · funext h I
    cases side <;>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations] <;>
      simp only [seed.atoms.rightWeight, seed.originalSource_allocation, plainWeight₂]
  · funext h i q
    cases side with
    | false =>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations]
      simpa only [seed.atoms.slotWeight, indexFalse]
        using seed.beforeSlotWeight_remaining input false i q
    | true =>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations]
      simpa only [seed.atoms.slotWeight, indexTrue]
        using seed.beforeSlotWeight_remaining input true i q
  · funext h I
    cases side <;>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations] <;>
      simp only [seed.original_leftLocation, seed.originalSource_allocation,
        seed.location_mul, plainDivisorTranslation, Bool.false_eq_true, ite_false]
  · funext h I
    cases side <;>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations] <;>
      simp only [seed.original_rightLocation, seed.originalSource_allocation,
        seed.location_mul, plainDivisorTranslation, ite_true]
  · funext h i q
    cases side <;>
      dsimp only [extractedPassiveSource, PassiveSource.source, unscaledOriginal,
        PassiveSource.withLeftWeight, canonicalSource,
        CanonicalJointAllocatedSource.translateLocations] <;>
      simp only [seed.original_slotLocation, zero_add]

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
