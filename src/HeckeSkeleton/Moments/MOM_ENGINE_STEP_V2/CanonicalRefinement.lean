module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One actual residual source and its global profile formula

The source is constructed field by field from the original occurrence
maps. It does not inherit the freely presented profile factors of an
ordinary dictionary. Both sides use one Boolean orientation; neither a
profile scalar nor an external normalizer can be enlarged independently.
The inner allocation scalar and the new passive scalar occur once each.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
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

def slotIndex (side : Bool) (i : Fin (seed.ordinary.residualSlotCount side)) :
    Fin call.node.data.geometry.slotCount :=
  seed.occurrences.remainingIndex side (Fin.cast (seed.residual_count side).symm i)

/-- The right column reverses the second Fourier variable and retains
the actual first-source sign. These are the original joint locations. -/
def logDirection (_seed : OrdinarySeed packet) (side : Bool) : ℝ × ℝ :=
  (-packet.firstSign, if side then 1 else -1)

def profile (kind : ParentProfileKind call) (side : Bool) (scale : ℝ)
    (absent : Bool) : OriginalProfileFormula input where
  kind := kind
  row := seed.reference
  time := 0
  formula := {
    original := kind.representative input seed.reference 0
    conjugate := false
    dilation := 1
    dilation_pos := zero_lt_one
    scalar := if absent then 0 else 1
    power := seed.occurrences.normPower
    phase := seed.logDirection side
    translation := ((seed.logDirection side).1 * Real.log scale,
      (seed.logDirection side).2 * Real.log scale) }
  original := rfl

def plainProfile (side rectangle plain : Bool) : OriginalProfileFormula input :=
  seed.profile input (.plain plain) side (seed.occurrences.plainScale side rectangle plain)
    (rectangle && !call.node.centered && !plain)

def primeProfile (side : Bool) (i : Fin (seed.ordinary.residualSlotCount side)) :
    OriginalProfileFormula input :=
  seed.profile input (.prime (seed.slotIndex side i)) side
    (call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) false

def inverseProfile : OriginalProfileFormula input where
  kind := .inverse
  row := seed.reference
  time := 0
  formula := {
    original := ParentProfileKind.inverse.representative input seed.reference 0
    conjugate := false
    dilation := 1
    dilation_pos := zero_lt_one
    scalar := 1
    power := 0
    phase := 0
    translation := 0 }
  original := rfl

def innerScalar (side : Bool) (h : seed.ordinary.rows.live) : ℂ :=
  (seed.ordinary.originalAllocation side).scalar (σ := Arithmetic.embedding c)
    (seed.phases.characters false (seed.occurrences.secondIndex side))
    ((seed.ordinary.originalSource side false).extractedFactor h)
    ((seed.ordinary.originalSource side false).row h).element call.base
    (seed.occurrences.beforeLength side) (seed.occurrences.beforeSlotWeight side)

def location (side : Bool) (norm : ℝ) : EngineParameter :=
  WithLp.toLp 2 ((seed.logDirection side).1 * Real.log norm,
    (seed.logDirection side).2 * Real.log norm)

/-- This constructor fixes every original arithmetic field, every
single weight and every location. Its only finite allocation is the
actual passive allocation on the displayed smooth carrier. -/
def canonicalSource (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    ActualAllocatedSource (Arithmetic.data c) EngineParameter
      seed.ordinary.rows.live (seed.ordinary.residualSlotCount side) where
  allocation := PassiveAllocation.allocation (support.carrier side) seed.ordinary.passiveMask a
  rows := (seed.ordinary.originalSource side false).rows
  weight h := (seed.ordinary.originalSource side false).weight h * seed.innerScalar side h *
    star (seed.innerScalar side h)
  originalIdeal := (seed.ordinary.originalSource side false).originalIdeal
  frequency := (seed.ordinary.originalSource side false).frequency
  extractedFactor := (seed.ordinary.originalSource side false).extractedFactor
  normFactor := (seed.ordinary.originalSource side false).normFactor
  row := (seed.ordinary.originalSource side false).row
  characters _ := seed.phases.characters true (seed.slotIndex side)
  scale₁ := seed.occurrences.plainScale side rectangle false
  scale₂ := seed.occurrences.plainScale side rectangle true
  base := call.base
  base_gt_one := call.domain.scale
  length i := (call.node.data.geometry.slots (seed.slotIndex side i)).length
  length_pos i := (call.node.data.geometry.slots (seed.slotIndex side i)).length_pos
  leftWeight _ I := (seed.plainProfile input side rectangle false).formula.value 0
    (idealNorm K I / seed.occurrences.plainScale side rectangle false)
  rightWeight _ I := (seed.plainProfile input side rectangle true).formula.value 0
    (idealNorm K I / seed.occurrences.plainScale side rectangle true)
  slotWeight _ i q := (seed.primeProfile input side i).formula.value 0
    ((Ideal.absNorm q.asIdeal : ℝ) /
      call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length)
  leftLocation _ I := seed.location side (idealNorm K I)
  rightLocation _ I := seed.location side (idealNorm K I)
  slotLocation _ _ q := seed.location side (Ideal.absNorm q.asIdeal : ℝ)

def refinement (support : seed.ordinary.PassiveSupport input) :
    RefinementData seed.ordinary input where
  support := support
  source := seed.canonicalSource input support
  allocation := fun _ _ _ => rfl
  base_eq := fun _ _ _ => rfl
  normalizer side _ _ := seed.occurrences.normalizer seed.phases side

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
