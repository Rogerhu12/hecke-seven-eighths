import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalOccurrenceData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralLocations

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Proposed global atom fields for the ordinary seed

Every right-hand side below is computed from the original call and its
two occurrence extractions. No calibration or energy estimate is an
input. The complex common scalar sits in the first plain weight of the
ordinary frame. N2 moves this same scalar outside its new source; it is
not the positive real Gauss normalizer of `SecondSideFrame`.

The old inner divisor allocation is kept. Its frozen scalar is paid in
the source child weight, separately from this common scalar.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField DedekindZetaZeroFree
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

namespace OrdinaryData

variable {packet : RawLeafPacket call p} (O : OrdinaryData packet)

def originalSource (side rectangle : Bool) :
    ActualAllocatedSource (Arithmetic.data c) EngineParameter O.rows.live
      (O.originalSlotCount side) := by
  cases side
  · exact (O.leftFrame rectangle).source
  · exact (O.rightFrame rectangle).source

def originalGaussNormalizer (side rectangle : Bool) : ℂ :=
  if side then (O.rightFrame rectangle).normalizer
  else (O.leftFrame rectangle).normalizer

end OrdinaryData

namespace OriginalOccurrenceData

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (D : OriginalOccurrenceData O)

/-- This is a global function of the normalized norm argument, using
the original row-independent norm profile from the call. -/
def plainProfile (plain : Bool) (x : ℝ) : ℂ :=
  (if plain then call.localizedNormProfiles.right PUnit.unit 0 x
   else call.localizedNormProfiles.left PUnit.unit 0 x) *
    ((x ^ D.normPower : ℝ) : ℂ)

def beforePlainWeight (side rectangle plain : Bool) (I : NonzeroIdeal K) : ℂ :=
  if rectangle && !call.node.centered && !plain then 0 else
    D.plainProfile plain (idealNorm K I / D.beforePlainScale side rectangle plain)

def originalCharacters (P : OriginalPhaseData packet) (side : Bool) :=
  P.characters false (D.secondIndex side)

end OriginalOccurrenceData

/-- Proposed extra field of `OrdinarySeed`: bind the actual frame's
single-atom fields on all ideals and primes, before any finite support
restriction or Fourier integration. -/
structure OriginalAtomBinding {packet : RawLeafPacket call p}
    (O : OrdinaryData packet) (P : OriginalPhaseData packet)
    (D : OriginalOccurrenceData O) : Prop where
  base : ∀ side rectangle, (O.originalSource side rectangle).base = call.base
  scale₁ : ∀ side rectangle, (O.originalSource side rectangle).scale₁ =
    D.beforePlainScale side rectangle false
  scale₂ : ∀ side rectangle, (O.originalSource side rectangle).scale₂ =
    D.beforePlainScale side rectangle true
  length : ∀ side rectangle i,
    (O.originalSource side rectangle).length i = D.beforeLength side i
  characters : ∀ side rectangle h,
    (O.originalSource side rectangle).characters h = D.originalCharacters P side
  leftWeight : ∀ side rectangle h I,
    (O.originalSource side rectangle).leftWeight h I =
      D.normalizer P side * D.beforePlainWeight side rectangle false I
  rightWeight : ∀ side rectangle h I,
    (O.originalSource side rectangle).rightWeight h I =
      D.beforePlainWeight side rectangle true I
  slotWeight : ∀ side rectangle h i q,
    (O.originalSource side rectangle).slotWeight h i q = D.beforeSlotWeight side i q
  leftLocation : ∀ side rectangle h I,
    (O.originalSource side rectangle).leftLocation h I =
      if side then -CanonicalLiteralLocations.plain packet.firstSign I
      else CanonicalLiteralLocations.plain packet.firstSign I
  rightLocation : ∀ side rectangle h I,
    (O.originalSource side rectangle).rightLocation h I =
      if side then -CanonicalLiteralLocations.plain packet.firstSign I
      else CanonicalLiteralLocations.plain packet.firstSign I
  slotLocation : ∀ side rectangle h i q,
    (O.originalSource side rectangle).slotLocation h i q =
      if side then -CanonicalLiteralLocations.prime packet.firstSign i q
      else CanonicalLiteralLocations.prime packet.firstSign i q
  gaussNormalizer : ∀ side rectangle, O.originalGaussNormalizer side rectangle = 1

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
