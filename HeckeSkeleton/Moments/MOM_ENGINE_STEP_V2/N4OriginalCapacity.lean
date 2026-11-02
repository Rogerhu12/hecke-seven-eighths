import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalCapacityContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4RecipeBridge

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: original capacity certificates for all sides and rectangles

The source family and calibrations are the actual N2/N3 objects. Their
primitive binding supplies exact identities only. The packet geometry,
complete support budgets and length records are constructed here, and
the original nonunit pattern is retained on every side and rectangle.

Paper: Section 4.8, lines 2883--2946.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep NumberField
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable (seed : OrdinarySeed packet) (support : seed.ordinary.PassiveSupport input)
variable (calibrations : (seed.refinement input support).Calibrations)
variable (pattern : Fin packet.block.primeCount → Bool)
variable (bindings : ∀ side a rectangle,
  CalibrationBinding seed support side a rectangle (calibrations.side side a rectangle) pattern)

/-- Every output is built on the same actual family. Neither a capacity
input nor a normalized child occurs among the hypotheses. -/
def originalCapacityCertificate (hpacket : packet.Realizes) :
    OriginalCapacityCertificate seed support calibrations where
  geometry side a rectangle := geometryOfBinding (bindings side a rectangle) hpacket
  nominal side a rectangle := geometryOfBinding_nominal (bindings side a rectangle) hpacket
  pattern side a rectangle h := (bindings side a rectangle).pattern_actual h
  conditions side a rectangle := conditionsOfBinding (bindings side a rectangle) hpacket
  rowError side a rectangle := geometryOfBinding_rowError (bindings side a rectangle) hpacket
  supportError side a rectangle := geometryOfBinding_supportError (bindings side a rectangle) hpacket
  rawScaleError side a rectangle := geometryOfBinding_rawScaleError (bindings side a rectangle) hpacket

theorem originalCapacityCertificate_pattern (hpacket : packet.Realizes)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    ((originalCapacityCertificate seed support calibrations pattern bindings hpacket).geometry
      side a rectangle).pattern = pattern :=
  geometryOfBinding_pattern (bindings side a rectangle) hpacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.originalCapacityCertificate
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.originalCapacityCertificate_pattern
