import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4NominalScale
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4FrozenIdeals
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4OriginalPrimeWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4InnerScale
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4UniformThreshold
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalCapacityContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the same original scale product spends only the fixed source loss

Both frozen prime lists inherit the original annulus. Their complete
frozen ideals have the exact nominal norm product. The inner allocation
only reduces the remaining scales, and one threshold fixed from the
frame pays all annulus factors. Consequently every capacity certificate
on this same source has rawScaleError equal to the original loss.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
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
variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}

/-- Before the inner allocation, both actual occurrence extractions
already satisfy the nominal degree bound with the fixed source loss. -/
theorem beforeStageProduct_le_nominal (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (D : OriginalOccurrenceData O)
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (ready : (annulusDemand p frame).Ready call input) (side rectangle : Bool) :
    beforeStageProduct D side rectangle ≤
      call.base ^ ((packet.nominal side).skeleton.rawDegree + p.loss) := by
  have hcomp := two_extraction_compensated_le D side rectangle
    (max 1 (2 * call.prepared.upper)) (le_max_left _ _)
    (fun i _ => first_frozen_prime_norm_le input packet side i)
    (fun i _ => second_frozen_prime_norm_le input hpacket D side i)
  exact rawScaleProduct_le_of_compensated hpacket phases side
    (firstFrozenIdeal_eq hpacket side) hcomp
    (uniform_annulus_power_le p frame input hframe ready)

/-- The canonical passive source retains the same bound for every
label and comparison rectangle, including an empty rectangle. -/
theorem canonical_sourceScaleProduct_le (hpacket : packet.Realizes)
    (seed : OrdinarySeed packet) (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) (ready : (annulusDemand p frame).Ready call input)
    (support : seed.ordinary.PassiveSupport input) (side : Bool)
    (a : support.labels side) (rectangle : Bool) :
    sourceScaleProduct (seed.canonicalSource input support side a rectangle) ≤
      call.base ^ ((packet.nominal side).skeleton.rawDegree + p.loss) :=
  (canonical_sourceScaleProduct_le_before seed input support side a rectangle).trans
    (beforeStageProduct_le_nominal hpacket seed.phases seed.occurrences
      frame input hframe ready side rectangle)

/-- This applies to any certificate with the public original-source
identity, not only the private constructor used by N4's task proof. -/
theorem certificate_rawScaleError_eq (hpacket : packet.Realizes)
    (seed : OrdinarySeed packet) (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) (ready : (annulusDemand p frame).Ready call input)
    (support : seed.ordinary.PassiveSupport input)
    (calibrations : (seed.refinement input support).Calibrations)
    (certificate : OriginalCapacityCertificate seed support calibrations)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    (certificate.geometry side a rectangle).lengths.rawScaleError = p.loss := by
  rw [certificate.rawScaleError side a rectangle]
  change sourceRawError (seed.canonicalSource input support side a rectangle)
    (packet.nominal side).skeleton.rawDegree p.loss = p.loss
  exact sourceRawError_eq_of_product_bound (calibrations.side side a rectangle)
    (packet.nominal side).skeleton.rawDegree p.loss
    (canonical_sourceScaleProduct_le hpacket seed frame input hframe ready
      support side a rectangle)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.beforeStageProduct_le_nominal
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.canonical_sourceScaleProduct_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.certificate_rawScaleError_eq
