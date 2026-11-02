import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4CalibrationContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original N3 calibration supplies the N4 binding

The public N3 specification fixes the actual parameters, moving factors,
remaining mask and finite row dictionary. Projecting those identities
gives the N4 consumption view on the same calibration. The original
S4 pattern stability supplies the packet's one common pattern.

Both task proofs remain explicit parameters. No capacity estimate,
normalized child or additional source hypothesis is introduced here.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep Blueprint

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}

/-- The common pattern follows from the same realized S4 source and
its original row labels, independently of a calibration construction. -/
theorem packetPattern_of_realizes
    (packet : RawLeafPacket call p)
    (hpacket : packet.Realizes) (h : packet.R.live) :
    actualNonunitPattern (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity
      (packet.R.frequency h.val) = CalibrationClass.pattern packet := by
  have hsecond : packet.second.Realizes := by
    rcases hpacket with
      ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
    exact htrace.second.stage
      (raw.covers.classKey (raw.index j).val).sourceIndex
  have hlabel (q : packet.R.live) :
      packet.chart.rowLabel q.val =
        SourceClassKey.rowLabel packet.key :=
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp q.property).1).2
  have hstable (q r : packet.R.live) :
      actualNonunitPattern (Arithmetic.context c) packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity
          (packet.R.frequency q.val) =
        actualNonunitPattern (Arithmetic.context c) packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity
          (packet.R.frequency r.val) :=
    hsecond.patternStable packet.key.1 packet.key.2.1 q.val r.val
      ((hlabel q).trans (hlabel r).symm)
  rw [CalibrationClass.pattern,
    dif_pos (show Nonempty packet.R.live from ⟨h⟩)]
  exact hstable h _

/-- Every field is a projection of the original N3 specification,
except pattern constancy, which is already proved for the same packet. -/
theorem calibrationBinding_of_spec
    (hpacket : packet.Realizes)
    (seed : OrdinarySeed packet) (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    (D : OriginalCalibration call (seed.canonicalSource input support side a rectangle))
    (spec : OriginalCalibrationSpec seed input support side a rectangle D) :
    N4.CalibrationBinding seed support side a rectangle D
      (CalibrationClass.pattern packet) where
  pattern_actual h := packetPattern_of_realizes packet hpacket h
  m := by
    simpa only [CalibrationParameters.parameters, CalibrationParameters.rowExponent]
      using congrArg RealParameters.m spec.parameters
  q := by
    simpa only [CalibrationParameters.parameters, CalibrationParameters.supportExponent,
      CalibrationParameters.rootLength] using congrArg RealParameters.q spec.parameters
  moving := by
    simpa only [CalibrationAtoms.moving] using spec.moving
  remaining := by
    simpa only [CalibrationAtoms.remaining] using spec.remaining
  allowed_exact := spec.allowed_exact
  timeIndependent := spec.timeIndependent
  primeSupport := spec.primeSupport

/-- Consume N3 once and retain both its full specification and the N4
view on that very family; later tasks reuse the same calibrations. -/
theorem calibrations_with_bindings
    (calibration : OriginalCalibrationTask c p)
    (call : Call c) (input : ProfileInput call) (packet : RawLeafPacket call p)
    (hpacket : packet.Realizes)
    (seed : OrdinarySeed packet) (support : seed.ordinary.PassiveSupport input)
    (canonical : seed.CanonicalSupport input support)
    (masks : seed.ResidualMaskIdentity) :
    ∃ C : (seed.refinement input support).Calibrations,
      (∀ side a rectangle,
        OriginalCalibrationSpec seed input support side a rectangle
          (C.side side a rectangle)) ∧
      ∀ side a rectangle,
        N4.CalibrationBinding seed support side a rectangle (C.side side a rectangle)
          (CalibrationClass.pattern packet) := by
  obtain ⟨C, specs⟩ := calibration call input packet hpacket seed support canonical masks
  exact ⟨C, specs, fun side a rectangle =>
    calibrationBinding_of_spec hpacket seed support side a rectangle
      (C.side side a rectangle) (specs side a rectangle)⟩

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.calibrationBinding_of_spec
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.packetPattern_of_realizes
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.calibrations_with_bindings
