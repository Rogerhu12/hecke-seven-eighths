import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalCapacityContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: pure original-calibration identities and capacity task

The primitive N3 binding and the quantified N4 tasks are declared without
importing private capacity proofs. Their fields and quantifiers are the
unchanged actual-source contract: no completed budget or child is an input.
The uniform task exposes the same certificate's exact small scale error,
with its demand selected before the call and every finite source label.

Paper: Section 4.8, lines 2883--2946.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

namespace N4

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable (seed : OrdinarySeed packet) (support : seed.ordinary.PassiveSupport input)
variable (side : Bool) (a : support.labels side) (rectangle : Bool)
variable (D : OriginalCalibration call (seed.canonicalSource input support side a rectangle))
variable (pattern : Fin packet.block.primeCount → Bool)

/-- Each field concerns the actual calibration before any capacity
construction. The normalized old remaining mask keeps all outside-S
primes, and the full second sixth root is retained literally. -/
structure CalibrationBinding : Prop where
  pattern_actual : ∀ h : packet.R.live,
    actualNonunitPattern (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) = pattern
  m : D.calibration.parameters.m = (packet.nominal side).skeleton.nominalRow + 12 * p.loss
  q : D.calibration.parameters.q = (packet.nominal side).skeleton.nominalSupport + 4 * p.loss +
    idealLogLength call.base (secondSixthRootIdeal packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity).val
  moving : D.recipe.moving = (seed.phases.moving true).append
    (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
      (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
      packet.R.rightMultiplicity pattern)
  remaining : D.recipe.remaining =
    remainingMaskIdeal (Arithmetic.data c) call.localizedSource.source.recipe.remaining *
      exteriorMomentIdeal (secondSixthRootIdeal packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity)
  allowed_exact : ∀ ξ u, (D.calibration.data ξ).allowedRow u ↔
    ∃ h ∈ (seed.canonicalSource input support side a rectangle).rows,
      ((seed.canonicalSource input support side a rectangle).row h).momentIdeal = u
  timeIndependent : ∀ ξ, ProfileTimeIndependent (D.calibration.data ξ)
  primeSupport : ∀ ξ, PrimeProfileSupport (D.calibration.data ξ)

end N4

def OriginalCapacityTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (input : ProfileInput call) (packet : RawLeafPacket call p),
    packet.Realizes → ∀ (seed : OrdinarySeed packet)
      (support : seed.ordinary.PassiveSupport input)
      (calibrations : (seed.refinement input support).Calibrations)
      (pattern : Fin packet.block.primeCount → Bool),
    (∀ side a rectangle, N4.CalibrationBinding seed support side a rectangle
      (calibrations.side side a rectangle) pattern) →
    ∃ certificate : OriginalCapacityCertificate seed support calibrations,
      ∀ side a rectangle, (certificate.geometry side a rectangle).pattern = pattern

/-- The fixed-frame demand precedes the call, source and finite labels.
The same original capacity certificate carries both the fixed pattern
and the exact raw scale error on every member of the actual family. -/
def UniformOriginalCapacityTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ frame : SourceFrame, ∃ demand : UniformDemand,
    ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      demand.Ready call input → ∀ packet : RawLeafPacket call p,
      packet.Realizes → ∀ (seed : OrdinarySeed packet)
        (support : seed.ordinary.PassiveSupport input)
        (calibrations : (seed.refinement input support).Calibrations)
        (pattern : Fin packet.block.primeCount → Bool),
      (∀ side a rectangle, N4.CalibrationBinding seed support side a rectangle
        (calibrations.side side a rectangle) pattern) →
      ∃ certificate : OriginalCapacityCertificate seed support calibrations,
        (∀ side a rectangle, (certificate.geometry side a rectangle).pattern = pattern) ∧
        ∀ side a rectangle,
          (certificate.geometry side a rectangle).lengths.rawScaleError = p.loss

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
