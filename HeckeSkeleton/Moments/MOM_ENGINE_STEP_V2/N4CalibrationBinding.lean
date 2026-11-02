import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4PacketGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the primitive identities consumed from the same N3 calibration

This is a consumption view of the actual N3 dictionary, not an extra
capacity hypothesis. Its fields identify the original pattern, m/q,
moving factors, remaining mask and finite row image. They contain no
support budget, full-joint budget, width estimate or normalized child.
The complete N3 contract additionally retains its global profile formulas
and all single-atom data identities.
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

theorem sixthRootIdeal_swap {A : SArithmeticData K} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (primes : ι → ExteriorPrime A) (m n : ι → ℕ) :
    secondSixthRootIdeal primes n m = secondSixthRootIdeal primes m n := by
  unfold secondSixthRootIdeal
  apply congrArg (primePowerProduct primes)
  funext i
  rw [min_comm]

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem sixthRootLength_eq {H ι : Type} [Fintype ι] [DecidableEq ι]
    (R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι)
    (side : Bool) (Z : ℝ) :
    sixthRootLength R side Z =
      idealLogLength Z (secondSixthRootIdeal R.primes
        R.leftMultiplicity R.rightMultiplicity).val := by
  cases side
  · rfl
  · change idealLogLength Z
        (secondSixthRootIdeal R.primes R.rightMultiplicity R.leftMultiplicity).val = _
    rw [sixthRootIdeal_swap]

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

variable {seed support side a rectangle D pattern}
variable (binding : CalibrationBinding seed support side a rectangle D pattern)

/-- The actual source trace discharges every pattern and tag premise;
the N3 binding supplies only the exact parameters of the same data. -/
def geometryOfBinding (hpacket : packet.Realizes) :
    SideGeometryData packet.R side
      (seed.canonicalSource input support side a rectangle) D := by
  let h : packet.R.live := Classical.choice (packet_live_nonempty packet hpacket)
  have hm : D.calibration.parameters.m = rowParameter (packet.nominal side) (12 * p.loss) :=
    binding.m
  have hq : D.calibration.parameters.q = supportParameter (packet.nominal side)
      (4 * p.loss) (sixthRootLength packet.R side call.base) := by
    rw [supportParameter, sixthRootLength_eq]
    exact binding.q
  exact sideGeometry packet.R side (seed.canonicalSource input support side a rectangle)
    D p (packet.nominal side) pattern
    (packet_leftMultiplicity_pos packet) (packet_rightMultiplicity_pos packet)
    (packet_second_ideal packet hpacket side) (packet_opposite_ideal packet hpacket side)
    (packet_unit_pattern packet hpacket side pattern h (binding.pattern_actual h))
    hm hq (packet_direct_parent_zero packet hpacket side)

theorem geometryOfBinding_nominal (hpacket : packet.Realizes) :
    (geometryOfBinding binding hpacket).nominal = packet.nominal side := by
  rfl

theorem geometryOfBinding_pattern (hpacket : packet.Realizes) :
    (geometryOfBinding binding hpacket).pattern = pattern := by
  rfl

theorem geometryOfBinding_rowError (hpacket : packet.Realizes) :
    (geometryOfBinding binding hpacket).lengths.scales.rowError = 12 * p.loss := by
  rfl

theorem geometryOfBinding_supportError (hpacket : packet.Realizes) :
    (geometryOfBinding binding hpacket).lengths.scales.supportError = 4 * p.loss := by
  rfl

theorem geometryOfBinding_rawScaleError (hpacket : packet.Realizes) :
    (geometryOfBinding binding hpacket).lengths.rawScaleError =
      sourceRawError (seed.canonicalSource input support side a rectangle)
        (packet.nominal side).skeleton.rawDegree p.loss := by
  rfl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.sixthRootLength_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.geometryOfBinding
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.geometryOfBinding_rawScaleError
