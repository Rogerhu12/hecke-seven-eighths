import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawLeafData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FinitePhase

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original finite coefficient outside each normalized leaf

The fixed PUnit ray phase has coefficient one. The leaf keeps exactly
the physical outer multiplier, its original orbit fibre, and its own
inner Mobius coefficient. No norm is moved between the two independent
divisor ledgers.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open HeckePort.IdealMobiusDivisorSum

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

theorem punitPhaseCoefficient_eq_one (χ : (PUnit.{1} × PUnit.{1}) →* Circle) :
    fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)) χ = 1 := by
  have hχ (x : PUnit.{1} × PUnit.{1}) : χ x = 1 := by
    rw [show x = (1 : PUnit.{1} × PUnit.{1}) from Subsingleton.elim _ _, map_one]
  simp [fixedPhaseCoefficient, finiteFourierCoeff, hχ, Nat.card_eq_fintype_card]

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem leaf_weight_eq :
    packet.leaf.weight = packet.second.physical.outerWeight *
      (packet.second.stage.fiber : ℝ) * ‖(moebius packet.allocation.1.val : ℂ)‖ := by
  change (packet.second.physical.outerWeight * (packet.second.stage.fiber : ℝ)) *
    (‖(moebius packet.allocation.1.val : ℂ)‖ *
      ‖fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)) packet.allocation.2.1‖) = _
  rw [punitPhaseCoefficient_eq_one, norm_one, mul_one]

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.punitPhaseCoefficient_eq_one
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.leaf_weight_eq
