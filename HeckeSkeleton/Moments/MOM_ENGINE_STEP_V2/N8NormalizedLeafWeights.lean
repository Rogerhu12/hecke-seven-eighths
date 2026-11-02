import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawLeafData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FinitePhase
import Lean.Elab.Command

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option Elab.async false

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

open EngineStep NumberField
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open HeckePort.IdealMobiusDivisorSum

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N8NormalizedLeafWeights checkpoint: before punitPhaseCoefficient_eq_one"
    stderr.flush

theorem punitPhaseCoefficient_eq_one (χ : (PUnit.{1} × PUnit.{1}) →* Circle) :
    fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)) χ = 1 := by
  have hχ (x : PUnit.{1} × PUnit.{1}) : χ x = 1 := by
    rw [show x = (1 : PUnit.{1} × PUnit.{1}) from Subsingleton.elim _ _, map_one]
  simp [fixedPhaseCoefficient, finiteFourierCoeff, hχ, Nat.card_eq_fintype_card]

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N8NormalizedLeafWeights checkpoint: after punitPhaseCoefficient_eq_one"
    stderr.flush

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N8NormalizedLeafWeights checkpoint: before leaf_weight_eq"
    stderr.flush

theorem leaf_weight_eq :
    packet.leaf.weight = packet.second.physical.outerWeight *
      (packet.second.stage.fiber : ℝ) *
        ‖(UniqueFactorizationMonoid.moebius packet.allocation.1.val : ℂ)‖ := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N8NormalizedLeafWeights checkpoint: leaf_weight_eq proof entered"
    stderr.flush
  dsimp only [leaf, secondSourceLeaf, ActualHybridLeaf.scale,
    SourceClassKey.rawLeaf, fullCorrelationHybridLeaf]
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N8NormalizedLeafWeights checkpoint: leaf_weight_eq after weight projection"
    stderr.flush
  run_tac do
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| rw [punitPhaseCoefficient_eq_one, norm_one, mul_one]))
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N8NormalizedLeafWeights checkpoint: leaf_weight_eq after rw"
    stderr.flush

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N8NormalizedLeafWeights checkpoint: after leaf_weight_eq"
    stderr.flush

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.punitPhaseCoefficient_eq_one
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.leaf_weight_eq
