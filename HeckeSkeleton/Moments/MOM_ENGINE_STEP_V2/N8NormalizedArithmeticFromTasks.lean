import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ArithmeticMassAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedMassContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8: pure assembly from the two task contracts

The same source index is consumed once. Its fixed loss is p.loss,
so its two-loss exponent cancels the two losses retained by N8b.
This helper depends only on the pure contracts. Its task arguments
can be supplied by the public proof wrappers or by the B assembly.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open Blueprint EngineStep EngineInduction.Source
open NumberField HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]

/-- The N8 task contracts supply one uniform arithmetic-mass
allowance for the same actual canonical family and original index. -/
theorem canonicalArithmeticMass_of_tasks (c : TargetContext K) (p : SourceParameters c)
    (hindex : SourceIndexTask c p) (hmass : NormalizedMassTask c p)
    (frame : SourceFrame) :
    ∃ cost : UniformCost,
      ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
        cost.Ready call input → ∀ (trace : SourceTrace call p), trace.Realizes →
        ∀ geometry : GeometryFamily trace.second, geometry.Realizes →
        ∀ raw : RawFamily geometry, raw.Realizes →
        ∀ (choices : FullKappaChoices c p.loss)
          (packets : ∀ j : Fin raw.count, CanonicalMassPacket (raw.packet j) input choices),
          (canonicalMassData raw input choices packets).arithmeticMass ≤
            cost.value input.amplitude call.request.height *
              call.base ^ (recipeInductionEdgeLoss c / 2) := by
  obtain ⟨index⟩ := hindex frame p.loss p.loss_pos
  obtain ⟨cost, hcost⟩ := hmass frame
  refine ⟨index.combinedCost cost, ?_⟩
  intro call input hframe ready trace htrace geometry hgeometry raw hraw choices packets
  have reduction := hcost call input hframe
    (SourceIndexCertificate.ready_original ready) trace htrace geometry hgeometry raw hraw
    choices packets
  apply arithmeticMass_of_sourceIndex index cost call input hframe ready trace htrace
    geometry hgeometry raw hraw (canonicalMassData raw input choices packets)
  simpa only [show recipeInductionEdgeLoss c / 2 - p.loss - p.loss =
    recipeInductionEdgeLoss c / 2 - 2 * p.loss by ring] using reduction

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.canonicalArithmeticMass_of_tasks
