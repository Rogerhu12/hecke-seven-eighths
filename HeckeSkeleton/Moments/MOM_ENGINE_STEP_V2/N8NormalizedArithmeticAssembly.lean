import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ArithmeticMassAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksNormalizedMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksSourceIndex

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8: the two proved estimates give the original arithmetic allowance

The same source index is consumed once. Its fixed loss is p.loss,
so its two-loss exponent cancels the two losses retained by N8b.
The coefficient and the maximum threshold are chosen before the
moving call, without rebuilding any normalized or raw label.
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

/-- Both parts of N8, with their actual constructors and original
index, supply one uniform arithmetic-mass allowance. -/
theorem canonicalArithmeticMass (c : TargetContext K) (p : SourceParameters c)
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
  obtain ⟨index⟩ := Tasks.sourceIndex c p frame p.loss p.loss_pos
  obtain ⟨cost, hcost⟩ := Tasks.normalizedMass c p frame
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

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.canonicalArithmeticMass
