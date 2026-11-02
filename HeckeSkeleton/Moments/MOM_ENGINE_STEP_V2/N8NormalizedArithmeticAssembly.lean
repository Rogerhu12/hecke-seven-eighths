import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedArithmeticFromTasks
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksNormalizedMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksSourceIndex

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8: the two proved estimates give the original arithmetic allowance

The public endpoint supplies the proved N8a and N8b tasks to the pure
assembly helper. The coefficient and maximum threshold precede the
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
              call.base ^ (recipeInductionEdgeLoss c / 2) :=
  canonicalArithmeticMass_of_tasks c p
    (Tasks.sourceIndex c p) (Tasks.normalizedMass c p) frame

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.canonicalArithmeticMass
