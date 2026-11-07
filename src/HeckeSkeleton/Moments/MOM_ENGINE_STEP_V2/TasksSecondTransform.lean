module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondTransformStage
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondTransformIntegral

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S4: independent source proof task

Paper: Section 4.8, lines 2883--2894 and 3004--3010. The complete statement and
its original-source data are in SecondContracts. The proof constructs
the actual stage once per source and sums its exact integrated bound.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global
open scoped BigOperators

variable {K : Type} [Field K] [NumberField K]

theorem secondTransform (c : TargetContext K) (p : SourceParameters c) :
    SecondTransformTask c p := by
  classical
  intro call F _ family _ expansion _ hw
  let second : SecondFamily expansion :=
    ⟨fun i => SecondTransformPrivate.construct (expansion.source i) (hw i)⟩
  refine ⟨second, ?_, ?_⟩
  · exact {
      physical := fun _ => rfl
      stage := fun i => SecondTransformPrivate.construct_realizes
        (expansion.source i) (hw i) }
  · have hpoint (i : Fin expansion.count) :
        (expansion.source i).cost ≤
          (second.source i).zero + (second.source i).tail + (second.source i).nonzero :=
      SecondTransformPrivate.source_cost_le (second.source i)
    simpa only [PoolExpansion.cost, SecondFamily.zero, SecondFamily.tail,
      SecondFamily.nonzero, Finset.sum_add_distrib] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.secondTransform


