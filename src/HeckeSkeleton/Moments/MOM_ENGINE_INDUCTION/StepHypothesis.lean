import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualCompleteSourceFamily

/-!
# The explicit paired-step hypothesis for the actual induction

The source, reflection branches, zero-width terms, finite rank, and final
scalar induction are constructed in this task.  The only remaining input
below produces the strict paired step on those prepared nodes.

The output type is `RecipeMellinStrictFamily`.  Its `outputs` field supplies
`MellinStrictBranchAt`; each of the latter's frequency outputs contains
`Node.EngineOutput`, which is an abbreviation of the owner's unchanged
`EngineStep.PairedEngineConclusion`.  The actual child labels preserve
their `MomentData`, parameters, common positive kernels, and all four
terminal terms.  Its other fields are profile and scalar budgets, not a
bound for a child or for the final source moment.

The backward engine orders and minimum profile coefficient are chosen
after the fixed annulus and reflection schedule, and before the source
preparation chooses its common `Cp` and `Hp`.  The resulting strict family
then chooses its coefficient, height degree, and threshold before any
moving scale, source index, node, or transform frequency.

The producer integration must establish this hypothesis from
`paired_engine_step`, including the support and same-child admissibility
transport required by the prepared family.  Merely possessing an output
for an unrelated admissibility predicate does not discharge it.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable {K : Type} [Field K] [NumberField K]
variable (Ωengine : Type) [MeasurableSpace Ωengine] (c : TargetContext K)

local instance stepReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤

local instance stepReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

/-- Uniform existence of the owner's complete strict outputs on the
actual source family.  The additional data carried by each output are
literal child labels and the original profile/coefficient budgets.
Neither a `RecipeScalarLocalInput` nor a source moment bound is assumed. -/
structure PairedStepHypothesis : Prop where
  outputs : ∀ lower upper : ℝ,
    0 < lower → lower ≤ 1 / 2 → 2 ≤ upper → lower < upper →
    ∀ decay : ℝ, 1 < decay →
    ∀ reflection : ℕ → ℕ,
      (∀ J, J ≤ reflection J ∧ 1 ≤ reflection J) →
      ∃ engine : ℕ → ℕ, ∃ minimumCp : ℝ,
      ∀ Cp Hp : ℝ, 0 < Cp → minimumCp ≤ Cp → 0 ≤ Hp →
        Nonempty (RecipeMellinStrictFamily Ωengine (expansionRecipeRaw K c)
          (actualCompleteSourceBudgetPrimitive c) 1 engine reflection
          decay Cp Hp lower upper)

variable {Ωengine}

/-- Construct both actual local induction inputs from the single-step
hypothesis and the proved source/reflection preparation.  Their common
profile and order choices are fixed before every moving source. -/
theorem actualRecipeScalarInputs_of_step
    (step : PairedStepHypothesis Ωengine c) :
    Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
      (fun _ _ i => i.noSlots) (fun _ _ _ => True)) ∧
    Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
      (fun _ _ i => i) (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty)) := by
  obtain ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
      decay, hdecay, reflection, hreflection, prepared⟩ :=
    actualRecipeCompleteMellinFamily_preparation c
  obtain ⟨engine, minimumCp, outputs⟩ :=
    step.outputs lower upper hlower hlowerSmall hupper hinterval
      decay hdecay reflection hreflection
  obtain ⟨Cp, Hp, hCp, hminimumCp, hHp, inputs⟩ :=
    prepared 1 engine le_rfl minimumCp
  obtain ⟨strict⟩ := outputs Cp Hp hCp hminimumCp hHp
  exact inputs Ωengine strict

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeScalarInputs_of_step
