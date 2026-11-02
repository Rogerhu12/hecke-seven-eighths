import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingReflectionCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeThetaFamily
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ScheduleCompatibility

/-!
# The moving-row conductor threshold in the unchanged recipe schedule

The finite correction/background constant is fixed before all moving
factors, rows, source indices, scales and Fourier parameters. It uses the
same reserve fraction as the original reflection construction. Moving
factors contribute only their actual displayed-support norm budget.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

/-- The fixed theta family is an input before the common threshold.
It is not selected from an individual moving character or row. -/
theorem recipe_moving_reflection_conductor_threshold {ε : ℝ} (hε : 0 < ε)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (ψ : HeckeCharacter K) (theta : Finset (HeckeCharacter K)) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      movingReflectionConductorConstant S ψ theta ≤ U ^ (sourceReserve ε / 8) ∧
        2 ≤ U ^ (sourceReserve ε / 8) := by
  have hr := (moment_mesh_engine_bounds hε).2.1
  exact reflection_constant_threshold (movingReflectionConductorConstant_pos S ψ theta)
    (by positivity) (by positivity)

namespace Source

variable {c : TargetContext K}

/-- Every source presentation shares this one threshold, including the
independent unmarked family and all later original moving-row recipes. -/
theorem recipe_source_moving_conductor_threshold
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c)) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      movingReflectionConductorConstant (places K c) (targetCharacter K c)
        (recipeThetaFamily R) ≤ U ^ (sourceReserve c.family.lamA / 8) ∧
      2 ≤ U ^ (sourceReserve c.family.lamA / 8) :=
  recipe_moving_reflection_conductor_threshold c.family.lamA_pos
    (places K c) (targetCharacter K c) (recipeThetaFamily R)

end Source

end HeckeSkeleton.Moments.EngineInduction
