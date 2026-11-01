import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeThetaFamily
import HeckeSkeleton.ExpansionModels.ActualRowEligibility

/-!
# The actual recipe uses the one canonical finite theta

Both actual presentations have exactly the same canonical theta. The
generic finite union used by the source preparation is therefore equal
to that theta, including when the target character has infinite order.
This identity only identifies the original finite arithmetic set.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global Expansion.Project
open scoped Classical

variable {K : Type} [Field K] [NumberField K] (c : TargetContext K)

theorem actualRecipeThetaFamily :
    recipeThetaFamily (expansionRecipeRaw K c) =
      canonicalDetectorTheta K (targetCharacter K c) := by
  apply Finset.ext
  intro chi
  rw [mem_recipeThetaFamily]
  change (chi = 1 ∨ ∃ j : Fin 2,
    chi ∈ canonicalDetectorTheta K (targetCharacter K c)) ↔
      chi ∈ canonicalDetectorTheta K (targetCharacter K c)
  constructor
  · rintro (rfl | ⟨_, hchi⟩)
    · exact one_mem_canonicalDetectorTheta K (targetCharacter K c)
    · exact hchi
  · intro hchi
    exact Or.inr ⟨0, hchi⟩

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeThetaFamily
