import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot

/-!
# One finite arithmetic background family before all source indices

A recipe has finitely many polynomial presentations. Their theta sets
are united once, with the identity added, before any source block,
witness, sector, arithmetic row, or Mellin frequency is selected.

The actual moving factors are not put in this finite family. Only the
fixed finite correction belongs to it. Consequently the conductor
constant for the later moving recipes can be selected uniformly without
asserting that theta is closed under multiplication or inversion.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}
variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- This fixed finite set precedes every moving parameter of the recipe. -/
def recipeThetaFamily : Finset (HeckeCharacter K) :=
  insert 1 (Finset.univ.biUnion fun j : Fin R.family.presentationCount =>
    (R.family.presentation j).theta)

theorem mem_recipeThetaFamily (χ : HeckeCharacter K) :
    χ ∈ recipeThetaFamily R ↔
      χ = 1 ∨ ∃ j : Fin R.family.presentationCount, χ ∈ (R.family.presentation j).theta := by
  simp [recipeThetaFamily]

/-- No finite-order assumption is added: each original presentation
already contains the required finite-order proof. -/
theorem recipeThetaFamily_finiteOrder (χ : HeckeCharacter K)
    (hχ : χ ∈ recipeThetaFamily R) : FiniteOrder χ := by
  rcases (mem_recipeThetaFamily R χ).mp hχ with hχ | ⟨j, hj⟩
  · subst χ
    exact IsOfFinOrder.one
  · exact (R.family.presentation j).theta_finite χ hj

theorem recipe_presentation_theta_subset (j : Fin R.family.presentationCount) :
    (R.family.presentation j).theta ⊆ recipeThetaFamily R := by
  intro χ hχ
  exact (mem_recipeThetaFamily R χ).mpr (Or.inr ⟨j, hχ⟩)

/-- Slot restriction and the original physical scale change preserve
the selected presentation, so every actual root uses this same set. -/
theorem recipeRoot_theta_subset {Z T : ℝ}
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) :
    (recipeRoot R i s).data.theta ⊆ recipeThetaFamily R := by
  change (R.family.presentation (_root_.ExpansionRecipe.decodePresentation
    R.family.presentationCount R.family.presentationCount_pos
    ((recipeMomentModels K c R).heights Z T i 4))).theta ⊆ recipeThetaFamily R
  exact recipe_presentation_theta_subset R _

/-- The independent unmarked family has the same finite containment,
even when its scales and all six coordinates are chosen independently. -/
theorem recipeUnmarked_theta_subset (U D : ℝ)
    (s : SixthUnitClasses K (places K c)) (ξ : ExpansionRecipe.RecipeVector)
    (σ τ : NonzeroIdeal K → ExpansionRecipe.RecipeVector) :
    ((recipeMomentModels K c R).unmarked U D s ξ σ τ).theta ⊆ recipeThetaFamily R := by
  change (R.family.presentation (_root_.ExpansionRecipe.decodePresentation
    R.family.presentationCount R.family.presentationCount_pos (ξ 4))).theta ⊆
      recipeThetaFamily R
  exact recipe_presentation_theta_subset R _

end HeckeSkeleton.Moments.EngineInduction.Source
