import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeInduction
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedAnnulusPrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineFinalBudget

/-!
# The finite original numerical boxes for strict source production

The actual slot mesh remains the mesh fixed in the original recipe.
The small analytic cutoff is selected separately by the owner's box.
Its requested loss is the existing source reserve; the explicit mesh
charge in the literal engine mass fits the existing edge budget.

Only the annulus depends on the finite rank. Every box is selected
before the moving data, source height, row and Fourier variables.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global EngineStep
open CanonicalPrimitiveEngineChoices

variable {K : Type} [Field K] [NumberField K] (c : TargetContext K)

/-- The common finite rank count of the original width-two source. -/
def recipeStrictRankBound : ℕ := 6 * (widthBand (recipeInductionSigma c) 2 + 1)

def recipeStrictEngineBox (lower upper : ℝ)
    (hlower : 0 < lower) (hlowerSmall : lower ≤ 1 / 2) (hupper : 2 ≤ upper)
    (rank : ℕ) : Box where
  cap := c.geometry.slots
  widthMax := 2
  paddingMax := recipeInductionSigma c / 16
  lo := clippedAnnulusLower lower upper (recipeStrictRankBound c) rank / 2
  hi := 2 * rankedAnnulusUpper upper (recipeStrictRankBound c) rank
  step := recipeInductionSigma c
  ε := sourceReserve c.family.lamA
  width_nonneg := by norm_num
  padding_nonneg := div_nonneg (recipeInduction_budget (c := c)).1.le (by norm_num)
  lo_pos := div_pos (clippedAnnulusLower_pos hlower _ _) (by norm_num)
  lo_le_one := by
    have h := clippedAnnulusLower_le hlower.le (recipeStrictRankBound c) rank
    linarith
  hi_ge_one := by
    have h := le_mul_of_one_le_right (show 0 ≤ upper by linarith)
      (one_le_pow₀ (n := recipeStrictRankBound c - rank) (show (1 : ℝ) ≤ 2 by norm_num))
    change 1 ≤ 2 * (upper * (2 : ℝ) ^ (recipeStrictRankBound c - rank))
    linarith
  step_pos := (recipeInduction_budget (c := c)).1
  ε_pos := (moment_mesh_engine_bounds c.family.lamA_pos).2.1

/-- The original mesh is paid once inside the already chosen edge loss. -/
theorem recipeStrictEngineBox_mass_budget (lower upper : ℝ)
    (hlower : 0 < lower) (hlowerSmall : lower ≤ 1 / 2) (hupper : 2 ≤ upper)
    (rank : ℕ) :
    (recipeStrictEngineBox c lower upper hlower hlowerSmall hupper rank).ε +
        (momentMesh K c.family).val ≤ recipeInductionEdgeLoss c := by
  have hr := (moment_mesh_engine_bounds c.family.lamA_pos).2.1
  change sourceReserve c.family.lamA + (momentMesh K c.family).val ≤
    sourceReserve c.family.lamA + (momentMesh K c.family).val + sourceReserve c.family.lamA
  linarith

/-- The same original terminal ledger pays the owner's genuine first,
second, exceptional and tail budget. -/
theorem recipeStrictEngineBox_terminal_budget (lower upper : ℝ)
    (hlower : 0 < lower) (hlowerSmall : lower ≤ 1 / 2) (hupper : 2 ≤ upper)
    (rank : ℕ) :
    CanonicalPrimitiveEngineFinalBudget.terminalExponent
        (recipeStrictEngineBox c lower upper hlower hlowerSmall hupper rank) ≤
      recipeInductionTerminalLoss c := by
  have hs := (recipeInduction_budget (c := c)).1
  change recipeInductionSigma c / 16 + 3 * recipeInductionSigma c +
      sourceReserve c.family.lamA ≤
    terminalBudget (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)
      (recipeInductionSigma c) (sourceReserve c.family.lamA)
  unfold terminalBudget
  linarith

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.recipeStrictEngineBox_mass_budget
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.recipeStrictEngineBox_terminal_budget
