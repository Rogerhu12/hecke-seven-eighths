import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineMassChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualOriginalExponent

/-!
# The final common scalar budget

The actual first, second, exceptional and mass estimates have already
fixed their constants before the source. This file combines only those
numbers, preserving two first and two second terminal payments.
-/

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineFinalBudget

open CanonicalPrimitiveEngineChoices

def constant (first second exceptional mass : ℝ) : ℝ :=
  1 + 2 * first + 2 * second + exceptional + mass

def degree (b : Box) (exceptional : ℕ) : ℕ :=
  max (CanonicalPrimitiveEngineMassChoices.degree b) exceptional

def terminalExponent (b : Box) : ℝ := b.paddingMax + 3 * b.step + b.ε

theorem constant_pos {first second exceptional mass : ℝ}
    (hfirst : 0 ≤ first) (hsecond : 0 ≤ second)
    (hexceptional : 0 ≤ exceptional) (hmass : 0 ≤ mass) :
    0 < constant first second exceptional mass := by
  unfold constant
  linarith

theorem terminals_le {first second exceptional mass : ℝ} (hmass : 0 ≤ mass) :
    2 * first + 2 * second + exceptional ≤ constant first second exceptional mass := by
  unfold constant
  linarith

theorem mass_le {first second exceptional mass : ℝ}
    (hfirst : 0 ≤ first) (hsecond : 0 ≤ second) (hexceptional : 0 ≤ exceptional) :
    mass ≤ constant first second exceptional mass := by
  unfold constant
  linarith

theorem second_degree_le (b : Box) (exceptional : ℕ) :
    2 * (b.cap + 2) ≤ degree b exceptional := by
  have h : 2 * (b.cap + 2) ≤ CanonicalPrimitiveEngineMassChoices.degree b := by
    rw [CanonicalPrimitiveEngineMassChoices.degree_eq]
    omega
  exact h.trans (le_max_left _ _)

theorem first_degree_le (b : Box) (exceptional : ℕ) :
    firstDualOriginalProfileDegree b.cap 1 ≤ degree b exceptional := by
  simpa only [firstDualOriginalProfileDegree, Nat.mul_one] using
    second_degree_le b exceptional

theorem mass_degree_le (b : Box) (exceptional : ℕ) :
    CanonicalPrimitiveEngineMassChoices.degree b ≤ degree b exceptional := le_max_left _ _

theorem exceptional_degree_le (b : Box) (exceptional : ℕ) :
    exceptional ≤ degree b exceptional := le_max_right _ _

theorem terminalExponent_pos (b : Box) : 0 < terminalExponent b := by
  have hp := b.padding_nonneg
  have hs := b.step_pos
  have hε := b.ε_pos
  unfold terminalExponent
  positivity

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineFinalBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineFinalBudget.constant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineFinalBudget.first_degree_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineFinalBudget.terminals_le
