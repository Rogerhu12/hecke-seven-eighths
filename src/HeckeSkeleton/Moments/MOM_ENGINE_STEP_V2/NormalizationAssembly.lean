module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The ordinary source budget reaches the same actual child kernels

The finite atom controls are explicit inputs. The inequality is the
merged base theorem, including the same whole-slot removal and original
two Fourier measures. This assembly file imports no unfinished task.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable (N : NormalizedData call) {J₁₁ J₁₂ J₂₁ J₂₂ : ℕ}

theorem sourceBudget_le_childBudget
    (atoms : N.family.FourierAtomControl N.labels J₁₁ J₁₂ J₂₁ J₂₂) :
    N.sourceBudget ≤ N.childBudget := by
  have h := atoms.source_integral N.firstKernel N.secondKernel N.outer
    N.parentWidth call.base_pos (fun b _ => N.outer_nonneg b)
  simpa only [NormalizedData.sourceBudget, NormalizedData.childBudget,
    NormalizedData.kernel, ActualNormalizedPairFamily.childPair_eq_frozen] using h

/-- The original producer has only to reach the unnormalized source
budget. The capacity and kernel step is discharged here from base. -/
theorem parentBound_of_sourceBound
    (atoms : N.family.FourierAtomControl N.labels J₁₁ J₁₂ J₂₁ J₂₂)
    (firstZero secondZero exceptional tail : ℝ)
    (hsource : N.ParentSourceBound firstZero secondZero exceptional tail) :
    N.ParentBound firstZero secondZero exceptional tail :=
  hsource.trans (add_le_add (le_refl _) (sourceBudget_le_childBudget N atoms))

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.sourceBudget_le_childBudget
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.parentBound_of_sourceBound
