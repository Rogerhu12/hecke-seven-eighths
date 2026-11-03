import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original parent normalization for the actual terminal expressions

Every source terminal is divided by the same original parent width.
The working full-support parameters retain that width. These operations
are actual scalar definitions and elementary positivity identities.
-/

noncomputable section
open scoped BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

def parentNormalizer (call : Call c) : ℝ :=
  call.base ^ (call.node.parameters.m + call.node.parameters.q)

def normalizedScalar (call : Call c) (value : ℝ) : ℝ :=
  value / call.parentNormalizer

theorem parentNormalizer_pos (call : Call c) : 0 < call.parentNormalizer :=
  Real.rpow_pos_of_pos call.base_pos _

theorem normalizedScalar_nonneg (call : Call c) {value : ℝ} (hvalue : 0 ≤ value) :
    0 ≤ call.normalizedScalar value :=
  div_nonneg hvalue call.parentNormalizer_pos.le

theorem normalizedScalar_add (call : Call c) (left right : ℝ) :
    call.normalizedScalar (left + right) =
      call.normalizedScalar left + call.normalizedScalar right :=
  add_div _ _ _

theorem normalizedScalar_energy (call : Call c) :
    call.normalizedScalar (call.node.energy call.base 0) =
      call.node.normalizedEnergy call.base 0 := rfl

end Call

namespace FirstPresentation

def normalizedZero (F : FirstPresentation call p) : ℝ := call.normalizedScalar F.zero

def normalizedTail (F : FirstPresentation call p) : ℝ := call.normalizedScalar F.tail

theorem normalizedZero_nonneg (F : FirstPresentation call p) : 0 ≤ F.normalizedZero := by
  apply call.normalizedScalar_nonneg
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem normalizedTail_nonneg (F : FirstPresentation call p) : 0 ≤ F.normalizedTail := by
  apply call.normalizedScalar_nonneg
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

end FirstPresentation
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
