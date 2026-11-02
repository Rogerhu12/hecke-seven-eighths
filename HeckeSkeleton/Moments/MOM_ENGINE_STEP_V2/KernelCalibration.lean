import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFiniteKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TwoDivisorLabelMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The whole finite family has one common positive-kernel budget

The actual first and second common-support counts, both independent
divisor allocations, exact central coefficients and the single pool
density are charged once.  The original per-slot mesh is retained as
part of the induction edge loss.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.ThetaSkeleton.Global
open EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

def selectedKernelBudget (request : Request c frame Cp Hp hCp hminimum hHp) : ℝ :=
  (selectedCall request).engineCoefficient * (selectedCall request).engineControl *
    request.base ^ recipeInductionEdgeLoss c

/-- A scalar majorant for each actual normalized leaf, obtained from
its original atom envelopes and the weighted common Fourier measure. -/
def leafMassBudget (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (b : Fin (selectedExpansion request frequency).branches) : ℝ := by
  sorry

theorem leafMassBudget_nonneg (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (b : Fin (selectedExpansion request frequency).branches) :
    0 ≤ leafMassBudget request frequency b := by
  sorry

theorem leaf_kernel_bound (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (b : Fin (selectedExpansion request frequency).branches) :
    ((selectedNormalization request frequency).measures b).mass ≤
      leafMassBudget request frequency b := by
  sorry

/-- Both divisor density factors survive in this sum; neither is
replaced by a previously normalized Gauss allowance. -/
theorem leafMassBudget_sum (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (∑ b : Fin (selectedExpansion request frequency).branches,
      leafMassBudget request frequency b) ≤ selectedKernelBudget request := by
  sorry

theorem kernel_bound (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (selectedNormalization request frequency).kernels.mass ≤ selectedKernelBudget request := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2
