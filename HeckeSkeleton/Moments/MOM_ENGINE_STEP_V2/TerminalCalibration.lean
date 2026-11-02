import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalSupportedVolume
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussRawTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TerminalPowerBudget

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Four separately calibrated terminal contributions

The genuine first zero, full second diagonal, exceptional rows and
whole-frequency tails remain separate.  The exceptional proof uses
the same common-mask residue cancellation before absolute values and
uses the supported-volume alternative for nonpositive formal lengths.
Every bound refers to the original selected expansion.
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

def selectedTerminals (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) : ScalarLedger :=
  (selectedExpansion request frequency).normalizedTerminals (request_base_pos request).le

def selectedTerminalBudget (request : Request c frame Cp Hp hCp hminimum hHp) : ℝ :=
  (selectedCall request).engineCoefficient * (selectedCall request).engineControl *
    request.base ^ recipeInductionTerminalLoss c

theorem firstZero_bound (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (selectedTerminals request frequency).firstZero ≤ selectedTerminalBudget request / 4 := by
  sorry

theorem secondZero_bound (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (selectedTerminals request frequency).secondZero ≤ selectedTerminalBudget request / 4 := by
  sorry

/-- The complete exceptional count and centered cancellation use the
actual support-extracted rows of the same finite leaves. -/
theorem exceptional_bound (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (selectedTerminals request frequency).exceptional ≤ selectedTerminalBudget request / 4 := by
  sorry

/-- The tails are removed as whole common dyads before the finite
coprime extension and Fourier absolute values. -/
theorem tail_bound (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (selectedTerminals request frequency).tail ≤ selectedTerminalBudget request / 4 := by
  sorry

theorem terminal_bound (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (selectedTerminals request frequency).total ≤ selectedTerminalBudget request := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2
