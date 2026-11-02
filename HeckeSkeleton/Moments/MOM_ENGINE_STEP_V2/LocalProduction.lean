import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TerminalCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.KernelCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.Output

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Assemble the compact output on the literal prepared source

The four terminal bounds and full kernel mass refer to the very same
source expansion, normalized children and shared measures.  This
constructor only assembles the proved intermediate obligations; no
parent estimate or final induction estimate enters its assumptions.
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

def selectedOutput (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    Output (selectedNormalization request frequency).Label EngineParameter
      (selectedModel request frequency).centered (selectedModel request frequency).data
      (selectedModel request frequency).parameters request.base 0
      (request.base ^ (selectedModel request frequency).comparison₁)
      (request.base ^ (selectedModel request frequency).comparison₂)
      (recipeInductionSigma c) (recipeInductionEdgeLoss c) (recipeInductionTerminalLoss c)
      (selectedCall request).engineCoefficient (selectedCall request).engineControl
      (admissibleOfInvariant request.primitive) where
  children := (selectedNormalization request frequency).children
  kernels := (selectedNormalization request frequency).kernels
  terminals := selectedTerminals request frequency
  terminal_bound := terminal_bound request frequency
  parent_bound := selectedNormalization_parent request frequency
  mass_bound := kernel_bound request frequency

end HeckeSkeleton.Moments.EngineStepV2
