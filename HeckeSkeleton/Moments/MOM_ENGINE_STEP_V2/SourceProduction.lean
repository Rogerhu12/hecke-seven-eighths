import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LeafNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondCoveredSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstReduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentSource

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual source reaches one finite family of literal leaves

The source is the exact prepared Mellin model.  The complete moving
mask, Cartesian coefficient, two original Fourier kernels and four
amplifier valuations are retained.  The first and second common support
and their divisor allocations are independent parts of each finite
label.  The original single pool is chosen before any branch.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

def selectedModel (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) : Node K c.family.omega (targetCharacter K c) :=
  (selectedCall request).model frequency

def selectedInput (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) : OriginalInput c (selectedModel request frequency) request.base :=
  request.originalInput (selectedCall request) frequency

theorem request_base_pos (request : Request c frame Cp Hp hCp hminimum hHp) :
    0 < request.base := by
  sorry

/-- The data constructor contains raw finite leaf polynomials and their
actual transform terminal terms.  It assumes no source inequality. -/
def selectedExpansion (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    HybridExpansion c (selectedModel request frequency) request.base
      (selectedInput request frequency) := by
  sorry

/-- Empty original row carriers remain empty throughout the construction. -/
theorem selectedExpansion_empty (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (hrows : pairedRows (selectedModel request frequency).data
      (selectedModel request frequency).parameters request.base = ∅) :
    (selectedExpansion request frequency).branches = 0 ∧
      (selectedExpansion request frequency).total = 0 := by
  sorry

/-- A zero-slot source takes the direct branch and constructs no prime pool. -/
theorem selectedExpansion_zero_slots (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (hzero : (selectedModel request frequency).data.geometry.slotCount = 0) :
    (selectedExpansion request frequency).pool = ∅ ∧
      ∀ b, (selectedExpansion request frequency).tag b = AmplificationTag.direct := by
  sorry

/-- The two complete transforms prove the inequality on the original
finite source before any leaf or child energy estimate is inserted. -/
theorem selectedExpansion_parent (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (selectedModel request frequency).energy request.base 0 ≤
      (selectedExpansion request frequency).total := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2
