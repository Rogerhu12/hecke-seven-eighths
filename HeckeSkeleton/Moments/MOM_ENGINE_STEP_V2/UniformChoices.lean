import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PreparedCall

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform order, coefficient and profile choices

The choice order here is part of the public contract: the source frame
fixes the engine schedule and minimum source coefficient; Cp and Hp
then fix the common engine coefficient, height degree and scale
threshold; only afterward is a moving source request introduced.
Prepared calls contain original profile controls and scalar constants,
and do not contain the engine output being constructed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

local instance uniformReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance uniformReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

/-- Backward orders include both actual Fourier passes and the
Schwartz-to-Euler bridge for the next strict child rank. -/
def selectedSchedule (c : TargetContext K) (frame : SourceFrame) : OrderSchedule := by
  sorry

theorem selectedSchedule_minimumCp_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ (selectedSchedule c frame).minimumCp := by
  sorry

/-- A finite maximum over the rank, branch and side choices is taken
before the moving source scale, original index and node. -/
def selectedBounds (c : TargetContext K) (frame : SourceFrame) (Cp Hp : ℝ)
    (hCp : 0 < Cp) (hminimum : (selectedSchedule c frame).minimumCp ≤ Cp)
    (hHp : 0 ≤ Hp) : UniformBounds := by
  sorry

/-- The same original request with its uniform choices already fixed. -/
abbrev Request (c : TargetContext K) (frame : SourceFrame) (Cp Hp : ℝ)
    (hCp : 0 < Cp) (hminimum : (selectedSchedule c frame).minimumCp ≤ Cp)
    (hHp : 0 ≤ Hp) :=
  SourceRequest c frame (selectedSchedule c frame) Cp Hp
    (selectedBounds c frame Cp Hp hCp hminimum hHp)

variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

/-- The literal node's scheduled Euler profiles choose the actual
Mellin order and positive annulus before any Fourier frequency. -/
def selectedCall (request : Request c frame Cp Hp hCp hminimum hHp) :
    PreparedCall request.parent := by
  sorry

/-- This pays only the outer Mellin scalar and the chosen common
engine coefficient. No source or child moment estimate is assumed. -/
theorem selectedCall_budget (request : Request c frame Cp Hp hCp hminimum hHp) :
    (selectedCall request).mellinCost ≤
      (selectedBounds c frame Cp Hp hCp hminimum hHp).coefficient *
        (1 + request.height) ^
          (selectedBounds c frame Cp Hp hCp hminimum hHp).heightDegree := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2
