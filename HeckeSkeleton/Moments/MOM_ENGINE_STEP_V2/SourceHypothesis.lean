import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.StrictFamily

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exact original paired-step hypothesis

The uniform compact producer is packaged as the existing induction
hypothesis on the actual source. No extra analytic or child-admissibility
premise is added. During the statement-skeleton stage the unfinished
proofs remain in the explicit production and uniform-choice modules.
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

/-- The complete target, with all source constants chosen before every
moving source, recursive node and Mellin or Fourier frequency. -/
theorem pairedStepHypothesis (c : TargetContext K) :
    PairedStepHypothesis EngineParameter c := by
  constructor
  intro lower upper hlower hlowerSmall hupper hinterval decay hdecay reflection hreflection
  let frame : SourceFrame := {
    lower := lower
    upper := upper
    lower_pos := hlower
    lower_small := hlowerSmall
    upper_large := hupper
    interval := hinterval
    decay := decay
    decay_gt_one := hdecay
    reflection := reflection
    reflection_order := hreflection }
  refine ⟨(selectedSchedule c frame).engine, (selectedSchedule c frame).minimumCp, ?_⟩
  intro Cp Hp hCp hminimum hHp
  exact ⟨selectedStrictFamily c frame Cp Hp hCp hminimum hHp⟩

end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.pairedStepHypothesis
