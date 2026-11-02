import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CallData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform preparation contains original inputs only

The analytic tasks first choose their own fixed orders, coefficients and
thresholds. A later uniform-choice task uses those particular witnesses
to construct this data by finite maxima and backward profile propagation.
This record does not assert that arbitrary numerical choices suffice,
and contains no source expansion, normalized family or engine output.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

structure UniformPreparation (c : TargetContext K) (frame : SourceFrame) where
  schedule : OrderSchedule
  bounds : ∀ (Cp Hp : ℝ), 0 < Cp → schedule.minimumCp ≤ Cp → 0 ≤ Hp → UniformBounds
  prepared : ∀ (Cp Hp : ℝ) (hCp : 0 < Cp) (hminimum : schedule.minimumCp ≤ Cp)
    (hHp : 0 ≤ Hp),
    ∀ request : SourceRequest c frame schedule Cp Hp (bounds Cp Hp hCp hminimum hHp),
      PreparedCall request.parent
  budget : ∀ (Cp Hp : ℝ) (hCp : 0 < Cp) (hminimum : schedule.minimumCp ≤ Cp)
    (hHp : 0 ≤ Hp),
    ∀ request : SourceRequest c frame schedule Cp Hp (bounds Cp Hp hCp hminimum hHp),
      (prepared Cp Hp hCp hminimum hHp request).mellinCost ≤
        (bounds Cp Hp hCp hminimum hHp).coefficient *
          (1 + request.height) ^ (bounds Cp Hp hCp hminimum hHp).heightDegree

namespace UniformPreparation

variable {c : TargetContext K} {frame : SourceFrame}
variable (preparation : UniformPreparation c frame)

abbrev Request (Cp Hp : ℝ) (hCp : 0 < Cp)
    (hminimum : preparation.schedule.minimumCp ≤ Cp) (hHp : 0 ≤ Hp) :=
  SourceRequest c frame preparation.schedule Cp Hp
    (preparation.bounds Cp Hp hCp hminimum hHp)

/-- A later frequency changes only the literal Mellin model; all
uniform numerical witnesses were already selected. -/
def toCall {Cp Hp : ℝ} {hCp : 0 < Cp}
    {hminimum : preparation.schedule.minimumCp ≤ Cp} {hHp : 0 ≤ Hp}
    (request : preparation.Request Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ) :
    Call c where
  frame := frame
  schedule := preparation.schedule
  Cp := Cp
  Hp := Hp
  bounds := preparation.bounds Cp Hp hCp hminimum hHp
  request := request
  prepared := preparation.prepared Cp Hp hCp hminimum hHp request
  frequency := frequency

end UniformPreparation
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
