import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OutputAssembly

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Reuse the exact normalized family in the original engine conclusion

This final local adapter only unfolds the shared data package. It does
not select new labels, children, measures or numerical estimates.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)} {J₁₁ J₁₂ J₂₁ J₂₂ : ℕ}

def normalizedOutput (N : NormalizedData call)
    (geometry : N.family.OutputGeometry N.labels call.node.data call.node.parameters
      (recipeInductionSigma c) rowDomain window seminorms)
    (atoms : N.family.FourierAtomControl N.labels J₁₁ J₁₂ J₂₁ J₂₂)
    (admissible : N.RecursiveAdmissible)
    (firstZero secondZero exceptional tail : ℝ)
    (hfirstZero : 0 ≤ firstZero) (hsecondZero : 0 ≤ secondZero)
    (hexceptional : 0 ≤ exceptional) (htail : 0 ≤ tail)
    (hterminals : firstZero + secondZero + exceptional + tail ≤
      call.prepared.engineCoefficient * call.prepared.engineControl *
        call.base ^ recipeInductionTerminalLoss c)
    (hparent : N.ParentBound firstZero secondZero exceptional tail)
    (hmass : N.MassBound call.prepared.engineCoefficient call.prepared.engineControl
      (recipeInductionEdgeLoss c)) :
    call.node.EngineOutput (Ω := EngineParameter) call.base
      (recipeInductionSigma c) (recipeInductionEdgeLoss c)
      (recipeInductionTerminalLoss c) call.prepared.engineCoefficient
      call.prepared.engineControl (admissibleOfInvariant call.primitive) :=
  engineOutput call N.family N.labels geometry atoms
    N.firstKernel N.secondKernel N.outer admissible.1 admissible.2
    firstZero secondZero exceptional tail hfirstZero hsecondZero hexceptional htail
    hterminals hparent hmass

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.normalizedOutput
