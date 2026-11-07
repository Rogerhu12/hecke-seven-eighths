module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyParentEngineOutput

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Empty original rows require no physical source or prime pool -/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

/-- The same original empty row set gives zero children and all four
zero terminal terms. This handles the otherwise vacuous row budgets
before any nonempty-source task is invoked. -/
def emptyOutput (call : Call c) (inactive : ¬call.Active) :
    call.node.EngineOutput (Ω := EngineParameter) call.base
      (recipeInductionSigma c) (recipeInductionEdgeLoss c)
      (recipeInductionTerminalLoss c) call.prepared.engineCoefficient
      call.prepared.engineControl (admissibleOfInvariant call.primitive) := by
  have hrows : pairedRows call.node.data call.node.parameters call.base = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp inactive
  exact PairedEngineConclusion.ofEmptyParent
    call.node.centered call.node.data call.node.parameters
    call.base 0 (call.base ^ call.node.comparison₁) (call.base ^ call.node.comparison₂)
    (recipeInductionSigma c) (recipeInductionEdgeLoss c)
    (recipeInductionTerminalLoss c) call.prepared.engineCoefficient
    call.prepared.engineControl (admissibleOfInvariant call.primitive)
    call.base_pos.le call.prepared.engineCoefficient_nonneg
    call.prepared.engineControl_nonneg hrows

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.emptyOutput
