import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TerminalContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.BudgetAssembly

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The four separate terminal tasks pay their same original source

All four proofs are explicit parameters. Their numerical witnesses
are selected before the uniform preparation. The later estimates apply
to the same source trace and the same actual exceptional predicate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]

def terminalCertificates (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c)
    (first : FirstZeroTask c p) (second : SecondZeroTask c p)
    (exceptional : ExceptionalTask c p) (tail : TailTask c p) :
    TerminalCertificates c frame p where
  first := Classical.choice (first frame)
  second := Classical.choice (second frame)
  exceptional := Classical.choice (exceptional frame)
  tail := Classical.choice (tail frame)

variable {c : TargetContext K} {frame : SourceFrame} {p : SourceParameters c}

theorem source_terminal_budget (certificates : TerminalCertificates c frame p)
    (arithmeticMass profileMass : Finset (ℕ × ℕ) → UniformCost)
    (demand : Finset (ℕ × ℕ) → UniformDemand)
    (call : Call c)
    (input : PreparedEstimates
      ((certificates.costs arithmeticMass profileMass).withDemand demand) call)
    (hframe : call.frame = frame)
    (trace : SourceTrace call p) (htrace : trace.Realizes)
    (geometry : GeometryFamily trace.second) (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes) :
    trace.first.normalizedZero + trace.second.normalizedZero + raw.normalizedExceptional +
      (trace.first.normalizedTail + trace.second.normalizedTail) ≤
        call.prepared.engineCoefficient * call.prepared.engineControl *
          call.base ^ recipeInductionTerminalLoss c := by
  exact terminal_budget input _ _ _ _
    (certificates.first.bound call input.profile hframe
      (UniformCost.ready_of_withDemand input.firstZero_ready) trace.first htrace.first)
    (certificates.second.bound call input.profile hframe
      (UniformCost.ready_of_withDemand input.secondZero_ready) trace htrace)
    (certificates.exceptional.bound call input.profile hframe
      (UniformCost.ready_of_withDemand input.exceptional_ready)
      trace htrace geometry hgeometry raw hraw)
    (certificates.tail.bound call input.profile hframe
      (UniformCost.ready_of_withDemand input.tail_ready) trace htrace)

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.terminalCertificates
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.source_terminal_budget
