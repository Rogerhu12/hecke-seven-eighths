import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ExceptionalRecoveryContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ExceptionalContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceIndexContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T3b: whole-centered volume and the original exceptional divisor sum

T3a supplies only the original arithmetic classification. This task
applies supported annular volume to the two whole centered rectangles,
including the absolute estimate when the remaining length is not
positive. It then sums the same two divisors and physical source
indices, retaining the one chosen pool and the original second-divisor
dyad. Its conclusion is the exceptional uniform certificate; no new
absolute envelope or independently selected leaf family is admitted.

Paper: Section 4.8, lines 2967--3002. The base entry points are
`SecondSideFrame.exceptional_original_label_integral_from_atoms`,
`uniform_exceptional_dyad_mass` and
`uniform_amplified_exceptional_dyad_mass`.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

/-- T3b explicitly consumes T3a and the original arithmetic-index
estimate N8a. `ExceptionalTask` is only its uniform-certificate
conclusion, not a separate blueprint obligation. -/
def ExceptionalSummationTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ExceptionalRecoveryTask c p → SourceIndexTask c p → ExceptionalTask c p

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
