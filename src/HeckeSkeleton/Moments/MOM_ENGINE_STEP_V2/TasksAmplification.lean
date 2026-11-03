import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3Assembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3OriginalColumnBound

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S3: independent source proof task

Paper: Section 4.8, lines 2852--2881. The original row and column
windows give one fixed exponent box before the shared prime pool is
chosen. Its literal main and valuation 1/6/7 sources carry the exact
single density charge; the zero-slot case reuses the direct family.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem amplification (c : TargetContext K) (p : SourceParameters c) :
    AmplificationTask c p := by
  exact S3.amplification_of_uniform_column_bound c p
    (S3Proof.uniform_firstColumn_bound c p)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.amplification


