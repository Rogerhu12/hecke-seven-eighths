module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPaidRows

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The proved supported row estimate with the actual cutoff loss

The base theorem already consumes volume estimates only on a fixed
positive support window. It keeps the two whole centered sources, the
same sixth-power row count, the exact divisor saving, and the one-sixth
power of the actual physical cutoff loss. T3b reuses this theorem
without duplicating its proof or strengthening its hypotheses.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

export HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalRows
  (exists_original_paired_row_bound_with_cutoff)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b
