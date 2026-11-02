import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T2: uniform second-zero estimate

Paper: Section 4.8, lines 3004--3010, after the second transform in
lines 2883--2894. Bound the genuine zero contribution of every amplified
physical source, under its original first Fourier measure, and sum the
exact finite indices and one common pool density.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem secondZero (c : TargetContext K) (p : SourceParameters c) :
    SecondZeroTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.secondZero
