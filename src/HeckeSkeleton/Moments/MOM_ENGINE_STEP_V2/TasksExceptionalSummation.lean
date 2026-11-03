import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bUniformNormalizer

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T3b: supported volume and summation of the original exceptional source

The arithmetic recovery and original index-mass theorems are the two
frozen premises. The proof retains both whole centered polynomials,
both actual Fourier kernels, both independent divisors, all four
valuation branches and the same pool. The original absolute source
bound covers nonpositive residual lengths. All analytic, profile and
normalization witnesses are fixed before the moving call and leaf.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem exceptional_summation (c : TargetContext K) (p : SourceParameters c) :
    ExceptionalSummationTask c p := by
  apply T3b.exceptionalSummation_of_normalizer
  intro frame
  exact ⟨T3b.normalizerConstant c p frame, T3b.normalizerConstant_nonneg c p frame,
    T3b.normalizer_bound c p frame⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.exceptional_summation
