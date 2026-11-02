import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstResidualProfileCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityRelativeScalar

set_option linter.unusedSectionVars false

/-!
# The original first allowance with both residual scalars

The scalar pair is paid together with the actual first Poisson weight.
The original common-radical saving then follows from the original two
Cauchy allowances. No estimate on the Poisson weight alone is required.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep

open CommonSupportMass

open NumberField
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

theorem firstOriginalAllowanceWeight_profile_mul
    (Z parentWidth total rawProfile scalarPair : ℝ) (D E : Ideal (𝓞 K)) :
    firstOriginalAllowanceWeight Z parentWidth total rawProfile D E * scalarPair =
      firstOriginalAllowanceWeight Z parentWidth total (rawProfile * scalarPair) D E := by
  sorry

/-- The complete original first cost supplies the common radical.
`hprofile` is the pointwise original-atom conclusion proved by
`literalOriginalAtoms_first_combined_profile_le`, with the small Mellin
tilt still explicit. -/
theorem firstOriginalAllowanceWeight_mul_le_radical
    (Z parentWidth total rawProfile scalarPair profileCost tilt : ℝ)
    (hZ : 1 < Z) (hcost : 0 ≤ profileCost)
    (hprofile : rawProfile * scalarPair ≤
      profileCost * Z ^ (parentWidth - total + tilt))
    (D E : Ideal (𝓞 K)) (hD : D ≠ 0) (hE : E ≠ 0)
    (hsupport : primeSupport D = primeSupport E) :
    firstOriginalAllowanceWeight Z parentWidth total rawProfile D E * scalarPair ≤
      profileCost * Z ^ tilt / (Ideal.absNorm (commonRadical D E) : ℝ) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstOriginalAllowanceWeight_profile_mul
#print axioms HeckeSkeleton.Moments.EngineStep.firstOriginalAllowanceWeight_mul_le_radical
