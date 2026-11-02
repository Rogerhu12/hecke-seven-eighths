import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalOriginalIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalPoolAllowanceTransport

set_option linter.unusedSectionVars false

/-!
# The exact divisor saving is the original harmonic index weight

The literal exceptional source retains the logarithm of its actual
allocation divisor. Its saving is therefore the exact harmonic
denominator already used by the same original arithmetic carrier.
No new dyadic rounding or divisor count is needed. The amplified
identity preserves the same pool, valuation and moving-prime weight.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace CommonSupportMass.TwoDivisorCommonBranch

/-- Use the exact original divisor logarithm, preserving every other
coordinate of the same dependent arithmetic index. -/
theorem exceptionalDyadWeight_at_divisor
    (b : TwoDivisorCommonBranch (K := K)) (Z : ℝ) (hZ : 1 < Z)
    (i : b.Index) (hdivisor : i.2.2.2.1.val ≠ 0) :
    b.exceptionalDyadWeight Z (idealLogLength Z i.2.2.2.1.val) i =
      b.indexWeight i := by
  sorry

end CommonSupportMass.TwoDivisorCommonBranch

variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- The same exact denominator survives the original main/1/6/7
pool multiplier. There is no density comparison in this identity. -/
theorem amplifiedExceptionalDyadWeight_at_divisor
    (pool : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    (i : AmplifiedCommonIndex pool main error)
    (hdivisor : amplifiedInnerDivisor i ≠ 0) :
    amplifiedExceptionalDyadWeight pool M B main error
        (idealLogLength Z (amplifiedInnerDivisor i)) i =
      amplifiedIndexWeight pool M B main error i := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.exceptionalDyadWeight_at_divisor
#print axioms HeckeSkeleton.Moments.EngineStep.amplifiedExceptionalDyadWeight_at_divisor
