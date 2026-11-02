import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalTerminalPowers

set_option linter.unusedSectionVars false

/-!
# The original pool charges in a sharp terminal amplitude

The main tag moves precisely one pool length from the exponent into
its actual norm charge. The valuation tags retain their full frozen
prime power and have a norm charge at least one. These elementary
identities leave the original shared arithmetic divisor untouched.
-/

noncomputable section
open scoped Classical NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z ell eps)

/-- Every literal main or 1/6/7 norm charge is at least one. -/
theorem one_le_poolTagNormCharge (tag : PoolSourceTag pool) :
    1 ≤ poolTagNormCharge pool tag := by
  sorry

/-- Separating an original norm charge changes neither its source
nor the denominator of the original shared arithmetic divisor. -/
theorem terminal_amplitude_shift_by_charge
    (Z coefficient divisor exponent length charge : ℝ)
    (hZ : 0 < Z) (hcoefficient : 0 ≤ coefficient) (hdivisor : 0 ≤ divisor)
    (hcharge : Z ^ length ≤ charge) :
    (coefficient / divisor) * Z ^ exponent ≤
      (coefficient * charge / divisor) * Z ^ (exponent - length) := by
  sorry

/-- The original frozen prime power can only increase its logarithmic
length. It is not replaced by the radical of a residual column. -/
theorem original_frozen_length_ge
    (hZ : 1 < Z) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    idealLogLength Z D ≤ idealLogLength Z (D * p.asIdeal ^ n) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.one_le_poolTagNormCharge
#print axioms HeckeSkeleton.Moments.EngineStep.terminal_amplitude_shift_by_charge
#print axioms HeckeSkeleton.Moments.EngineStep.original_frozen_length_ge
