import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalTerminalPowers

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
  have hprime (p : pool.primes) : 1 ≤ Q p.val := by
    change (1 : ℝ) ≤ (Ideal.absNorm p.val.val.asIdeal : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun he => p.val.val.ne_bot (Ideal.absNorm_eq_zero_iff.mp he))
  rcases tag with u | p | p | p
  · exact Real.one_le_rpow pool.base_gt_one.le pool.exponent_pos.le
  all_goals exact one_le_pow₀ (hprime p)

/-- Separating an original norm charge changes neither its source
nor the denominator of the original shared arithmetic divisor. -/
theorem terminal_amplitude_shift_by_charge
    (Z coefficient divisor exponent length charge : ℝ)
    (hZ : 0 < Z) (hcoefficient : 0 ≤ coefficient) (hdivisor : 0 ≤ divisor)
    (hcharge : Z ^ length ≤ charge) :
    (coefficient / divisor) * Z ^ exponent ≤
      (coefficient * charge / divisor) * Z ^ (exponent - length) := by
  calc
    _ = ((coefficient / divisor) * Z ^ length) * Z ^ (exponent - length) := by
      rw [mul_assoc, ← Real.rpow_add hZ]
      congr 2
      ring
    _ ≤ ((coefficient / divisor) * charge) * Z ^ (exponent - length) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcharge (div_nonneg hcoefficient hdivisor))
        (Real.rpow_nonneg hZ.le _)
    _ = _ := by ring

/-- The original frozen prime power can only increase its logarithmic
length. It is not replaced by the radical of a residual column. -/
theorem original_frozen_length_ge
    (hZ : 1 < Z) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    idealLogLength Z D ≤ idealLogLength Z (D * p.asIdeal ^ n) := by
  have hproduct : D * p.asIdeal ^ n ≠ 0 := mul_ne_zero hD (pow_ne_zero _ p.ne_bot)
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [rpow_idealLogLength Z hZ D hD,
    rpow_idealLogLength Z hZ (D * p.asIdeal ^ n) hproduct]
  exact norm_le_of_dvd hproduct ⟨p.asIdeal ^ n, rfl⟩

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.one_le_poolTagNormCharge
#print axioms HeckeSkeleton.Moments.EngineStep.terminal_amplitude_shift_by_charge
#print axioms HeckeSkeleton.Moments.EngineStep.original_frozen_length_ge
