import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitiveFourier
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalConductor
import Mathlib.Tactic.FieldSimp

/-!
# Physical scales of the actual primitive Poisson formula

The conductor norm and divisor norm below are those of the actual
S-integer generators. The factor is not introduced by matching an
exponent: its size follows from the genuine Poisson factor and the
actual finite Gauss sum. The reciprocal radius bound connects norm
support budgets to the bare outer-frequency truncation.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualPoissonScale

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

def fieldConstant : ℝ :=
  (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)|

theorem fieldConstant_nonneg : 0 ≤ fieldConstant K := by
  unfold fieldConstant
  positivity

/-- The actual modulus gives exactly the inverse product radius. -/
theorem primitive_dual_radius (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) :
    (sIntegerMaskDualRadius K S (primitiveModulus K S D B t)
      (primitiveModulus_ne_zero K S D B t) r d).val =
      (r.val * (sIntegerElementNorm K Sset d).val *
        ((primitiveIdeal B.support t).absNorm : ℝ))⁻¹ := by
  simp only [sIntegerMaskDualRadius, sIntegerMaskDilationRadius, primitiveModulus_norm]

/-- The finite Gauss size cancels one square root of the literal
conductor norm in the genuine Poisson prefactor. -/
theorem primitive_prefactor_norm (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) :
    ‖sIntegerMaskPoissonFactor K S (primitiveModulus K S D B t)
      (primitiveModulus_ne_zero K S D B t) r d * primitiveGauss K S D B t‖ =
      fieldConstant K /
        (r.val * (sIntegerElementNorm K Sset d).val *
          Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ)) := by
  have hq : 0 < ((primitiveIdeal B.support t).absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors (primitiveExterior K S B t).val
  have hd := (sIntegerElementNorm K Sset d).property
  have hs := Real.sqrt_pos.mpr hq
  rw [norm_mul, primitiveGauss_norm]
  simp only [sIntegerMaskPoissonFactor, sIntegerMaskDilationRadius,
    primitiveModulus_norm, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (mul_pos r.property hd).le,
    Real.norm_of_nonneg (fieldConstant_nonneg K), Real.norm_of_nonneg hq.le]
  change (r.val * (sIntegerElementNorm K Sset d).val)⁻¹ *
      fieldConstant K * ((primitiveIdeal B.support t).absNorm : ℝ)⁻¹ *
        Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) = _
  have hsimpl : ((primitiveIdeal B.support t).absNorm : ℝ)⁻¹ *
      Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) =
        (Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ))⁻¹ := by
    apply (mul_left_inj' (ne_of_gt hs)).mp
    rw [show ((primitiveIdeal B.support t).absNorm : ℝ)⁻¹ *
        Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) *
          Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) =
        ((primitiveIdeal B.support t).absNorm : ℝ)⁻¹ *
          (Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ)) ^ 2 by ring,
      Real.sq_sqrt hq.le, inv_mul_cancel₀ (ne_of_gt hq), inv_mul_cancel₀ (ne_of_gt hs)]
  calc
    _ = (r.val * (sIntegerElementNorm K Sset d).val)⁻¹ * fieldConstant K *
      (((primitiveIdeal B.support t).absNorm : ℝ)⁻¹ *
        Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ)) := by ring
    _ = _ := by rw [hsimpl]; simp only [div_eq_mul_inv, mul_inv]; ring

/-- At physical row length `Z^M`, the analytic radius is `Z^(-M)`.
The divisor and square-root conductor remain in the denominator. -/
theorem primitive_prefactor_norm_at_row_scale (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (Z M : ℝ) (hZ : 0 < Z) (d : NonzeroRingElements OS) :
    ‖sIntegerMaskPoissonFactor K S (primitiveModulus K S D B t)
      (primitiveModulus_ne_zero K S D B t)
      ⟨Z ^ (-M), Real.rpow_pos_of_pos hZ _⟩ d * primitiveGauss K S D B t‖ =
      fieldConstant K * Z ^ M /
        ((sIntegerElementNorm K Sset d).val *
          Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ)) := by
  rw [primitive_prefactor_norm, Real.rpow_neg hZ.le]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- A support budget for the three actual norm factors supplies the
uniform lower radius used by outer-frequency tail estimates. -/
theorem primitive_dual_radius_lower (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (Z A : ℝ) (hZ : 0 < Z)
    (hbudget : r.val * (sIntegerElementNorm K Sset d).val *
      ((primitiveIdeal B.support t).absNorm : ℝ) ≤ Z ^ A) :
    Z ^ (-A) ≤ (sIntegerMaskDualRadius K S (primitiveModulus K S D B t)
      (primitiveModulus_ne_zero K S D B t) r d).val := by
  rw [primitive_dual_radius, Real.rpow_neg hZ.le]
  have hq : 0 < ((primitiveIdeal B.support t).absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors (primitiveExterior K S B t).val
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hZ A)
    (mul_pos (mul_pos r.property (sIntegerElementNorm K Sset d).property) hq)).mpr hbudget

/-- Separate source annuli imply the required product budget. -/
theorem primitive_dual_radius_lower_of_annuli (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (Z A R E : ℝ) (hZ : 0 < Z)
    (hr : r.val ≤ Z ^ R)
    (hd : (sIntegerElementNorm K Sset d).val ≤ Z ^ E)
    (hq : ((primitiveIdeal B.support t).absNorm : ℝ) ≤ Z ^ A) :
    Z ^ (-(R + E + A)) ≤
      (sIntegerMaskDualRadius K S (primitiveModulus K S D B t)
        (primitiveModulus_ne_zero K S D B t) r d).val := by
  apply primitive_dual_radius_lower K S D B t r d Z (R + E + A) hZ
  rw [Real.rpow_add hZ, Real.rpow_add hZ]
  exact mul_le_mul (mul_le_mul hr hd
    (sIntegerElementNorm K Sset d).property.le (Real.rpow_pos_of_pos hZ R).le)
    hq (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualPoissonScale

end
