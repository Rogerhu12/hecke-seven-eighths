module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# A witness that the two radial signs give different Gamma quotients

The witness lies at a zero of the reciprocal Gamma factor. Thus the statement
uses Mathlib's total Gamma function consistently: `Gamma 0 = 0` and division
by that value is zero. The numerator Gamma factors have positive real part.
For the opposite radial sign, both denominator Gamma arguments have nonzero
imaginary part, so the opposite quotient is nonzero.

This is an algebraic special-function distinction. No assertion is made that
the literal Bessel Mellin integrals converge at this witness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HeckeSkeleton.ThetaLocal.Project

/-- The local Gamma quotient occurring in `Global.reflectionMultiplier`. -/
def radialGammaQuotient (a ρ : ℝ) (s : ℂ) : ℂ :=
  (Complex.Gamma ((a : ℂ) + s + Complex.I * ρ - 1 / 6) *
    Complex.Gamma ((a : ℂ) + s + Complex.I * ρ + 1 / 6)) /
  (Complex.Gamma ((a : ℂ) - s - Complex.I * ρ - 1 / 6) *
    Complex.Gamma ((a : ℂ) - s - Complex.I * ρ + 1 / 6))

/-- The first zero arising from the denominator Gamma pair. -/
def radialSignWitness (a ρ : ℝ) : ℂ :=
  (a : ℂ) - 1 / 6 - Complex.I * ρ

theorem gamma_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  apply hz
  have h := congrArg Complex.im hn
  simpa using h

theorem radialGammaQuotient_at_witness (a ρ : ℝ) :
    radialGammaQuotient a ρ (radialSignWitness a ρ) = 0 := by
  unfold radialGammaQuotient radialSignWitness
  have hz : (a : ℂ) - ((a : ℂ) - 1 / 6 - Complex.I * ρ) - Complex.I * ρ =
      1 / 6 := by ring
  rw [hz]
  simp [Complex.Gamma_zero]

theorem radialGammaQuotient_neg_at_witness_ne_zero (a ρ : ℝ)
    (ha : (1 / 2 : ℝ) ≤ a) (hρ : ρ ≠ 0) :
    radialGammaQuotient a (-ρ) (radialSignWitness a ρ) ≠ 0 := by
  unfold radialGammaQuotient
  apply div_ne_zero
  · apply mul_ne_zero <;> apply Complex.Gamma_ne_zero_of_re_pos <;>
      simp [radialSignWitness] <;> linarith
  · apply mul_ne_zero <;> apply gamma_ne_zero_of_im_ne_zero <;>
      simp [radialSignWitness] <;> exact hρ

/-- For nonzero radial parameter, changing its sign changes the multiplier. -/
theorem radialGammaQuotient_ne_neg (a ρ : ℝ)
    (ha : (1 / 2 : ℝ) ≤ a) (hρ : ρ ≠ 0) :
    radialGammaQuotient a ρ ≠ radialGammaQuotient a (-ρ) := by
  intro he
  have h := congrFun he (radialSignWitness a ρ)
  rw [radialGammaQuotient_at_witness] at h
  exact radialGammaQuotient_neg_at_witness_ne_zero a ρ ha hρ h.symm

/-- A fixed nonzero scalar, including a unit phase, cannot correct the radial sign. -/
theorem radialGammaQuotient_ne_const_mul_neg (a ρ : ℝ)
    (ha : (1 / 2 : ℝ) ≤ a) (hρ : ρ ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    radialGammaQuotient a ρ ≠ fun s => z * radialGammaQuotient a (-ρ) s := by
  intro he
  have h := congrFun he (radialSignWitness a ρ)
  rw [radialGammaQuotient_at_witness] at h
  exact (mul_ne_zero hz (radialGammaQuotient_neg_at_witness_ne_zero a ρ ha hρ)) h.symm


end HeckeSkeleton.ThetaLocal.Project
