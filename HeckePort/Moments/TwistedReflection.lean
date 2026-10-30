import HeckePort.Moments.NaturalReflection
import HeckePort.Moments.ComparisonReflection

/-!
# Twisted polynomials and the norm-twisted source

Port of the formal part of openai/math `OAI/NumberTheory/DirichletL/Moments/TwistedReflection.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`, together with the definitions it uses from
`Hecke/Dyadic.lean` (`HeckeDyadic.shift/summand/polynomial`) and
`RowCompletion/PolynomialHeight.lean` (`CompletedHeight.normTwistedSource`), for an abstract
ideal coefficient `a : Ideal (𝓞 K) → ℂ` in place of `idealCoeff χ`.

* `polynomial_twisted_source` is verbatim (the proof uses the phase identity `norm_phase`).
* `actual_original_twisted_reflection` combines `original_inverse_reflection` (the cubic
  radial reflection with `paperRadialFourier`, `ℤ[ω]`-only) with the smooth Schwartz extension of
  the twisted source `CompletedHeight.uniformTwistedSchwartz`.  The formal step is the
  hypothesis-form `twisted_reflection_of_source`: a reflection identity valid for a class `P`
  of test functions transfers to the `ω`-twisted polynomial of `W` whenever the norm-twisted source of
  `W` lies in `P`.  The identity itself, and the Schwartz extension, are not ported.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- openai `HeckeDyadic.shift`. -/
def dyadicShift (σ ω : ℝ) : ℂ := (σ : ℂ) - (ω : ℂ) * Complex.I

/-- openai `FourierBridge.logPhase`. -/
def logPhase (t y : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I)

/-- openai `CompletedHeight.normTwistedSource`. -/
def normTwistedSource (W : ℝ → ℂ) (t x : ℝ) : ℂ := logPhase t (Real.log x) * W x

/-- openai `HeckeDyadic.summand`, for an abstract coefficient. -/
def dyadicSummand (a : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (D σ ω : ℝ) (I : NI K) : ℂ :=
  a I.val * W (inorm I / D) * ((inorm I / D : ℝ) : ℂ) ^ (-dyadicShift σ ω)

/-- openai `HeckeDyadic.polynomial`, for an abstract coefficient. -/
def dyadicPoly (a : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (D σ ω : ℝ) : ℂ :=
  (D : ℂ) ^ (-(1 / 2 : ℂ)) * ∑' I : NI K, dyadicSummand a W D σ ω I

/-- At `σ = ω = 0` the dyadic polynomial is the plain polynomial of `ReflectionDeletion`. -/
theorem dyadicPoly_zero (a : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0 ≤ X) :
    dyadicPoly a W X 0 0 = plainPoly a W X := by
  unfold dyadicPoly plainPoly dyadicSummand dyadicShift
  have h := inverse_half_power X hX
  rw [h]
  congr 1
  apply tsum_congr
  intro I
  simp

lemma logPhase_eq_cpow (t y : ℝ) (x : ℝ) (hx : 0 < x) (hy : y = Real.log x) :
    logPhase t y = (x : ℂ) ^ (-dyadicShift 0 (2 * Real.pi * t)) := by
  subst hy
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), logPhase,
    ← Complex.ofReal_log hx.le]
  congr 1
  simp only [dyadicShift, Complex.ofReal_zero, zero_sub, neg_neg, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

/-- openai `polynomial_twisted_source`. -/
theorem polynomial_twisted_source (a : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) :
    dyadicPoly a W X 0 (2 * Real.pi * t) =
      dyadicPoly a (normTwistedSource W t) X 0 0 := by
  unfold dyadicPoly
  congr 1
  apply tsum_congr
  intro I
  unfold dyadicSummand normTwistedSource
  have hx : 0 < inorm I / X := div_pos (inorm_pos I) hX
  rw [logPhase_eq_cpow t _ _ hx rfl]
  simp only [dyadicShift, Complex.ofReal_zero, zero_sub, neg_neg, zero_mul,
    sub_zero, neg_zero, Complex.cpow_zero, mul_one]
  ring

/-- openai `actual_original_twisted_reflection`, formal step. -/
theorem twisted_reflection_of_source (a : Ideal (𝓞 K) → ℂ) (P : (ℝ → ℂ) → Prop)
    (Rhs : (ℝ → ℂ) → ℂ) (X : ℝ)
    (hrefl : ∀ W' : ℝ → ℂ, P W' → dyadicPoly a W' X 0 0 = Rhs W')
    (hX : 0 < X) (W : ℝ → ℂ) (t : ℝ) (hP : P (normTwistedSource W t)) :
    dyadicPoly a W X 0 (2 * Real.pi * t) = Rhs (normTwistedSource W t) := by
  rw [polynomial_twisted_source a W X t hX]
  exact hrefl _ hP

end HeckePort.Moments

end
