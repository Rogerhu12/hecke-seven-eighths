import CubicSieve.ProfileSpectrum

/-! Exact separation of both column norm parameters by the actual Mellin
spectrum. The column multipliers are contractions on the whole prefix x≤1. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Profile

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open scoped Classical NumberField ComplexConjugate

def columnPower (c τ x : ℝ) : ℂ := (x : ℂ) ^ lineExponent c τ
def rowPower (c τ r : ℝ) : ℂ := (r : ℂ) ^ (-lineExponent c τ)

theorem columnPower_norm (c τ x : ℝ) (hx : 0 < x) : ‖columnPower c τ x‖ = x ^ c := by
  rw [columnPower, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [lineExponent]

theorem columnPower_norm_le_one (c τ x : ℝ) (hc : 0 ≤ c) (hx : 0 < x) (hx₁ : x ≤ 1) :
    ‖columnPower c τ x‖ ≤ 1 := by
  rw [columnPower_norm c τ x hx]
  exact Real.rpow_le_one hx.le hx₁ hc

theorem rowPower_norm (c τ r : ℝ) (hr : 0 < r) : ‖rowPower c τ r‖ = r ^ (-c) := by
  rw [rowPower, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp [lineExponent]

theorem columnPower_star (c τ x : ℝ) (hx : 0 < x) :
    star (columnPower c (-τ) x) = columnPower c τ x := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  have he : conj (lineExponent c τ) = lineExponent c (-τ) := by
    apply Complex.ext <;> simp [lineExponent]
  simpa only [columnPower, Complex.star_def, he, Complex.conj_ofReal] using
    (Complex.conj_cpow (x : ℂ) (lineExponent c τ) harg).symm

theorem cpow_separation (c τ r x y : ℝ) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y) :
    ((r / (x * y) : ℝ) : ℂ) ^ (-lineExponent c τ) =
      rowPower c τ r * columnPower c τ x * columnPower c τ y := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hr.le (mul_pos hx hy).le,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le hy.le]
  simp only [rowPower, columnPower, Complex.cpow_neg, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)

theorem separated_spectrum_integrable (c r x y : ℝ)
    (hc : 0 < c) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y) :
    Integrable (fun τ : ℝ => spectralDensity A c τ * rowPower c τ r *
      columnPower c τ x * columnPower c τ y) := by
  have hi := (canonical_mellin_inversion A c (r / (x * y)) hc (div_pos hr (mul_pos hx hy))).1
  have he : (fun τ : ℝ => spectralDensity A c τ * rowPower c τ r *
      columnPower c τ x * columnPower c τ y) =
      fun τ : ℝ => ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (canonicalMellin A ((c : ℂ) + (τ : ℂ) * Complex.I) *
          ((r / (x * y) : ℝ) : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) := by
    funext τ
    rw [show -(c : ℂ) - (τ : ℂ) * Complex.I = -lineExponent c τ by
      dsimp [lineExponent]; ring,
      cpow_separation c τ r x y hr hx hy]
    simp only [spectralDensity, lineExponent]
    ring
  rw [he]
  exact hi.const_mul _

theorem dualProfile_separated (c r x y : ℝ)
    (hc : 0 < c) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y) :
    dualProfile A ⟨r / (x * y), div_pos hr (mul_pos hx hy)⟩ =
      ∫ τ : ℝ, spectralDensity A c τ * rowPower c τ r *
        columnPower c τ x * columnPower c τ y := by
  rw [(canonical_mellin_inversion A c (r / (x * y)) hc (div_pos hr (mul_pos hx hy))).2,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun τ => by
    dsimp only
    rw [show -(c : ℂ) - (τ : ℂ) * Complex.I = -lineExponent c τ by
      dsimp [lineExponent]; ring,
      cpow_separation c τ r x y hr hx hy]
    simp only [spectralDensity, lineExponent]
    ring

end CubicSieve.Profile

namespace CubicSieve.Profile.Gaussian

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open scoped Classical NumberField ComplexConjugate BigOperators

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)

theorem separated_spectrum_integrable (c r x y : ℝ)
    (hc : 0 < c) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y) :
    Integrable (fun τ : ℝ => spectralDensity A c τ * rowPower c τ r *
      columnPower c τ x * columnPower c τ y) := by
  have hi := (canonical_mellin_inversion A c (r / (x * y)) hc (div_pos hr (mul_pos hx hy))).1
  have he : (fun τ : ℝ => spectralDensity A c τ * rowPower c τ r *
      columnPower c τ x * columnPower c τ y) =
      fun τ : ℝ => ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (canonicalMellin A ((c : ℂ) + (τ : ℂ) * Complex.I) *
          ((r / (x * y) : ℝ) : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) := by
    funext τ
    rw [show -(c : ℂ) - (τ : ℂ) * Complex.I = -lineExponent c τ by
      dsimp [lineExponent]; ring,
      cpow_separation c τ r x y hr hx hy]
    simp only [spectralDensity, lineExponent]
    ring
  rw [he]
  exact hi.const_mul _

theorem dualProfile_separated (c r x y : ℝ)
    (hc : 0 < c) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y) :
    dualProfile A ⟨r / (x * y), div_pos hr (mul_pos hx hy)⟩ =
      ∫ τ : ℝ, spectralDensity A c τ * rowPower c τ r *
        columnPower c τ x * columnPower c τ y := by
  rw [(canonical_mellin_inversion A c (r / (x * y)) hc (div_pos hr (mul_pos hx hy))).2,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun τ => by
    dsimp only
    rw [show -(c : ℂ) - (τ : ℂ) * Complex.I = -lineExponent c τ by
      dsimp [lineExponent]; ring,
      cpow_separation c τ r x y hr hx hy]
    simp only [spectralDensity, lineExponent]
    ring


end CubicSieve.Profile.Gaussian
