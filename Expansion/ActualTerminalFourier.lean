import Expansion.UniformTerminalFourier
import Expansion.TerminalCoefficientMass

/-! The exact ideal detector, uniform logarithmic Fourier profiles, and
finite coefficient mass combine into a normalized product spike.  The
remaining budget is a displayed scalar inequality, independent of the
row, frequency, and selected dyadic pair. -/

set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic
open MeasureTheory
open scoped NumberField Classical BigOperators ContDiff FourierTransform SchwartzMap
open ExpansionDetector.Fourier ExpansionDetector.IdealCutoff

variable {K : Type*} [Field K] [NumberField K]

/-- Constants precede every arithmetic homomorphism and every scale.
`hq` can be supplied by `actualIdeal_terminal_lower_of_zero`; neither
witness polynomial is an input hypothesis. -/
theorem actual_terminal_product_of_numeric_budget
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (order : ℕ) :
    ∃ C₀ Corder : ℝ, 0 ≤ C₀ ∧ 0 ≤ Corder ∧
    ∀ (w : Ideal (𝓞 K) →*₀ ℂ), (∀ I, ‖w I‖ ≤ 1) →
    (∀ x, ‖V x‖ ≤ 1) → ∀ D H Y R CZ q : ℝ,
    0 ≤ D → 1 ≤ H → 0 ≤ Y → 0 < R → 0 ≤ CZ →
    Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-2 : ℝ)) →
    (∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ →
    ∀ s : ℂ, 0 ≤ s.re →
    q ≤ ‖∑ I ∈ terminalIdealSet H,
      terminalTerm w V V D H (fun n => (n : ℂ) ^ (-s) * (Real.exp (-(n : ℝ) / Y) : ℂ)) I‖ →
    let n := dyadicCap (3 * H)
    ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) *
      ((((3 * H) ^ 2 * CZ) ^ 2) / R ^ order * Corder) ≤ q / 2 →
    ∃ j ≤ n, ∃ k ≤ n, ∃ t : ℝ, ‖t‖ ≤ R ∧
      q / 2 ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) * C₀ *
        ((2 : ℝ) ^ j) ^ (1 / 2 - s.re) * ((2 : ℝ) ^ k) ^ (1 / 2 - s.re) *
        ‖normalizedPolynomial (nonzeroTerminalSet H) (inverseRawCoefficient w V D)
            idealNorm annularProfile ((2 : ℝ) ^ j) s.re (2 * Real.pi * t - s.im) *
          normalizedPolynomial (nonzeroTerminalSet H) w
            idealNorm annularProfile ((2 : ℝ) ^ k) s.re (2 * Real.pi * t - s.im)‖ := by
  obtain ⟨C₀, hC₀, hmass⟩ := uniform_terminal_fourier_mass V hV hone hzero
  obtain ⟨Corder, hCorder, hmoment⟩ := uniform_terminal_fourier_moment V hV hone hzero order
  refine ⟨C₀, Corder, hC₀, hCorder, ?_⟩
  intro w hw hVnorm D H Y R CZ q hD hH hY hR hCZ hzeta hCZsum s hs hq
  dsimp only
  intro hbudget
  obtain ⟨j, hj, k, hk, t, ht, hsource⟩ :=
    actual_terminal_normalized_frequency w V V hV hV D H Y hH hzero s R hR order q hq
  refine ⟨j, hj, k, hk, t, ht, ?_⟩
  have hA := (actual_terminal_coefficient_mass w hw V hVnorm D H ((2 : ℝ) ^ j)
    hH s hs CZ hzeta hCZsum).1
  have hB := (actual_terminal_coefficient_mass w hw V hVnorm D H ((2 : ℝ) ^ k)
    hH s hs CZ hzeta hCZsum).2
  have hpair :
      (∑ I ∈ nonzeroTerminalSet H,
        ‖sourceCoefficient (inverseRawCoefficient w V D) idealNorm annularProfile ((2 : ℝ) ^ j) s I‖) *
      (∑ I ∈ nonzeroTerminalSet H,
        ‖sourceCoefficient w idealNorm annularProfile ((2 : ℝ) ^ k) s I‖)
        ≤ ((3 * H) ^ 2 * CZ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hA hB (by positivity) (by positivity)
  have hF := hmoment D H Y ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)
    hD (by linarith) hY (by positivity) (by positivity)
  have hF₀ := hmass D H Y ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)
    hD (by linarith) hY (by positivity) (by positivity)
  have htail := mul_le_mul (div_le_div_of_nonneg_right hpair (pow_nonneg hR.le order))
    hF (integral_nonneg fun u => by positivity) (by positivity)
  have hmain := mul_le_mul_of_nonneg_right hF₀
    (show 0 ≤ ((2 : ℝ) ^ j) ^ (1 / 2 - s.re) * ((2 : ℝ) ^ k) ^ (1 / 2 - s.re) *
      ‖normalizedPolynomial (nonzeroTerminalSet H) (inverseRawCoefficient w V D)
          idealNorm annularProfile ((2 : ℝ) ^ j) s.re (2 * Real.pi * t - s.im) *
        normalizedPolynomial (nonzeroTerminalSet H) w
          idealNorm annularProfile ((2 : ℝ) ^ k) s.re (2 * Real.pi * t - s.im)‖ by positivity)
  have hb := hsource.trans (mul_le_mul_of_nonneg_left (add_le_add htail hmain) (by positivity))
  exact product_lower_of_fourier_budget _ _ _ _ _ _ _ _ hb hbudget


/-- Constants precede every arithmetic homomorphism and every scale.
The same selected pair also retains its literal support-length bounds.
`hq` can be supplied by `actualIdeal_terminal_lower_of_zero`; neither
witness polynomial is an input hypothesis. -/
theorem actual_terminal_supported_product_of_numeric_budget
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (order : ℕ) :
    ∃ C₀ Corder : ℝ, 0 ≤ C₀ ∧ 0 ≤ Corder ∧
    ∀ (w : Ideal (𝓞 K) →*₀ ℂ), (∀ I, ‖w I‖ ≤ 1) →
    (∀ x, ‖V x‖ ≤ 1) → ∀ D H Y R CZ q : ℝ,
    0 < D → 1 ≤ H → 0 ≤ Y → 0 < R → 0 ≤ CZ →
    Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-2 : ℝ)) →
    (∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ →
    ∀ s : ℂ, 0 ≤ s.re → 0 < q →
    q ≤ ‖∑ I ∈ terminalIdealSet H,
      terminalTerm w V V D H (fun n => (n : ℂ) ^ (-s) * (Real.exp (-(n : ℝ) / Y) : ℂ)) I‖ →
    let n := dyadicCap (3 * H)
    ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) *
      ((((3 * H) ^ 2 * CZ) ^ 2) / R ^ order * Corder) ≤ q / 2 →
    ∃ j ≤ n, ∃ k ≤ n,
      ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
        (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * H) ∧
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      q / 2 ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) * C₀ *
        ((2 : ℝ) ^ j) ^ (1 / 2 - s.re) * ((2 : ℝ) ^ k) ^ (1 / 2 - s.re) *
        ‖normalizedPolynomial (nonzeroTerminalSet H) (inverseRawCoefficient w V D)
            idealNorm annularProfile ((2 : ℝ) ^ j) s.re (2 * Real.pi * t - s.im) *
          normalizedPolynomial (nonzeroTerminalSet H) w
            idealNorm annularProfile ((2 : ℝ) ^ k) s.re (2 * Real.pi * t - s.im)‖ := by
  obtain ⟨C₀, hC₀, hmass⟩ := uniform_terminal_fourier_mass V hV hone hzero
  obtain ⟨Corder, hCorder, hmoment⟩ := uniform_terminal_fourier_moment V hV hone hzero order
  refine ⟨C₀, Corder, hC₀, hCorder, ?_⟩
  intro w hw hVnorm D H Y R CZ q hD hH hY hR hCZ hzeta hCZsum s hs hqpos hq
  dsimp only
  intro hbudget
  obtain ⟨j, hj, k, hk, hsupport, t, ht, hsource⟩ :=
    actual_terminal_normalized_frequency_with_support w V hV hone hzero
      D H Y hD hH s R hR order q hqpos hq
  refine ⟨j, hj, k, hk, hsupport, t, ht, ?_⟩
  have hA := (actual_terminal_coefficient_mass w hw V hVnorm D H ((2 : ℝ) ^ j)
    hH s hs CZ hzeta hCZsum).1
  have hB := (actual_terminal_coefficient_mass w hw V hVnorm D H ((2 : ℝ) ^ k)
    hH s hs CZ hzeta hCZsum).2
  have hpair :
      (∑ I ∈ nonzeroTerminalSet H,
        ‖sourceCoefficient (inverseRawCoefficient w V D) idealNorm annularProfile ((2 : ℝ) ^ j) s I‖) *
      (∑ I ∈ nonzeroTerminalSet H,
        ‖sourceCoefficient w idealNorm annularProfile ((2 : ℝ) ^ k) s I‖)
        ≤ ((3 * H) ^ 2 * CZ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hA hB (by positivity) (by positivity)
  have hF := hmoment D H Y ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)
    hD.le (by linarith) hY (by positivity) (by positivity)
  have hF₀ := hmass D H Y ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)
    hD.le (by linarith) hY (by positivity) (by positivity)
  have htail := mul_le_mul (div_le_div_of_nonneg_right hpair (pow_nonneg hR.le order))
    hF (integral_nonneg fun u => by positivity) (by positivity)
  have hmain := mul_le_mul_of_nonneg_right hF₀
    (show 0 ≤ ((2 : ℝ) ^ j) ^ (1 / 2 - s.re) * ((2 : ℝ) ^ k) ^ (1 / 2 - s.re) *
      ‖normalizedPolynomial (nonzeroTerminalSet H) (inverseRawCoefficient w V D)
          idealNorm annularProfile ((2 : ℝ) ^ j) s.re (2 * Real.pi * t - s.im) *
        normalizedPolynomial (nonzeroTerminalSet H) w
          idealNorm annularProfile ((2 : ℝ) ^ k) s.re (2 * Real.pi * t - s.im)‖ by positivity)
  have hb := hsource.trans (mul_le_mul_of_nonneg_left (add_le_add htail hmain) (by positivity))
  exact product_lower_of_fourier_budget _ _ _ _ _ _ _ _ hb hbudget

end Expansion.Dyadic
