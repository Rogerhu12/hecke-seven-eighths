import Expansion.ActualTerminalFourier
import Expansion.TerminalTailBudget
import ExpansionDetector.AnnularNormalization

/-!
# Uniform terminal Fourier extraction with the tail absorbed

The Fourier order is selected after its positive height exponent and before
the Fourier constants. One scale threshold then absorbs the complete tail,
including the two dyadic counts and both actual ideal coefficient masses.
The terminal source and the two normalized polynomials use the same complete
multiplicative ideal coefficient; no deleted Euler factor is restored.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic

open scoped NumberField Classical BigOperators ContDiff
open ExpansionDetector.Fourier ExpansionDetector.IdealCutoff

variable {K : Type*} [Field K] [NumberField K]

/-- A terminal source of norm at least one quarter produces a normalized
product at one common bounded frequency. There is no Fourier-tail premise.
The constants are fixed before the arithmetic coefficient, cutoff scale,
spectral parameter, or selected dyadic pair. -/
theorem actual_terminal_product_eventually
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (τ : ℝ) (hτ : 0 < τ) (CZ : ℝ) (hCZ : 0 ≤ CZ)
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ)))
    (hCZsum : (∑' I : NonzeroIntegralIdeal (K := K),
      nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ) :
    ∃ C U₀ : ℝ, 0 < C ∧ 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ (w : Ideal (𝓞 K) →*₀ ℂ), (∀ I, ‖w I‖ ≤ 1) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ D : ℝ, 0 < D →
      ∀ s : ℂ, 0 ≤ s.re →
      (1 / 4 : ℝ) ≤ ‖∑ I ∈ terminalIdealSet (U ^ (21 : ℕ)),
        terminalTerm w V V D (U ^ (21 : ℕ))
          (fun n => (n : ℂ) ^ (-s) *
            (Real.exp (-(n : ℝ) / U ^ (20 : ℕ)) : ℂ)) I‖ →
      let n := dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n,
        ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
      ∃ t : ℝ,
        ‖t‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        (1 / 8 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) * C *
          ((2 : ℝ) ^ j) ^ (1 / 2 - s.re) *
          ((2 : ℝ) ^ k) ^ (1 / 2 - s.re) *
          ‖normalizedPolynomial (nonzeroTerminalSet (U ^ (21 : ℕ)))
              (inverseRawCoefficient w V D) idealNorm annularProfile
              ((2 : ℝ) ^ j) s.re (2 * Real.pi * t - s.im) *
            normalizedPolynomial (nonzeroTerminalSet (U ^ (21 : ℕ))) w
              idealNorm annularProfile ((2 : ℝ) ^ k) s.re
              (2 * Real.pi * t - s.im)‖ := by
  obtain ⟨order, _, hbudget⟩ := exists_terminal_fourier_tail_budget τ hτ
  obtain ⟨C, Corder, hC, hCorder, hproduct⟩ :=
    actual_terminal_supported_product_of_numeric_budget (K := K) V hV hone hzero order
  obtain ⟨U₀, hU₀, htail⟩ := hbudget CZ Corder hCorder
  refine ⟨C + 1, U₀, by linarith, hU₀, ?_⟩
  intro U hU w hw hVnorm D hD s hs hsource
  have hUtwo : 2 ≤ U := hU₀.trans hU
  have hUone : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have hH : 1 ≤ U ^ (21 : ℕ) := one_le_pow₀ hUone
  have hR : 0 < U ^ τ / (8 * Real.pi + 8) := by positivity
  have hn := htail U hU
  have hresult :=
    hproduct w hw hVnorm D (U ^ (21 : ℕ)) (U ^ (20 : ℕ))
      (U ^ τ / (8 * Real.pi + 8)) CZ (1 / 4) hD hH (by positivity) hR hCZ
      hzeta hCZsum s hs (by norm_num) hsource (by simpa only [pow_two] using hn)
  obtain ⟨j, hj, k, hk, hsupport, t, ht, hbound⟩ := hresult
  refine ⟨j, hj, k, hk, hsupport, t, ht, ?_⟩
  norm_num only [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at hbound
  apply hbound.trans
  gcongr <;> linarith

/-- Full zero-to-product extraction for the actual ideal Dirichlet source.
The analytic inputs are the ordinary entire continuation, its initial
Dirichlet series, absolute convergence there, and one polynomial strip
bound. The source lower bound and Fourier tail are both proved internally.

The separate exponents `θ` and `τ` control the original zero height and the
Fourier radius, respectively. In a buffered contour application, the latter
can be chosen below the available physical height allowance. -/
theorem actual_zero_product_eventually
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVcomp : ∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1)
    (A θ α CL CZ τ : ℝ) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hα : α ≤ 2)
    (hCL : 0 ≤ CL) (hCZ : 0 ≤ CZ) (hheight : A * θ ≤ 1) (hτ : 0 < τ)
    (hzeta₃ : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-3 / 2 : ℝ)))
    (hzeta₂ : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ)))
    (hCZsum : (∑' I : NonzeroIntegralIdeal (K := K),
      nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ) :
    ∃ C U₀ : ℝ, 0 < C ∧ 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ (w : Ideal (𝓞 K) →*₀ ℂ) (D : ℝ) (L : ℂ → ℂ) (ρ : ℂ),
      (∀ I, ‖w I‖ ≤ 1) → 2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) →
      Differentiable ℂ L →
      (∀ s : ℂ, 1 < s.re →
        L s = ∑' I : Ideal (𝓞 K), idealDirichletWeight w s I) →
      (∀ s : ℂ, 1 < s.re →
        Summable (fun I : Ideal (𝓞 K) => ‖idealDirichletWeight w s I‖)) →
      (∀ s : ℂ, 1 / 100 ≤ s.re → s.re ≤ 3 →
        ‖L s‖ ≤ CL * U ^ α * (2 + |s.im|) ^ A) →
      L ρ = 0 → 51 / 100 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ U ^ θ →
      let n := dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n,
        ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
      ∃ t : ℝ,
        ‖t‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        (1 / 8 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) * C *
          ((2 : ℝ) ^ j) ^ (1 / 2 - ρ.re) *
          ((2 : ℝ) ^ k) ^ (1 / 2 - ρ.re) *
          ‖normalizedPolynomial (nonzeroTerminalSet (U ^ (21 : ℕ)))
              (inverseRawCoefficient w V D) idealNorm annularProfile
              ((2 : ℝ) ^ j) ρ.re (2 * Real.pi * t - ρ.im) *
            normalizedPolynomial (nonzeroTerminalSet (U ^ (21 : ℕ))) w
              idealNorm annularProfile ((2 : ℝ) ^ k) ρ.re
              (2 * Real.pi * t - ρ.im)‖ := by
  obtain ⟨C, U₁, hC, hU₁, hproduct⟩ :=
    actual_terminal_product_eventually (K := K) V hV hone hzero τ hτ CZ hCZ
      hzeta₂ hCZsum
  obtain ⟨U₂, hU₂, hsource⟩ := actualIdeal_terminal_lower_of_zero
    A θ α CL CZ hA hθ hα hCL hCZ hheight hzeta₃ hzeta₂ hCZsum
  refine ⟨C, max U₁ U₂, hC, hU₁.trans (le_max_left _ _), ?_⟩
  intro U hU w D L ρ hw hD hDU hL hseries habs hstrip hzeroρ hβ hβ1 hγ
  have hUleft : U₁ ≤ U := (le_max_left _ _).trans hU
  have hUright : U₂ ≤ U := (le_max_right _ _).trans hU
  have hterminal := hsource U hUright w V V D L ρ hw hVnorm hVcomp hVcomp
    (fun x _ hx => hone x hx) (fun x _ hx => hone x hx) hzero hzero
    hD hDU hL hseries habs hstrip hzeroρ hβ hβ1 hγ
  exact hproduct U hUleft w hw hVnorm D (by linarith) ρ (by linarith) hterminal

end Expansion.Dyadic
