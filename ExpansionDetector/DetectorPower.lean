import ExpansionDetector.ZeroDetectorBound

/-! Explicit scale and height exponents for the fixed-line detector.
The L-function input is a conventional polynomial strip bound; there is no
source-witness or expansion hypothesis. -/
noncomputable section
namespace ExpansionDetector.Analytic
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology

/-- With D <= U^(3/2), the crude finite-inverse bound and Y=U^20 give
U^(alpha-7), uniformly for 51/100 <= beta <= 1. -/
theorem gammaDetector_power_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ G : ℝ, 0 < G ∧
      ∀ {ι : Type*} (S : Finset ι) (c : ι → ℂ) (N : ι → ℝ)
        (L : ℂ → ℂ) (ρ : ℂ) (U D CL CZ α : ℝ),
      2 ≤ U → 0 ≤ D → D ≤ U ^ (3 / 2 : ℝ) →
      0 ≤ CL → 0 ≤ CZ → Differentiable ℂ L → L ρ = 0 →
      51 / 100 ≤ ρ.re → ρ.re ≤ 1 →
      (∀ i ∈ S, 1 ≤ N i ∧ N i ≤ 2 * D) →
      (∀ i ∈ S, ‖c i‖ ≤ 1) →
      (∑ i ∈ S, N i ^ (-2 : ℝ)) ≤ CZ →
      (∀ s : ℂ, 1 / 100 ≤ s.re → s.re ≤ 3 →
        ‖L s‖ ≤ CL * U ^ α * (2 + |s.im|) ^ A) →
      ‖gammaDetector L (dirichletPolynomial S c N) ρ (U ^ 20)‖ ≤
        (4 * G * CL * CZ) * U ^ (α - 7) * (2 + |ρ.im|) ^ A := by
  obtain ⟨G, hG, hdet⟩ := gammaDetector_bound_at_zero A hA
  refine ⟨G, hG, ?_⟩
  intro ι S c N L ρ U D CL CZ α hU hD hDU hCL hCZ hL hz hβ hβ1 hN hc hCZsum hLb
  have hUp : 0 < U := by linarith
  have hUpow : (U ^ (3 / 2 : ℝ)) ^ 2 = U ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hUp.le]
    norm_num
  have hD2 : (2 * D) ^ 2 ≤ 4 * U ^ (3 : ℝ) := by
    have h := sq_le_sq₀ hD (Real.rpow_nonneg hUp.le (3 / 2)) |>.mpr hDU
    rw [hUpow] at h
    nlinarith
  have hM : Differentiable ℂ (dirichletPolynomial S c N) :=
    dirichletPolynomial_entire S c N (fun i hi => zero_lt_one.trans_le (hN i hi).1)
  have hproduct (σ : ℝ) (hσ : σ ∈ Icc (-1 / 2 : ℝ) 2) (t : ℝ) :
      ‖L (ρ + vertical σ t) * dirichletPolynomial S c N (ρ + vertical σ t)‖ ≤
        (4 * CL * CZ * U ^ (α + 3)) * (2 + |ρ.im + t|) ^ A := by
    have hreal : (ρ + vertical σ t).re = ρ.re + σ := by simp
    have him : (ρ + vertical σ t).im = ρ.im + t := by simp
    have hMbound := dirichletPolynomial_norm_bound S c N (2 * D) CZ hN hc hCZsum
      (ρ + vertical σ t) (by rw [hreal]; linarith [hσ.1])
    have hM' : ‖dirichletPolynomial S c N (ρ + vertical σ t)‖ ≤
        4 * CZ * U ^ (3 : ℝ) := by
      apply hMbound.trans
      have h := mul_le_mul_of_nonneg_right hD2 hCZ
      nlinarith
    have hL' := hLb (ρ + vertical σ t)
      (by rw [hreal]; linarith [hσ.1]) (by rw [hreal]; linarith [hσ.2])
    rw [him] at hL'
    rw [norm_mul]
    calc
      _ ≤ (CL * U ^ α * (2 + |ρ.im + t|) ^ A) * (4 * CZ * U ^ (3 : ℝ)) :=
        mul_le_mul hL' hM' (norm_nonneg _) (by positivity)
      _ = _ := by rw [Real.rpow_add hUp]; ring
  have h := hdet L (dirichletPolynomial S c N) ρ (U ^ 20)
    (4 * CL * CZ * U ^ (α + 3)) hL hM hz (by positivity) (by positivity) hproduct
  apply h.trans_eq
  have h20 : (U ^ (20 : ℕ)) ^ (-1 / 2 : ℝ) = U ^ (-10 : ℝ) := by
    rw [← Real.rpow_natCast_mul hUp.le]
    norm_num
  rw [h20]
  have hp : U ^ (α + 3) * U ^ (-10 : ℝ) = U ^ (α - 7) := by
    rw [← Real.rpow_add hUp]
    congr 1
    ring
  calc
    _ = (4 * G * CL * CZ) * (U ^ (α + 3) * U ^ (-10 : ℝ)) *
        (2 + |ρ.im|) ^ A := by ring
    _ = _ := by rw [hp]

/-- Absorb the cumulative height allowance only after its degree A is fixed. -/
theorem detector_height_absorption {U A θ α C γ : ℝ}
    (hU : 1 ≤ U) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hγ : |γ| ≤ U ^ θ) :
    C * U ^ (α - 7) * (2 + |γ|) ^ A ≤
      (C * 3 ^ A) * U ^ (α - 7 + A * θ) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hpow : 1 ≤ U ^ θ := Real.one_le_rpow hU hθ
  have hh : (2 + |γ|) ^ A ≤ 3 ^ A * U ^ (A * θ) := by
    calc
      _ ≤ (3 * U ^ θ) ^ A := Real.rpow_le_rpow (by positivity) (by linarith) hA
      _ = 3 ^ A * U ^ (θ * A) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity),
          ← Real.rpow_mul hUp.le]
      _ = _ := by rw [mul_comm θ A]
  calc
    _ ≤ C * U ^ (α - 7) * (3 ^ A * U ^ (A * θ)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [Real.rpow_add hUp]; ring

/-- The fixed conductor cost alpha <= 1 leaves five powers of U after one
power has been allocated to the complete height budget. -/
theorem detector_height_power_five {U A θ α C γ : ℝ}
    (hU : 1 ≤ U) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hγ : |γ| ≤ U ^ θ) (hα : α ≤ 1) (hbudget : A * θ ≤ 1) :
    C * U ^ (α - 7) * (2 + |γ|) ^ A ≤
      (C * 3 ^ A) * U ^ (-5 : ℝ) := by
  apply (detector_height_absorption hU hA hθ hC hγ).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU (by linarith)) (by positivity)

/-- Hence the error is eventually smaller than any prescribed positive
constant, at a threshold common to the whole family. -/
theorem detector_uniform_small_numeric (C : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → C * U ^ (-5 : ℝ) < ε := by
  have ht : Tendsto (fun U : ℝ => C * U ^ (-5 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5)).const_mul C
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  exact ⟨max 2 U₀, le_max_left _ _, fun U hU => hU₀ U ((le_max_right _ _).trans hU)⟩

/-- The extra full power allowed here absorbs the crude finite Euler
deletion factor at primes dividing the row ideal. -/
theorem detector_height_power_four {U A θ α C γ : ℝ}
    (hU : 1 ≤ U) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hγ : |γ| ≤ U ^ θ) (hα : α ≤ 2) (hbudget : A * θ ≤ 1) :
    C * U ^ (α - 7) * (2 + |γ|) ^ A ≤
      (C * 3 ^ A) * U ^ (-4 : ℝ) := by
  apply (detector_height_absorption hU hA hθ hC hγ).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU (by linarith)) (by positivity)

theorem detector_uniform_small_power (C p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → C * U ^ (-p) < ε := by
  have ht : Tendsto (fun U : ℝ => C * U ^ (-p)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hp).const_mul C
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  exact ⟨max 2 U₀, le_max_left _ _, fun U hU => hU₀ U ((le_max_right _ _).trans hU)⟩

end ExpansionDetector.Analytic
