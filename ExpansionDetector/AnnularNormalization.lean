import ExpansionDetector.FourierNormalized

/-! Exact normalization of the finite Mellin polynomial and the fixed
Fourier-radius shrink needed by the physical height buffer. -/
noncomputable section
namespace ExpansionDetector.Fourier
open Complex
open scoped Classical BigOperators

@[simp] lemma centralShift_re (σ ν : ℝ) : (centralShift σ ν).re = σ := by
  simp [centralShift]

@[simp] lemma centralShift_im (σ ν : ℝ) : (centralShift σ ν).im = -ν := by
  simp [centralShift]

theorem sqrt_inverse_eq_cpow (D : ℝ) (hD : 0 < D) :
    (Real.sqrt D : ℂ)⁻¹ = (D : ℂ) ^ (-(1 / 2 : ℂ)) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hD.le]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  exact (Complex.cpow_neg (D : ℂ) (1 / 2)).symm

/-- The polynomial from the Fourier witness has exactly the Mellin
normalization X^(Re(s)-1/2), with no coefficient or phase alteration. -/
theorem normalizedPolynomial_norm_eq_dirichlet {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i)
    (W : ℝ → ℂ) (D σ ν : ℝ) (hD : 0 < D) :
    ‖normalizedPolynomial S c N W D σ ν‖ =
      D ^ (σ - 1 / 2) *
        ‖∑ i ∈ S, c i * (N i : ℂ) ^ (-centralShift σ ν) * W (N i / D)‖ := by
  have h := phase_eq_normalizedPolynomial S c N hN W D hD (centralShift σ ν) 0
  have h0 : phasePolynomial S (sourceCoefficient c N W D (centralShift σ ν))
      (fun i => Real.log (N i / D)) 0 =
      ∑ i ∈ S, c i * (N i : ℂ) ^ (-centralShift σ ν) * W (N i / D) := by
    simp only [phasePolynomial, sourceCoefficient, logPhase, mul_zero, zero_mul,
      Complex.ofReal_zero, Complex.exp_zero, mul_one]
  rw [h0] at h
  simp only [centralShift_re, centralShift_im, mul_zero, zero_sub, neg_neg] at h
  have hn := congrArg norm h
  rw [norm_mul, normalization_norm D hD, centralShift_re] at hn
  have hprod : D ^ (σ - 1 / 2) * D ^ (1 / 2 - σ) = 1 := by
    rw [← Real.rpow_add hD]
    convert Real.rpow_zero D using 1 <;> ring
  calc
    _ = (D ^ (σ - 1 / 2) * D ^ (1 / 2 - σ)) *
        ‖normalizedPolynomial S c N W D σ ν‖ := by rw [hprod, one_mul]
    _ = D ^ (σ - 1 / 2) *
        (D ^ (1 / 2 - σ) * ‖normalizedPolynomial S c N W D σ ν‖) := by ring
    _ = _ := by rw [← hn]

/-- Using the Fourier radius T/(8π+8), rather than T, leaves enough room
for a height-T rectangle and the genuine 3/2 analytic padding between
the selected height 3iT and the upper height 3(i+1)T. -/
theorem common_frequency_contour_padding (i : ℕ) (T R t γ : ℝ)
    (hT : 1 ≤ T) (hR : R ≤ T / (8 * Real.pi + 8))
    (ht : ‖t‖ ≤ R) (hγ : |γ| ≤ 3 * (i : ℝ) * T) :
    |2 * Real.pi * t - γ| + T + 3 / 2 ≤ 3 * ((i + 1 : ℕ) : ℝ) * T := by
  have hRnonneg : 0 ≤ R := (norm_nonneg t).trans ht
  have hden : 0 < 8 * Real.pi + 8 := by positivity
  have hmul := (le_div_iff₀ hden).mp hR
  have hsmall : 2 * Real.pi * R ≤ T / 4 := by nlinarith
  have hh := common_frequency_bound t γ R (3 * (i : ℝ) * T) ht hγ
  push_cast
  nlinarith

end ExpansionDetector.Fourier
