import ExpansionDetector.FourierWitness

/-! The common Fourier frequency gives the same centrally normalized
coefficient polynomial in both witnesses. All phases and profiles are
explicit; the coefficient data are unchanged by the normalization. -/
noncomputable section
namespace ExpansionDetector.Fourier
open Complex
open scoped Classical BigOperators

def centralShift (σ ν : ℝ) : ℂ := (σ : ℂ) - (ν : ℂ) * I

def normalizedPolynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (N : ι → ℝ) (W : ℝ → ℂ) (D σ ν : ℝ) : ℂ :=
  (D : ℂ) ^ (-(1 / 2 : ℂ)) *
    ∑ i ∈ S, c i * W (N i / D) * ((N i / D : ℝ) : ℂ) ^ (-centralShift σ ν)

def sourceCoefficient {ι : Type*} (c : ι → ℂ) (N : ι → ℝ)
    (W : ℝ → ℂ) (D : ℝ) (s : ℂ) (i : ι) : ℂ :=
  c i * (N i : ℂ) ^ (-s) * W (N i / D)

lemma norm_phase (x D : ℝ) (hx : 0 < x) (hD : 0 < D) (s : ℂ) (t : ℝ) :
    (x : ℂ) ^ (-s) * logPhase t (Real.log (x / D)) =
      (D : ℂ) ^ (-s) * ((x / D : ℝ) : ℂ) ^ (-centralShift s.re (2 * Real.pi * t - s.im)) := by
  have hxD : 0 < x / D := div_pos hx hD
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxD.ne')]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hD.le,
    ← Complex.ofReal_log hxD.le]
  unfold logPhase centralShift
  rw [← Complex.exp_add, ← Complex.exp_add, Real.log_div hx.ne' hD.ne']
  congr 1
  have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  rw [hs]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  push_cast
  ring

lemma normalization (D : ℝ) (hD : 0 < D) (s : ℂ) :
    (D : ℂ) ^ ((1 / 2 : ℂ) - s) * (D : ℂ) ^ (-(1 / 2 : ℂ)) =
      (D : ℂ) ^ (-s) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 1
  ring

theorem phase_eq_normalizedPolynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i) (W : ℝ → ℂ)
    (D : ℝ) (hD : 0 < D) (s : ℂ) (t : ℝ) :
    phasePolynomial S (sourceCoefficient c N W D s) (fun i => Real.log (N i / D)) t =
      (D : ℂ) ^ ((1 / 2 : ℂ) - s) *
        normalizedPolynomial S c N W D s.re (2 * Real.pi * t - s.im) := by
  unfold normalizedPolynomial
  rw [← mul_assoc, normalization D hD s, Finset.mul_sum]
  unfold phasePolynomial sourceCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  have hp := norm_phase (N i) D (hN i hi) hD s t
  calc
    _ = c i * W (N i / D) *
        ((N i : ℂ) ^ (-s) * logPhase t (Real.log (N i / D))) := by ring
    _ = _ := by rw [hp]; ring

lemma normalization_norm (D : ℝ) (hD : 0 < D) (s : ℂ) :
    ‖(D : ℂ) ^ ((1 / 2 : ℂ) - s)‖ = D ^ (1 / 2 - s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
  congr 1
  simp

/-- Both normalized factors have one and the same frequency. -/
theorem pair_phase_norm {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (N : ι → ℝ) (M : κ → ℝ)
    (hN : ∀ i ∈ S, 0 < N i) (hM : ∀ j ∈ T, 0 < M j)
    (W V : ℝ → ℂ) (D E : ℝ) (hD : 0 < D) (hE : 0 < E) (s : ℂ) (t : ℝ) :
    ‖phasePolynomial S (sourceCoefficient c N W D s) (fun i => Real.log (N i / D)) t *
      phasePolynomial T (sourceCoefficient d M V E s) (fun j => Real.log (M j / E)) t‖ =
      D ^ (1 / 2 - s.re) * E ^ (1 / 2 - s.re) *
        ‖normalizedPolynomial S c N W D s.re (2 * Real.pi * t - s.im) *
          normalizedPolynomial T d M V E s.re (2 * Real.pi * t - s.im)‖ := by
  rw [phase_eq_normalizedPolynomial S c N hN W D hD,
    phase_eq_normalizedPolynomial T d M hM V E hE]
  simp only [norm_mul, normalization_norm D hD s, normalization_norm E hE s]
  ring

theorem common_frequency_bound (t γ R T : ℝ) (ht : ‖t‖ ≤ R) (hγ : |γ| ≤ T) :
    |2 * Real.pi * t - γ| ≤ 2 * Real.pi * R + T := by
  calc
    _ ≤ |2 * Real.pi * t| + |γ| := abs_sub _ _
    _ = 2 * Real.pi * ‖t‖ + |γ| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), Real.norm_eq_abs]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left ht (by positivity)) hγ

end ExpansionDetector.Fourier
