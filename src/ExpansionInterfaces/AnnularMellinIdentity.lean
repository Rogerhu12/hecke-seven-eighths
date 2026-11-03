import ExpansionInterfaces.AnnularMellinProfile
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Exact initial-line Mellin formula for annular Dirichlet polynomials

The infinite Dirichlet coefficients, their smoothed finite polynomial,
and the Mellin integral use the same coefficient function.  Absolute
initial-line summability justifies the exchange; no smoothed-polynomial
upper bound or Mellin identity is assumed.
-/

noncomputable section
namespace ExpansionInterfaces.Mellin
open MeasureTheory Set
open scoped Classical BigOperators

def dirichletSeries {ι : Type*} (c : ι → ℂ) (N : ι → ℝ) (s : ℂ) : ℂ :=
  ∑' i, c i * (N i : ℂ) ^ (-s)

def smoothedTerm {ι : Type*} (W : AnnularProfile) (c : ι → ℂ)
    (N : ι → ℝ) (s : ℂ) (X : ℝ) (i : ι) : ℂ :=
  c i * (N i : ℂ) ^ (-s) * W.function (N i / X)

theorem initial_term_norm (c : ℂ) {N : ℝ} (hN : 0 < N) (s : ℂ) (σ t : ℝ) :
    ‖c * (N : ℂ) ^ (-(s + vertical σ t))‖ = ‖c‖ * N ^ (-(s.re + σ)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.neg_re, Complex.add_re, vertical_re]

theorem dirichletSeries_initial_continuous {ι : Type*}
    (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i) (s : ℂ) (σ : ℝ)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + σ)))) :
    Continuous (fun t : ℝ => dirichletSeries c N (s + vertical σ t)) := by
  unfold dirichletSeries
  refine continuous_tsum (fun i => ?_) hsum
    (fun i t => (initial_term_norm (c i) (hN i) s σ t).le)
  exact continuous_const.mul
    ((by unfold vertical; fun_prop : Continuous (fun t : ℝ => -(s + vertical σ t))).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (hN i).ne')))

theorem dirichletSeries_initial_norm_le {ι : Type*}
    (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i) (s : ℂ) (σ t : ℝ)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + σ)))) :
    ‖dirichletSeries c N (s + vertical σ t)‖ ≤
      ∑' i, ‖c i‖ * N i ^ (-(s.re + σ)) := by
  have hn : Summable (fun i => ‖c i * (N i : ℂ) ^ (-(s + vertical σ t))‖) := by
    simpa only [initial_term_norm _ (hN _) s σ t] using hsum
  simpa only [dirichletSeries, initial_term_norm _ (hN _) s σ t] using
    norm_tsum_le_tsum_norm hn

theorem mellin_weight_identity (q X : ℝ) (hq : 0 < q) (hX : 0 < X) (s z : ℂ) :
    (q : ℂ) ^ (-s) * ((q / X : ℝ) : ℂ) ^ (-z) =
      (X : ℂ) ^ z * (q : ℂ) ^ (-(s + z)) := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hq.le hX.le,
    Complex.cpow_neg (X : ℂ), div_inv_eq_mul, neg_add,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hq.ne')]
  ring

theorem annular_inverse_integrable (W : AnnularProfile) (σ x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      mellin W.function (vertical σ t) * (x : ℂ) ^ (-vertical σ t)) := by
  have hc : Continuous (fun t : ℝ =>
      mellin W.function (vertical σ t) * (x : ℂ) ^ (-vertical σ t)) :=
    (W.mellin_differentiable.continuous.comp (by unfold vertical; fun_prop)).mul
      ((by unfold vertical; fun_prop : Continuous (fun t : ℝ => -vertical σ t)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))
  apply ((W.vertical_norm_integrable σ).mul_const (x ^ (-σ))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re, vertical_re]

theorem annular_mellin_term (W : AnnularProfile) (σ q X : ℝ)
    (hq : 0 < q) (hX : 0 < X) (s a : ℂ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, mellin W.function (vertical σ t) *
        (a * (q : ℂ) ^ (-(s + vertical σ t))) * (X : ℂ) ^ vertical σ t) =
      a * (q : ℂ) ^ (-s) * W.function (q / X) := by
  have he (t : ℝ) : mellin W.function (vertical σ t) *
      (a * (q : ℂ) ^ (-(s + vertical σ t))) * (X : ℂ) ^ vertical σ t =
      (a * (q : ℂ) ^ (-s)) *
        (mellin W.function (vertical σ t) * ((q / X : ℝ) : ℂ) ^ (-vertical σ t)) := by
    have h := mellin_weight_identity q X hq hX s (vertical σ t)
    linear_combination -a * mellin W.function (vertical σ t) * h
  simp_rw [he]
  rw [integral_const_mul]
  have h := W.inversion σ (q / X) (div_pos hq hX)
  linear_combination (a * (q : ℂ) ^ (-s)) * h

theorem annular_mellin_term_integrable (W : AnnularProfile) (σ q X : ℝ)
    (hq : 0 < q) (hX : 0 < X) (s a : ℂ) :
    Integrable (fun t : ℝ => mellin W.function (vertical σ t) *
      (a * (q : ℂ) ^ (-(s + vertical σ t))) * (X : ℂ) ^ vertical σ t) := by
  have hi := (annular_inverse_integrable W σ (q / X) (div_pos hq hX)).const_mul
    (a * (q : ℂ) ^ (-s))
  apply hi.congr
  filter_upwards [] with t
  have h := mellin_weight_identity q X hq hX s (vertical σ t)
  linear_combination a * mellin W.function (vertical σ t) * h

/-- This stronger HasSum statement rules out any use of tsum's zero default. -/
theorem hasSum_annular_mellin {ι : Type*} [Countable ι]
    (W : AnnularProfile) (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (s : ℂ) (σ X : ℝ) (hX : 0 < X)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + σ)))) :
    HasSum (smoothedTerm W c N s X)
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, mellin W.function (vertical σ t) *
          dirichletSeries c N (s + vertical σ t) * (X : ℂ) ^ vertical σ t) := by
  let F : ι → ℝ → ℂ := fun i t => mellin W.function (vertical σ t) *
    (c i * (N i : ℂ) ^ (-(s + vertical σ t))) * (X : ℂ) ^ vertical σ t
  have hi (i : ι) : Integrable (F i) :=
    annular_mellin_term_integrable W σ (N i) X (hN i) hX s (c i)
  have hnorm (i : ι) (t : ℝ) : ‖F i t‖ =
      (‖mellin W.function (vertical σ t)‖ * X ^ σ) *
        (‖c i‖ * N i ^ (-(s.re + σ))) := by
    dsimp [F]
    rw [norm_mul, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hN i),
      Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [Complex.neg_re, Complex.add_re, vertical_re]
    ring
  have hnormint (i : ι) : (∫ t : ℝ, ‖F i t‖) =
      ((∫ t : ℝ, ‖mellin W.function (vertical σ t)‖) * X ^ σ) *
        (‖c i‖ * N i ^ (-(s.re + σ))) := by
    simp_rw [hnorm]
    rw [integral_mul_const, integral_mul_const]
  have hsumint : Summable (fun i => ∫ t : ℝ, ‖F i t‖) := by
    simp_rw [hnormint]
    exact hsum.mul_left _
  have heach (i : ι) : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F i t =
      smoothedTerm W c N s X i :=
    annular_mellin_term W σ (N i) X (hN i) hX s (c i)
  have hpoint (t : ℝ) : (∑' i, F i t) =
      mellin W.function (vertical σ t) * dirichletSeries c N (s + vertical σ t) *
        (X : ℂ) ^ vertical σ t := by
    dsimp [F, dirichletSeries]
    rw [tsum_mul_right, tsum_mul_left]
  have hs := (hasSum_integral_of_summable_integral_norm hi hsumint).mul_left
    (((1 / (2 * Real.pi) : ℝ) : ℂ))
  simpa only [heach, hpoint] using hs

theorem annular_mellin_series {ι : Type*} [Countable ι]
    (W : AnnularProfile) (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (s : ℂ) (σ X : ℝ) (hX : 0 < X)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + σ)))) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, mellin W.function (vertical σ t) *
        dirichletSeries c N (s + vertical σ t) * (X : ℂ) ^ vertical σ t) =
      ∑' i, smoothedTerm W c N s X i :=
  (hasSum_annular_mellin W c N hN s σ X hX hsum).tsum_eq.symm

/-- The initial line is calibrated to the actual L or reciprocal-L series.
Only initial-line equality and absolute coefficient summability are inputs. -/
theorem annular_mellin_finite_of_initial_line {ι : Type*} [Countable ι]
    (W : AnnularProfile) (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (L : ℂ → ℂ) (s : ℂ) (σ X : ℝ) (hX : 0 < X)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + σ))))
    (hline : ∀ t, L (s + vertical σ t) = dirichletSeries c N (s + vertical σ t))
    (S : Finset ι) (hS : ∀ i, N i ≤ W.upper * X → i ∈ S) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, mellin W.function (vertical σ t) *
        L (s + vertical σ t) * (X : ℂ) ^ vertical σ t) =
      ∑ i ∈ S, smoothedTerm W c N s X i := by
  simp_rw [hline]
  rw [annular_mellin_series W c N hN s σ X hX hsum]
  apply tsum_eq_sum
  intro i hi
  have hlarge : W.upper * X < N i := lt_of_not_ge (fun h => hi (hS i h))
  have hzero := W.zero_above ((lt_div_iff₀ hX).mpr hlarge)
  simp only [smoothedTerm, hzero, mul_zero]

end ExpansionInterfaces.Mellin
