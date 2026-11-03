import ThetaGlobal.ScalarMellinConvolution
import ThetaGlobal.VerticalContour
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# All absolute power moments of a scalar Mellin deconvolver

For an entire spectral function G, quadratic decay on every fixed vertical
strip implies that its inverse Mellin transform has every absolute power
moment. This is the exact local condition supplied by the annular Mellin
transform times a Gaussian times the entire reciprocal gamma product.
No theta identity or final reflection statement is a hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.DeconvolverMoments

open MeasureTheory Set Filter
open scoped Topology

def verticalSpectrum (G : ℂ → ℂ) (c t : ℝ) : ℂ :=
  G ((c : ℂ) + (t : ℂ) * Complex.I)

def exponentialPhase (c t u : ℝ) : ℂ :=
  Complex.exp (-((c : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))

def logInverse (G : ℂ → ℂ) (c u : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t, verticalSpectrum G c t * exponentialPhase c t u

/-- Local scalar spectral decay, proved in the application from the Gaussian
and the fixed-strip growth of reciprocal gamma. -/
def QuadraticStripDecay (G : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
    ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖verticalSpectrum G c t‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)

theorem norm_exponentialPhase (c t u : ℝ) :
    ‖exponentialPhase c t u‖ = Real.exp (-c * u) := by
  rw [exponentialPhase, Complex.norm_exp]
  simp

theorem integrable_verticalSpectrum {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G) (c : ℝ) :
    Integrable (verticalSpectrum G c) := by
  obtain ⟨C, _, hC⟩ := hstrip c c le_rfl
  have hc : Continuous (verticalSpectrum G c) := by
    exact hG.continuous.comp (by fun_prop)
  apply ((VerticalContour.integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul C).mono'
    hc.aestronglyMeasurable
  exact Eventually.of_forall (fun t => hC c ⟨le_rfl, le_rfl⟩ t)

private theorem strip_exponent_le {a b c : ℝ}
    (ha : a ≤ c) (hb : c ≤ b) (u : ℝ) :
    -c * u ≤ |a * u| + |b * u| := by
  rcases le_total 0 u with hu | hu
  · calc
      -c * u = -(c * u) := by ring
      _ ≤ -(a * u) := neg_le_neg (mul_le_mul_of_nonneg_right ha hu)
      _ ≤ |a * u| := neg_le_abs _
      _ ≤ _ := le_add_of_nonneg_right (abs_nonneg _)
  · calc
      -c * u = -(c * u) := by ring
      _ ≤ -(b * u) := neg_le_neg (mul_le_mul_of_nonpos_right hb hu)
      _ ≤ |b * u| := neg_le_abs _
      _ ≤ _ := le_add_of_nonneg_left (abs_nonneg _)

/-- The two inverse lines agree pointwise in the logarithmic argument. -/
theorem logInverse_line_independent {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G)
    (a b u : ℝ) : logInverse G a u = logInverse G b u := by
  have shift (a b : ℝ) (hab : a ≤ b) :
      logInverse G a u = logInverse G b u := by
    obtain ⟨C, hC, hbound⟩ := hstrip a b hab
    unfold logInverse
    congr 1
    apply VerticalContour.verticalIntegral_eq_of_poly_strip
      (f := fun z => G z * Complex.exp (-z * (u : ℂ)))
      (C := C * Real.exp (|a * u| + |b * u|)) (e := 2) hab (by norm_num)
    · intro z _ _
      exact (hG z).mul (by fun_prop)
    · intro c hc t
      change ‖verticalSpectrum G c t * exponentialPhase c t u‖ ≤ _
      rw [norm_mul, norm_exponentialPhase]
      calc
        _ ≤ (C * (1 + |t|) ^ (-2 : ℝ)) *
            Real.exp (|a * u| + |b * u|) :=
          mul_le_mul (hbound c hc t)
            (Real.exp_le_exp.mpr (strip_exponent_le hc.1 hc.2 u))
            (Real.exp_pos _).le
            (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
        _ = _ := by ring
  rcases le_total a b with hab | hba
  · exact shift a b hab
  · exact (shift b a hba).symm

theorem logInverse_bound (G : ℂ → ℂ) (c u : ℝ) :
    ‖logInverse G c u‖ ≤
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * ∫ t, ‖verticalSpectrum G c t‖) *
        Real.exp (-c * u) := by
  unfold logInverse
  rw [norm_mul]
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t, ‖verticalSpectrum G c t * exponentialPhase c t u‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = _ := by
      simp_rw [norm_mul, norm_exponentialPhase]
      rw [integral_mul_const]
      ring

/-- Continuity is pointwise, so scalar inversion identities never have to
remain merely almost everywhere statements. -/
theorem continuous_logInverse {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G) :
    Continuous (logInverse G 0) := by
  have hspec := integrable_verticalSpectrum hG hstrip 0
  have hspec_cont : Continuous (verticalSpectrum G 0) :=
    hG.continuous.comp (by fun_prop)
  have hi : Continuous (fun u : ℝ =>
      ∫ t, verticalSpectrum G 0 t * exponentialPhase 0 t u) := by
    apply continuous_of_dominated (bound := fun t => ‖verticalSpectrum G 0 t‖)
    · intro u
      exact (hspec_cont.mul (by unfold exponentialPhase; fun_prop)).aestronglyMeasurable
    · intro u
      filter_upwards [] with t
      rw [norm_mul, norm_exponentialPhase]
      simp
    · exact hspec.norm
    · filter_upwards [] with t
      unfold exponentialPhase
      fun_prop
  exact continuous_const.mul hi

theorem zeroLine_eq_scalarInverse (G : ℂ → ℂ) (u : ℝ) :
    logInverse G 0 u =
      ScalarMellinConvolution.inverseLine (verticalSpectrum G 0) u := by
  unfold logInverse ScalarMellinConvolution.inverseLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  unfold exponentialPhase ScalarMellinConvolution.phase
  congr 1
  push_cast
  ring

/-- A pair of opposite log-exponential envelopes gives the required L1
moment. This is the rigorous split into t <= 1 and t >= 1. -/
theorem integrable_log_weight_of_two_bounds (J : ℝ → ℂ)
    (hJ : Continuous J) (q Cminus Cplus : ℝ)
    (hminus : ∀ u, ‖J u‖ ≤ Cminus * Real.exp (-(q - 1) * u))
    (hplus : ∀ u, ‖J u‖ ≤ Cplus * Real.exp (-(q + 1) * u)) :
    Integrable (fun u => ‖J u‖ * Real.exp (q * u)) := by
  let f : ℝ → ℝ := fun u => ‖J u‖ * Real.exp (q * u)
  have hf : Continuous f := hJ.norm.mul (by fun_prop)
  have hleft : IntegrableOn f (Iic 0) := by
    apply ((integrableOn_exp_Iic 0).const_mul Cminus).mono' hf.aestronglyMeasurable
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    calc
      f u ≤ (Cminus * Real.exp (-(q - 1) * u)) * Real.exp (q * u) :=
        mul_le_mul_of_nonneg_right (hminus u) (Real.exp_pos _).le
      _ = Cminus * Real.exp u := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring
  have hright : IntegrableOn f (Ioi 0) := by
    apply ((integrableOn_exp_neg_Ioi 0).const_mul Cplus).mono' hf.aestronglyMeasurable
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    calc
      f u ≤ (Cplus * Real.exp (-(q + 1) * u)) * Real.exp (q * u) :=
        mul_le_mul_of_nonneg_right (hplus u) (Real.exp_pos _).le
      _ = Cplus * Real.exp (-u) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring
  simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union hright

/-- Every absolute power moment of the Mellin deconvolver is finite in
logarithmic coordinates. The constants are allowed to depend on the line. -/
theorem integrable_log_power_moment {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G) (q : ℝ) :
    Integrable (fun u => ‖logInverse G 0 u‖ * Real.exp (q * u)) := by
  apply integrable_log_weight_of_two_bounds (logInverse G 0)
    (continuous_logInverse hG hstrip) q
    (‖(2 * (Real.pi : ℂ))⁻¹‖ * ∫ t, ‖verticalSpectrum G (q - 1) t‖)
    (‖(2 * (Real.pi : ℂ))⁻¹‖ * ∫ t, ‖verticalSpectrum G (q + 1) t‖)
  · intro u
    rw [logInverse_line_independent hG hstrip 0 (q - 1) u]
    exact logInverse_bound G (q - 1) u
  · intro u
    rw [logInverse_line_independent hG hstrip 0 (q + 1) u]
    exact logInverse_bound G (q + 1) u

def multiplicativeInverse (G : ℂ → ℂ) (t : ℝ) : ℂ :=
  logInverse G 0 (Real.log t)

/-- The exact dt/t form, including any real positive or negative moment. -/
theorem integrable_multiplicative_power_moment {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G) (q : ℝ) :
    IntegrableOn (fun t => ‖multiplicativeInverse G t‖ * t ^ q / t) (Ioi 0) := by
  have h := (integrableOn_comp_log_Ioi_zero
    (fun u => ‖logInverse G 0 u‖ * Real.exp (q * u))).mpr
      (integrable_log_power_moment hG hstrip q)
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  change t⁻¹ * (‖logInverse G 0 (Real.log t)‖ * Real.exp (q * Real.log t)) =
    ‖logInverse G 0 (Real.log t)‖ * t ^ q / t
  rw [Real.rpow_def_of_pos ht, mul_comm (Real.log t) q]
  ring

end ThetaGlobal.DeconvolverMoments

