import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
/-!
A logarithmic Fourier/Mellin decay theorem from actual L1 derivative norms.
This provides the profile input used by the finite boundary theorem;
it does not postulate any vertical decay or contour integral estimate.
-/

noncomputable section
namespace HighBinBoundary.LogFourier

open MeasureTheory Complex
open scoped FourierTransform Topology ContDiff

attribute [local instance 101] secondCountableTopologyEither_of_left

/-- Positive-sign Fourier frequency, normalized to match exp(i*t*log u). -/
def transform (f : ℝ → ℂ) (t : ℝ) : ℂ := 𝓕 f (-t / (2 * Real.pi))

/-- The exact exponential-integral dictionary, including 2*pi normalization. -/
theorem transform_eq_integral (f : ℝ → ℂ) (t : ℝ) :
    transform f t = ∫ v : ℝ, Complex.exp ((v * t : ℝ) * I) * f v := by
  unfold transform
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [smul_eq_mul]
  congr 3
  field_simp [Real.pi_ne_zero]

/-- The elementary L1 Fourier bound in the normalization above. -/
theorem norm_transform_le (f : ℝ → ℂ) (t : ℝ) :
    ‖transform f t‖ ≤ ∫ v : ℝ, ‖f v‖ := by
  unfold transform
  rw [Real.fourier_real_eq]
  apply (norm_integral_le_integral_norm _).trans_eq
  simp_rw [Circle.norm_smul]

/-- n integrations by parts, supplied by Mathlib's Fourier derivative theorem. -/
theorem norm_transform_iteratedDeriv (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hi : ∀ j : ℕ, Integrable (iteratedDeriv j f))
    (n : ℕ) (t : ℝ) :
    ‖transform (iteratedDeriv n f) t‖ = |t| ^ n * ‖transform f t‖ := by
  have h := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hf
    (fun j _ => hi j) (n := n) (by simp)
  have ht := congrArg (fun h : ℝ → ℂ => h (-t / (2 * Real.pi))) h
  have hcoef : 2 * (Real.pi : ℂ) * I * ((-t / (2 * Real.pi) : ℝ) : ℂ) =
      -(t : ℂ) * I := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  change transform (iteratedDeriv n f) t =
    (2 * (Real.pi : ℂ) * I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) ^ n * transform f t at ht
  rw [hcoef] at ht
  rw [ht]
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    norm_I, mul_one]

/-- A convenient two-term version of the binomial bound. -/
theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ 2 ^ n * (1 + x ^ n) := by
  rcases le_or_gt x 1 with h | h
  · calc
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ _ := by
        have hp : 0 ≤ x ^ n := pow_nonneg hx n
        have htwo : 0 ≤ (2 : ℝ) ^ n := by positivity
        nlinarith
  · calc
      _ ≤ (2 * x) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * x ^ n := mul_pow _ _ _
      _ ≤ _ := by
        have htwo : 0 ≤ (2 : ℝ) ^ n := by positivity
        nlinarith

/-- Uniform vertical decay with an explicit finite L1 derivative seminorm.
No Fourier decay estimate is assumed; all orders follow from smoothness
and the actual integrability of the derivatives. -/
theorem weighted_transform_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hi : ∀ j : ℕ, Integrable (iteratedDeriv j f))
    (n : ℕ) (t : ℝ) :
    (1 + |t|) ^ n * ‖transform f t‖ ≤
      2 ^ n * ((∫ v : ℝ, ‖f v‖) + ∫ v : ℝ, ‖iteratedDeriv n f v‖) := by
  have h0 := norm_transform_le f t
  have hn := norm_transform_le (iteratedDeriv n f) t
  rw [norm_transform_iteratedDeriv f hf hi n t] at hn
  calc
    _ ≤ (2 ^ n * (1 + |t| ^ n)) * ‖transform f t‖ :=
      mul_le_mul_of_nonneg_right (one_add_pow_le |t| (abs_nonneg t) n) (norm_nonneg _)
    _ = 2 ^ n * (‖transform f t‖ + |t| ^ n * ‖transform f t‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h0 hn) (by positivity)

/-- A positive constant for every external derivative order. -/
theorem exists_rapid_transform_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hi : ∀ j : ℕ, Integrable (iteratedDeriv j f))
    (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, (1 + |t|) ^ n * ‖transform f t‖ ≤ D := by
  let D : ℝ := 2 ^ n * ((∫ v : ℝ, ‖f v‖) + ∫ v : ℝ, ‖iteratedDeriv n f v‖)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D + 1, by linarith, ?_⟩
  intro t
  exact (weighted_transform_bound f hf hi n t).trans (by dsimp only [D]; linarith)

/-! An actual log-Euler family gives all L1 derivatives of its exponential
weight. This elementary closure is the only new step needed before applying
the Fourier theorem to the project's genuine orbital profiles. -/

def weightedProfile (P : ℕ → ℝ → ℂ) (σ : ℝ) (j : ℕ) (v : ℝ) : ℂ :=
  (Real.exp (σ * v) : ℂ) * P j v

theorem weightedProfile_smooth (P : ℕ → ℝ → ℂ) (σ : ℝ)
    (hc : ∀ j, ContDiff ℝ ∞ (P j)) (j : ℕ) :
    ContDiff ℝ ∞ (weightedProfile P σ j) := by
  exact (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_id).exp).mul (hc j)

theorem weightedProfile_deriv (P : ℕ → ℝ → ℂ) (σ : ℝ)
    (hd : ∀ j v, HasDerivAt (P j) (P (j + 1) v) v) (j : ℕ) :
    deriv (weightedProfile P σ j) =
      fun v => (σ : ℂ) * weightedProfile P σ j v + weightedProfile P σ (j + 1) v := by
  funext v
  have he : HasDerivAt (fun t : ℝ => (Real.exp (σ * t) : ℂ))
      ((σ : ℂ) * (Real.exp (σ * v) : ℂ)) v := by
    simpa only [id_eq, mul_one, Complex.ofReal_mul, mul_comm] using
      (((hasDerivAt_id v).const_mul σ).exp).ofReal_comp
  have h := he.mul (hd j v)
  change deriv ((fun t : ℝ => (Real.exp (σ * t) : ℂ)) * P j) v =
    (σ : ℂ) * ((Real.exp (σ * v) : ℂ) * P j v) +
      (Real.exp (σ * v) : ℂ) * P (j + 1) v
  simpa only [Pi.mul_apply, mul_assoc] using h.deriv

theorem weightedProfile_integrable (P : ℕ → ℝ → ℂ) (σ : ℝ)
    (hc : ∀ j, ContDiff ℝ ∞ (P j))
    (hi : ∀ j, Integrable (fun v => Real.exp (σ * v) * ‖P j v‖)) (j : ℕ) :
    Integrable (weightedProfile P σ j) := by
  apply (integrable_norm_iff
    (weightedProfile_smooth P σ hc j).continuous.aestronglyMeasurable).mp
  convert hi j using 1
  funext v
  simp only [weightedProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem weightedProfile_iteratedDeriv_integrable (P : ℕ → ℝ → ℂ) (σ : ℝ)
    (hc : ∀ j, ContDiff ℝ ∞ (P j))
    (hd : ∀ j v, HasDerivAt (P j) (P (j + 1) v) v)
    (hi : ∀ j, Integrable (fun v => Real.exp (σ * v) * ‖P j v‖))
    (n : ℕ) : ∀ j, Integrable (iteratedDeriv n (weightedProfile P σ j)) := by
  induction n with
  | zero =>
      intro j
      simpa using weightedProfile_integrable P σ hc hi j
  | succ n ih =>
      intro j
      rw [iteratedDeriv_succ', weightedProfile_deriv P σ hd j]
      have hcm : ContDiff ℝ ∞
          (fun v : ℝ => (σ : ℂ) * weightedProfile P σ j v) :=
        contDiff_const.mul (weightedProfile_smooth P σ hc j)
      have heq :
          iteratedDeriv n
            (fun v => (σ : ℂ) * weightedProfile P σ j v + weightedProfile P σ (j + 1) v) =
          fun v => (σ : ℂ) * iteratedDeriv n (weightedProfile P σ j) v +
            iteratedDeriv n (weightedProfile P σ (j + 1)) v := by
        funext v
        rw [iteratedDeriv_fun_add
          (hcm.of_le (by simp)).contDiffAt
          ((weightedProfile_smooth P σ hc (j + 1)).of_le (by simp)).contDiffAt,
          iteratedDeriv_const_mul_field]
      rw [heq]
      exact ((ih j).const_mul (σ : ℂ)).add (ih (j + 1))

#print axioms weightedProfile_iteratedDeriv_integrable
#print axioms transform_eq_integral
#print axioms weighted_transform_bound
#print axioms exists_rapid_transform_bound

end HighBinBoundary.LogFourier
