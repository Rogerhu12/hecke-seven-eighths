import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
/-!
Finite rectangle transport and explicit coupled Gaussian profile bounds.
These are Mathlib-only theorems. No row arithmetic, no high-bin estimate,
and no assertion about an unconstructed actual presentation is assumed.
-/

noncomputable section
namespace HighBinBoundary

open MeasureTheory Set Complex
open scoped BigOperators

/-- Exact finite-height contour transport, retaining both horizontal faces. -/
theorem finite_rectangle_identity (F : ℂ → ℂ) (l r H : ℝ)
    (hF : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-H) H)) :
    (∫ t : ℝ in -H..H, F ((r : ℂ) + t * I)) -
      (∫ t : ℝ in -H..H, F ((l : ℂ) + t * I)) =
    I * ((∫ x : ℝ in l..r, F ((x : ℂ) + (-H) * I)) -
      (∫ x : ℝ in l..r, F ((x : ℂ) + H * I))) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l : ℂ) + (-H) * I) ((r : ℂ) + H * I) (by simpa using hF)
  have h' :
      (∫ x : ℝ in l..r, F ((x : ℂ) + (-H) * I)) -
        (∫ x : ℝ in l..r, F ((x : ℂ) + H * I)) +
        I * (∫ t : ℝ in -H..H, F ((r : ℂ) + t * I)) -
        I * (∫ t : ℝ in -H..H, F ((l : ℂ) + t * I)) = 0 := by
    simpa [smul_eq_mul] using h
  have h'' := congrArg (fun z : ℂ => -I * z) h'
  ring_nf at h'' ⊢
  simp only [I_sq] at h''
  linear_combination h''

/-- A bound for the actual finite-height difference, derived from the two
horizontal faces. The amplitude labels never enter this identity. -/
theorem finite_rectangle_bound (F : ℂ → ℂ) (l r H M : ℝ)
    (hF : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-H) H))
    (hminus : ∀ x ∈ uIcc l r, ‖F ((x : ℂ) + (-H) * I)‖ ≤ M)
    (hplus : ∀ x ∈ uIcc l r, ‖F ((x : ℂ) + H * I)‖ ≤ M) :
    ‖(∫ t : ℝ in -H..H, F ((r : ℂ) + t * I)) -
      (∫ t : ℝ in -H..H, F ((l : ℂ) + t * I))‖ ≤
      2 * M * |r - l| := by
  rw [finite_rectangle_identity F l r H hF, norm_mul, norm_I, one_mul]
  have hm := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hminus x (uIoc_subset_uIcc hx))
  have hp := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hplus x (uIoc_subset_uIcc hx))
  exact (norm_sub_le _ _).trans (by linarith)

/-- A completely explicit Gaussian moment constant. -/
def gaussianMoment (n : ℕ) : ℝ := 2 ^ n * (1 + (n.factorial : ℝ))

lemma gaussianMoment_pos (n : ℕ) : 0 < gaussianMoment n := by
  unfold gaussianMoment
  positivity

/-- Uniform arbitrary-order decay of the one-dimensional Gaussian. -/
theorem gaussian_weighted_bound (n : ℕ) (x : ℝ) :
    (1 + |x|) ^ n * Real.exp (-(x ^ 2)) ≤ gaussianMoment n := by
  have he : Real.exp (-(x ^ 2)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have ht : (x ^ 2) ^ n * Real.exp (-(x ^ 2)) ≤ (n.factorial : ℝ) := by
    have hs := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) n
    have hs' : (x ^ 2) ^ n ≤ Real.exp (x ^ 2) * (n.factorial : ℝ) :=
      (div_le_iff₀ hfac).mp hs
    calc
      _ ≤ (Real.exp (x ^ 2) * (n.factorial : ℝ)) * Real.exp (-(x ^ 2)) :=
        mul_le_mul_of_nonneg_right hs' (Real.exp_pos _).le
      _ = _ := by rw [mul_right_comm, ← Real.exp_add]; simp
  by_cases hx : |x| ≤ 1
  · have hpow : (1 + |x|) ^ n ≤ (2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ (2 : ℝ) ^ n * 1 :=
        mul_le_mul hpow he (Real.exp_pos _).le (by positivity)
      _ ≤ gaussianMoment n := by
        unfold gaussianMoment
        have hf : 0 ≤ (n.factorial : ℝ) := by positivity
        have htwo : 0 ≤ (2 : ℝ) ^ n := by positivity
        nlinarith
  · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hx2 : |x| ≤ x ^ 2 := by nlinarith [sq_abs x]
    have hp : (1 + |x|) ^ n ≤ (2 : ℝ) ^ n * (x ^ 2) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ ((2 : ℝ) ^ n * (x ^ 2) ^ n) * Real.exp (-(x ^ 2)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = (2 : ℝ) ^ n * ((x ^ 2) ^ n * Real.exp (-(x ^ 2))) := by ring
      _ ≤ (2 : ℝ) ^ n * (n.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ gaussianMoment n := by
        unfold gaussianMoment
        have htwo : 0 ≤ (2 : ℝ) ^ n := by positivity
        nlinarith

/-- The coupled Gaussian is weak near z=-s. Decay of the z-profile covers
that region through this multiplicative height inequality. -/
theorem coupled_height_le (x y : ℝ) :
    1 + |x| ≤ (1 + |x + y|) * (1 + |y|) := by
  have hx : |x| ≤ |x + y| + |y| := by
    simpa using (abs_add_le (x + y) (-y))
  have hp : 0 ≤ |x + y| * |y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

/-- Transfer rapid z-profile decay across the coupled Gaussian to the
s-height. The estimate is uniform in both real heights. -/
theorem coupled_gaussian_profile_bound (g : ℝ → ℂ) (n : ℕ) (D : ℝ)
    (hg : ∀ y : ℝ, (1 + |y|) ^ n * ‖g y‖ ≤ D)
    (x y : ℝ) :
    (1 + |x|) ^ n * (Real.exp (-((x + y) ^ 2)) * ‖g y‖) ≤
      gaussianMoment n * D := by
  have hp : (1 + |x|) ^ n ≤ (1 + |x + y|) ^ n * (1 + |y|) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (coupled_height_le x y) n
  calc
    _ ≤ ((1 + |x + y|) ^ n * (1 + |y|) ^ n) *
        (Real.exp (-((x + y) ^ 2)) * ‖g y‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = ((1 + |x + y|) ^ n * Real.exp (-((x + y) ^ 2))) *
        ((1 + |y|) ^ n * ‖g y‖) := by ring
    _ ≤ gaussianMoment n * D :=
      mul_le_mul (gaussian_weighted_bound n (x + y)) (hg y)
        (by positivity) (gaussianMoment_pos n).le

/-- The entire Gaussian alone has no uniform decay on a horizontal s-face
when z runs over the same box: the opposite corner cancels its imaginary part. -/
theorem gaussian_corner_no_decay (σ ν H : ℝ) :
    ‖Complex.exp ((((σ : ℂ) + H * I) + ((ν : ℂ) + (-H) * I) - 1) ^ 2)‖ =
      Real.exp ((σ + ν - 1) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two]

#print axioms finite_rectangle_identity
#print axioms finite_rectangle_bound
#print axioms gaussian_weighted_bound
#print axioms coupled_gaussian_profile_bound
#print axioms gaussian_corner_no_decay

end HighBinBoundary
