import ThetaGlobal.DeconvolverMoments
import ThetaGlobal.GaussianRegularization

/-!
# A Gaussian converts explicit exponential strip growth into quadratic decay

The fixed-strip input is the ordinary polynomial-times-exponential bound
provided by reciprocal-gamma Stirling estimates. The proof is elementary:
(1+x)^m <= exp(mx), followed by completion of the square. No decay or
integrability of the resulting deconvolver is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GaussianStripDecay

open Set
open DeconvolverMoments

/-- Explicit local strip growth, with natural polynomial degree. -/
def ExponentialStripGrowth (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℝ, ∃ N : ℕ,
    ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ N * Real.exp (A * |t|)

/-- Annular-test Mellin transforms are bounded on each fixed strip. -/
def BoundedOnVerticalStrips (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
    ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C

theorem BoundedOnVerticalStrips.exponentialGrowth {F : ℂ → ℂ}
    (hF : BoundedOnVerticalStrips F) : ExponentialStripGrowth F := by
  intro a b hab
  obtain ⟨C, hC, hbound⟩ := hF a b hab
  refine ⟨C, hC, 0, 0, ?_⟩
  simpa only [pow_zero, zero_mul, Real.exp_zero, mul_one] using hbound

theorem ExponentialStripGrowth.comp_neg {F : ℂ → ℂ}
    (hF : ExponentialStripGrowth F) :
    ExponentialStripGrowth (fun s => F (-s)) := by
  intro a b hab
  obtain ⟨C, hC, A, N, hbound⟩ := hF (-b) (-a) (neg_le_neg hab)
  refine ⟨C, hC, A, N, ?_⟩
  intro c hc t
  have h := hbound (-c) ⟨neg_le_neg hc.2, neg_le_neg hc.1⟩ (-t)
  have he : ((-c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
      -((c : ℂ) + (t : ℂ) * Complex.I) := by push_cast; ring
  rw [he] at h
  simpa only [abs_neg] using h

theorem ExponentialStripGrowth.mul {F G : ℂ → ℂ}
    (hF : ExponentialStripGrowth F) (hG : ExponentialStripGrowth G) :
    ExponentialStripGrowth (fun s => F s * G s) := by
  intro a b hab
  obtain ⟨C₁, hC₁, A₁, N₁, h₁⟩ := hF a b hab
  obtain ⟨C₂, hC₂, A₂, N₂, h₂⟩ := hG a b hab
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, A₁ + A₂, N₁ + N₂, ?_⟩
  intro c hc t
  rw [norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ N₁ * Real.exp (A₁ * |t|)) *
        (C₂ * (1 + |t|) ^ N₂ * Real.exp (A₂ * |t|)) :=
      mul_le_mul (h₁ c hc t) (h₂ c hc t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [pow_add, add_mul, Real.exp_add]
      ring

theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ Real.exp ((n : ℝ) * x) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by linarith)
  linarith [Real.add_one_le_exp x]

theorem linear_sub_quadratic_le {ε : ℝ} (hε : 0 < ε) (A x : ℝ) :
    A * x - ε * x ^ 2 ≤ A ^ 2 / (4 * ε) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * ε)).mpr
  nlinarith [sq_nonneg (2 * ε * x - A)]

def regularized (F : ℂ → ℂ) (ε : ℝ) (s : ℂ) : ℂ :=
  F s * Complex.exp ((ε : ℂ) * s ^ 2)

/-- The explicit quadratic strip constant. No uniformity as ε -> 0 is claimed
or needed for the fixed-ε moment and Fubini arguments. -/
def stripConstant (C A a b ε : ℝ) (N : ℕ) : ℝ :=
  C * Real.exp (ε * (a ^ 2 + b ^ 2) + (A + ((N + 2 : ℕ) : ℝ)) ^ 2 / (4 * ε))

theorem regularized_strip_bound
    (F : ℂ → ℂ) {a b C A ε : ℝ} (N : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ N * Real.exp (A * |t|)) :
    ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖regularized F ε ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        stripConstant C A a b ε N * (1 + |t|) ^ (-2 : ℝ) := by
  intro c hc t
  have hpoly := one_add_pow_le_exp (abs_nonneg t) (N + 2)
  have hsquare := VerticalContour.square_le_endpoints hc.1 hc.2
  have hcomplete := linear_sub_quadratic_le hε (A + ((N + 2 : ℕ) : ℝ)) |t|
  rw [sq_abs] at hcomplete
  have hexp : ((N + 2 : ℕ) : ℝ) * |t| + (A * |t| + ε * (c ^ 2 - t ^ 2)) ≤
      ε * (a ^ 2 + b ^ 2) + (A + ((N + 2 : ℕ) : ℝ)) ^ 2 / (4 * ε) := by
    have hc' := mul_le_mul_of_nonneg_left hsquare hε.le
    nlinarith
  have hweighted :
      ‖regularized F ε ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (1 + |t|) ^ 2 ≤
        stripConstant C A a b ε N := by
    unfold regularized
    rw [norm_mul]
    change (‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ *
      ‖GaussianRegularization.verticalGaussian ε c t‖) * (1 + |t|) ^ 2 ≤ _
    rw [GaussianRegularization.verticalGaussian_norm]
    calc
      _ ≤ (C * (1 + |t|) ^ N * Real.exp (A * |t|) *
          Real.exp (ε * (c ^ 2 - t ^ 2))) * (1 + |t|) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbound c hc t) (Real.exp_pos _).le)
          (sq_nonneg _)
      _ = C * (1 + |t|) ^ (N + 2) *
          Real.exp (A * |t| + ε * (c ^ 2 - t ^ 2)) := by
        rw [pow_add, Real.exp_add]
        ring
      _ ≤ C * Real.exp (((N + 2 : ℕ) : ℝ) * |t|) *
          Real.exp (A * |t| + ε * (c ^ 2 - t ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_pos _).le
      _ = C * Real.exp (((N + 2 : ℕ) : ℝ) * |t| +
          (A * |t| + ε * (c ^ 2 - t ^ 2))) := by
        simp_rw [Real.exp_add]
        ring
      _ ≤ stripConstant C A a b ε N :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
  have hpos : 0 < (1 + |t|) ^ 2 := by positivity
  have hdiv := (le_div_iff₀ hpos).mpr hweighted
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |t|) 2, Real.rpow_two]
  simpa only [div_eq_mul_inv] using hdiv

theorem quadraticStripDecay_regularized {F : ℂ → ℂ}
    (hF : ExponentialStripGrowth F) {ε : ℝ} (hε : 0 < ε) :
    QuadraticStripDecay (regularized F ε) := by
  intro a b hab
  obtain ⟨C, hC, A, N, hbound⟩ := hF a b hab
  refine ⟨stripConstant C A a b ε N, ?_, ?_⟩
  · exact mul_nonneg hC (Real.exp_pos _).le
  · exact regularized_strip_bound F N hC hε hbound

theorem differentiable_regularized {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (ε : ℝ) :
    Differentiable ℂ (regularized F ε) := by
  exact hF.mul (by fun_prop)

end ThetaGlobal.GaussianStripDecay

