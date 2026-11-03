import ExpansionInterfaces.AnnularMellinIdentity
import ExpansionInterfaces.FiniteMellinRectangle

/-!
# Annular polynomial upper bounds from finite-height L-function control

The main estimate is derived from L (or reciprocal L) on a finite rectangle,
its absolute initial line, and the actual Mellin profile.  Horizontal faces
and the initial-line tail remain explicit.  No final polynomial upper bound
is included among the assumptions.
-/

noncomputable section
namespace ExpansionInterfaces.Mellin
open MeasureTheory Set
open scoped Classical BigOperators

def annularKernel (W : AnnularProfile) (L : ℂ → ℂ) (s : ℂ) (X : ℝ) (z : ℂ) : ℂ :=
  mellin W.function z * L (s + z) * (X : ℂ) ^ z

theorem annularKernel_differentiableOn (W : AnnularProfile) (L : ℂ → ℂ)
    (s : ℂ) {X : ℝ} (hX : 0 < X) (D : Set ℂ)
    (hL : DifferentiableOn ℂ (fun z => L (s + z)) D) :
    DifferentiableOn ℂ (annularKernel W L s X) D := by
  exact (W.mellin_differentiable.differentiableOn.mul hL).mul
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).differentiableOn

theorem annularKernel_vertical_norm (W : AnnularProfile) (L : ℂ → ℂ)
    (s : ℂ) {X : ℝ} (hX : 0 < X) (σ t : ℝ) :
    ‖annularKernel W L s X (vertical σ t)‖ =
      ‖mellin W.function (vertical σ t)‖ * ‖L (s + vertical σ t)‖ * X ^ σ := by
  simp only [annularKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, vertical_re]

theorem annularKernel_vertical_norm_le (W : AnnularProfile) (L : ℂ → ℂ)
    (s : ℂ) {X σ t C : ℝ} (hX : 0 < X)
    (hL : ‖L (s + vertical σ t)‖ ≤ C) :
    ‖annularKernel W L s X (vertical σ t)‖ ≤
      (C * X ^ σ) * ‖mellin W.function (vertical σ t)‖ := by
  rw [annularKernel_vertical_norm W L s hX]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hL (norm_nonneg (mellin W.function (vertical σ t))))
    (Real.rpow_nonneg hX.le σ)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

theorem annularKernel_vertical_integrable (W : AnnularProfile) (L : ℂ → ℂ)
    (s : ℂ) {X σ C : ℝ} (hX : 0 < X)
    (hm : AEStronglyMeasurable (fun t : ℝ => L (s + vertical σ t)))
    (hL : ∀ t, ‖L (s + vertical σ t)‖ ≤ C) :
    Integrable (fun t : ℝ => annularKernel W L s X (vertical σ t)) := by
  have hMv : Continuous (fun t : ℝ => mellin W.function (vertical σ t)) :=
    W.mellin_differentiable.continuous.comp (by unfold vertical; fun_prop)
  have hPow : Continuous (fun t : ℝ => (X : ℂ) ^ vertical σ t) :=
    (by unfold vertical; fun_prop : Continuous (fun t : ℝ => vertical σ t)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  apply ((W.vertical_norm_integrable σ).const_mul (C * X ^ σ)).mono'
    ((hMv.aestronglyMeasurable.mul hm).mul hPow.aestronglyMeasurable)
  exact ae_of_all _ fun t => annularKernel_vertical_norm_le W L s hX (hL t)

theorem annularKernel_left_segment_bound (W : AnnularProfile) (L : ℂ → ℂ)
    (s : ℂ) {X a H M : ℝ} (hX : 0 < X) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hL : ∀ t, |t| ≤ H → ‖L (s + vertical a t)‖ ≤ M) :
    ‖verticalSegment (annularKernel W L s X) a H‖ ≤
      (M * X ^ a) * (∫ t : ℝ, ‖mellin W.function (vertical a t)‖) := by
  let g : ℝ → ℝ := fun t => (M * X ^ a) * ‖mellin W.function (vertical a t)‖
  have hg : Integrable g := (W.vertical_norm_integrable a).const_mul (M * X ^ a)
  have hgn : ∀ t, 0 ≤ g t := fun t =>
    mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hX.le a)) (norm_nonneg _)
  have hb : ∀ᵐ t : ℝ, t ∈ Ioc (-H) H →
      ‖annularKernel W L s X (vertical a t)‖ ≤ g t :=
    ae_of_all _ fun t ht => annularKernel_vertical_norm_le W L s hX
      (hL t (abs_le.mpr ⟨ht.1.le, ht.2⟩))
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (by linarith : -H ≤ H) hb hg.intervalIntegrable
  calc
    ‖verticalSegment (annularKernel W L s X) a H‖ ≤ ∫ t : ℝ in -H..H, g t := hi
    _ ≤ ∫ t : ℝ, g t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral hg (ae_of_all _ hgn)
    _ = _ := integral_const_mul _ _

/-- Quantitative finite-height estimate before the Mellin prefactor.
Mleft is the sharp left-line bound; M is allowed to be a coarser rectangle
bound.  A bounds the entire initial line, and K bounds the profile on the
two horizontal faces.  In particular, coarse horizontal conductor growth
does not replace the sharp reflected-L conductor power in the main term. -/
theorem annularKernel_rectangle_bound (W : AnnularProfile) (L : ℂ → ℂ)
    (s : ℂ) {X a b H Mleft M A K : ℝ}
    (hX : 1 ≤ X) (hab : a ≤ b) (hH : 0 ≤ H)
    (hMleft : 0 ≤ Mleft) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hLdiff : DifferentiableOn ℂ (fun z => L (s + z)) (closedRectangle a b H))
    (hLrect : ∀ z ∈ closedRectangle a b H, ‖L (s + z)‖ ≤ M)
    (hLleft : ∀ t, |t| ≤ H → ‖L (s + vertical a t)‖ ≤ Mleft)
    (hLmeas : AEStronglyMeasurable (fun t : ℝ => L (s + vertical b t)))
    (hLright : ∀ t, ‖L (s + vertical b t)‖ ≤ A)
    (hWbot : ∀ x ∈ Icc a b, ‖mellin W.function (vertical x (-H))‖ ≤ K)
    (hWtop : ∀ x ∈ Icc a b, ‖mellin W.function (vertical x H)‖ ≤ K) :
    ‖∫ t : ℝ, annularKernel W L s X (vertical b t)‖ ≤
      (Mleft * X ^ a) * (∫ t : ℝ, ‖mellin W.function (vertical a t)‖) +
        2 * K * M * X ^ b * (b - a) +
          (A * X ^ b) * (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical b t)‖) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hF := annularKernel_differentiableOn W L s hX0 _ hLdiff
  have hi := annularKernel_vertical_integrable W L s hX0 hLmeas hLright
  have hedges : ∀ y : ℝ, |y| ≤ H →
      (∀ x ∈ Icc a b, ‖mellin W.function (vertical x y)‖ ≤ K) →
      ∀ x ∈ Icc a b, ‖annularKernel W L s X (vertical x y)‖ ≤ K * M * X ^ b := by
    intro y hy hW x hx
    have hz : vertical x y ∈ closedRectangle a b H := by
      simpa only [closedRectangle, mem_ofPred_eq, vertical_re, vertical_im] using ⟨hx.1, hx.2, hy⟩
    rw [annularKernel_vertical_norm W L s hX0]
    calc
      _ ≤ K * M * X ^ x := mul_le_mul_of_nonneg_right
        (mul_le_mul (hW x hx) (hLrect _ hz) (norm_nonneg _) hK)
        (Real.rpow_nonneg hX0.le x)
      _ ≤ K * M * X ^ b := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX hx.2) (mul_nonneg hK hM)
  have hbot := hedges (-H) (by simpa only [abs_neg, abs_of_nonneg hH] using (le_rfl : H ≤ H)) hWbot
  have htop := hedges H (by simpa only [abs_of_nonneg hH] using (le_rfl : H ≤ H)) hWtop
  have hmain := full_line_from_rectangle (annularKernel W L s X)
    (fun t => mellin W.function (vertical b t)) hab hH hF hi (W.vertical_integrable b)
    hbot htop (fun t => annularKernel_vertical_norm_le W L s hX0 (hLright t))
  have hleft := annularKernel_left_segment_bound W L s hX0 hH hMleft hLleft
  nlinarith

/-- The upper bound for the literal finite annular polynomial follows from
the actual L-function data above and its initial Dirichlet calibration. -/
theorem annular_polynomial_upper_from_rectangle {ι : Type*} [Countable ι]
    (W : AnnularProfile) (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (L : ℂ → ℂ) (s : ℂ) {X a b H Mleft M A K : ℝ}
    (hX : 1 ≤ X) (hab : a ≤ b) (hH : 0 ≤ H)
    (hMleft : 0 ≤ Mleft) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + b))))
    (hline : ∀ t, L (s + vertical b t) = dirichletSeries c N (s + vertical b t))
    (hLdiff : DifferentiableOn ℂ (fun z => L (s + z)) (closedRectangle a b H))
    (hLrect : ∀ z ∈ closedRectangle a b H, ‖L (s + z)‖ ≤ M)
    (hLleft : ∀ t, |t| ≤ H → ‖L (s + vertical a t)‖ ≤ Mleft)
    (hLmeas : AEStronglyMeasurable (fun t : ℝ => L (s + vertical b t)))
    (hLright : ∀ t, ‖L (s + vertical b t)‖ ≤ A)
    (hWbot : ∀ x ∈ Icc a b, ‖mellin W.function (vertical x (-H))‖ ≤ K)
    (hWtop : ∀ x ∈ Icc a b, ‖mellin W.function (vertical x H)‖ ≤ K)
    (S : Finset ι) (hS : ∀ i, N i ≤ W.upper * X → i ∈ S) :
    ‖∑ i ∈ S, smoothedTerm W c N s X i‖ ≤ (1 / (2 * Real.pi)) *
      ((Mleft * X ^ a) * (∫ t : ℝ, ‖mellin W.function (vertical a t)‖) +
        2 * K * M * X ^ b * (b - a) +
          (A * X ^ b) * (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical b t)‖)) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  rw [← annular_mellin_finite_of_initial_line W c N hN L s b X hX0 hsum hline S hS,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left
    (annularKernel_rectangle_bound W L s hX hab hH hMleft hM hK hLdiff hLrect hLleft
      hLmeas hLright hWbot hWtop)
    (by positivity)

/-- Initial-line measurability and its uniform bound are also consequences
of the same summable coefficient sequence.  The displayed initial constant
is the absolute Dirichlet series, not an additional analytic hypothesis. -/
theorem annular_polynomial_upper_from_dirichlet_rectangle {ι : Type*} [Countable ι]
    (W : AnnularProfile) (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (L : ℂ → ℂ) (s : ℂ) {X a b H Mleft M K : ℝ}
    (hX : 1 ≤ X) (hab : a ≤ b) (hH : 0 ≤ H)
    (hMleft : 0 ≤ Mleft) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + b))))
    (hline : ∀ t, L (s + vertical b t) = dirichletSeries c N (s + vertical b t))
    (hLdiff : DifferentiableOn ℂ (fun z => L (s + z)) (closedRectangle a b H))
    (hLrect : ∀ z ∈ closedRectangle a b H, ‖L (s + z)‖ ≤ M)
    (hLleft : ∀ t, |t| ≤ H → ‖L (s + vertical a t)‖ ≤ Mleft)
    (hWbot : ∀ x ∈ Icc a b, ‖mellin W.function (vertical x (-H))‖ ≤ K)
    (hWtop : ∀ x ∈ Icc a b, ‖mellin W.function (vertical x H)‖ ≤ K)
    (S : Finset ι) (hS : ∀ i, N i ≤ W.upper * X → i ∈ S) :
    ‖∑ i ∈ S, smoothedTerm W c N s X i‖ ≤ (1 / (2 * Real.pi)) *
      ((Mleft * X ^ a) * (∫ t : ℝ, ‖mellin W.function (vertical a t)‖) +
        2 * K * M * X ^ b * (b - a) +
          ((∑' i, ‖c i‖ * N i ^ (-(s.re + b))) * X ^ b) *
            (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical b t)‖)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => L (s + vertical b t)) := by
    have heq : (fun t : ℝ => L (s + vertical b t)) =
        (fun t : ℝ => dirichletSeries c N (s + vertical b t)) := funext hline
    rw [heq]
    exact (dirichletSeries_initial_continuous c N hN s b hsum).aestronglyMeasurable
  have hb : ∀ t, ‖L (s + vertical b t)‖ ≤
      ∑' i, ‖c i‖ * N i ^ (-(s.re + b)) := by
    intro t
    rw [hline t]
    exact dirichletSeries_initial_norm_le c N hN s b t hsum
  exact annular_polynomial_upper_from_rectangle W c N hN L s hX hab hH hMleft hM hK
    hsum hline hLdiff hLrect hLleft hm hb hWbot hWtop S hS

end ExpansionInterfaces.Mellin
