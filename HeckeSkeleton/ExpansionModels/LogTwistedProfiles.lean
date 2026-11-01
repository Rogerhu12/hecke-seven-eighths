import HeckeSkeleton.ExpansionModels.LogProfileFourier

/-!
# Compact logarithmic profiles with real and imaginary exponential twists

The real part ranges over a fixed compact interval.  Imaginary twists have
explicit polynomial seminorm growth.  The zero-imaginary specialization
supplies rapid Mellin decay uniformly throughout a closed real strip.
-/

set_option autoImplicit false
noncomputable section
namespace ExpansionRecipe.LogProfile

open MeasureTheory
open scoped Classical ContDiff FourierTransform

def linearExp (z : ℂ) (y : ℝ) : ℂ := Complex.exp (z * (y : ℂ))

lemma linearExp_smooth (z : ℂ) : ContDiff ℝ ∞ (linearExp z) := by
  have h : ContDiff ℝ ∞ (fun y : ℝ => z * (y : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  exact h.cexp

lemma linearExp_hasDerivAt (z : ℂ) (y : ℝ) :
    HasDerivAt (linearExp z) (z * linearExp z y) y := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul z).cexp
  convert! h using 1; simp [linearExp, mul_comm]

lemma iteratedDeriv_linearExp (z : ℂ) (n : ℕ) :
    iteratedDeriv n (linearExp z) = fun y => z ^ n * linearExp z y := by
  induction n with
  | zero => ext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    rw [deriv_const_mul_field, (linearExp_hasDerivAt z y).deriv, pow_succ]
    ring

lemma linearExp_derivative_norm (z : ℂ) (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (linearExp z) y‖ = ‖z‖ ^ j * Real.exp (z.re * y) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_linearExp]
  simp [linearExp, norm_pow, Complex.norm_exp]

lemma linearExp_window_derivative_le (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (K j : ℕ) (hj : j ≤ K) (z : ℂ) (hz : |z.re| ≤ H) (y : ℝ) (hy : |y| ≤ L) :
    ‖iteratedFDeriv ℝ j (linearExp z) y‖ ≤
      ((1 + H) ^ K * Real.exp (H * L)) * (1 + |z.im|) ^ K := by
  rw [linearExp_derivative_norm]
  have hbase : 1 ≤ (1 + H) * (1 + |z.im|) := by
    nlinarith [abs_nonneg z.im]
  have hnorm : ‖z‖ ≤ (1 + H) * (1 + |z.im|) := by
    have hn := Complex.norm_le_abs_re_add_abs_im z
    nlinarith [abs_nonneg z.im]
  have hp : ‖z‖ ^ j ≤ ((1 + H) * (1 + |z.im|)) ^ K :=
    (pow_le_pow_left₀ (norm_nonneg z) hnorm j).trans (pow_le_pow_right₀ hbase hj)
  have hre : z.re * y ≤ H * L := by
    calc
      _ ≤ |z.re * y| := le_abs_self _
      _ = |z.re| * |y| := abs_mul _ _
      _ ≤ H * L := mul_le_mul hz hy (abs_nonneg y) hH
  calc
    _ ≤ ((1 + H) * (1 + |z.im|)) ^ K * Real.exp (H * L) :=
      mul_le_mul hp (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [mul_pow]; ring

def compactExpTwist (Ω : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (z : ℂ) : SchwartzMap ℝ ℂ :=
  (hΩc.mul_right : HasCompactSupport (fun y => Ω y * linearExp z y)).toSchwartzMap
    (hΩ.mul (linearExp_smooth z))

@[simp] lemma compactExpTwist_apply (Ω : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (z : ℂ) (y : ℝ) :
    compactExpTwist Ω hΩc hΩ z y = Ω y * linearExp z y := rfl

/-- Uniform in the entire vertical strip, with an explicit polynomial cost
in the imaginary parameter and all spatial seminorm powers. -/
theorem compact_exp_twist_uniform_seminorm (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ H → ∀ k j : ℕ, j ≤ K →
      SchwartzMap.seminorm ℝ k j (compactExpTwist Ω hΩc hΩ z) ≤
        L ^ k * C * (1 + |z.im|) ^ K := by
  obtain ⟨CΩ, hCΩ, hbΩ⟩ := hΩc.exists_bound_iteratedFDeriv hΩ K
  let CE := (1 + H) ^ K * Real.exp (H * L)
  refine ⟨(2 : ℝ) ^ K * CΩ * CE, by dsimp [CE]; positivity, ?_⟩
  intro z hz k j hj
  apply SchwartzMap.seminorm_le_bound ℝ k j _ (by dsimp [CE]; positivity)
  intro y
  change ‖y‖ ^ k * ‖iteratedFDeriv ℝ j (fun y => Ω y * linearExp z y) y‖ ≤ _
  by_cases hzero : ‖iteratedFDeriv ℝ j (fun y => Ω y * linearExp z y) y‖ = 0
  · rw [hzero, mul_zero]
    dsimp [CE]
    positivity
  have hs : y ∈ tsupport Ω := tsupport_mul_subset_left
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hzero))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hs)
  have hb : ‖iteratedFDeriv ℝ j (fun y => Ω y * linearExp z y) y‖ ≤
      (2 : ℝ) ^ K * CΩ * (CE * (1 + |z.im|) ^ K) :=
    product_derivative_bound Ω (linearExp z) hΩ (linearExp_smooth z) CΩ
      (CE * (1 + |z.im|) ^ K) hCΩ (by dsimp [CE]; positivity) K j hj y
      (fun i hi => hbΩ i hi y)
      (fun i hi => linearExp_window_derivative_le H L hH hL K i hi z hz y hy)
  calc
    _ ≤ L ^ k * ((2 : ℝ) ^ K * CΩ * (CE * (1 + |z.im|) ^ K)) :=
      mul_le_mul (by simpa [Real.norm_eq_abs] using (pow_le_pow_left₀ (abs_nonneg y) hy k)) hb (norm_nonneg _) (pow_nonneg hL k)
    _ = _ := by ring

/-- Rapid Fourier decay uniform in a compact real exponential twist.
For Ω(y)=W(exp(-y)), this is the uniform Mellin strip estimate. -/
theorem compact_real_exp_twist_uniform_fourier_decay (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, |a| ≤ H → ∀ t : ℝ,
      (1 + ‖t‖) ^ J * ‖(𝓕 (compactExpTwist Ω hΩc hΩ (a : ℂ))) t‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_exp_twist_uniform_seminorm Ω hΩc hΩ
    H L hH hL hwindow J
  let C' := (1 + L ^ integrationPower) * C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ) ^ J * (fourierSeminormConstant 0 C' + fourierSeminormConstant J C'),
    mul_nonneg (by positivity) (add_nonneg (fourierSeminormConstant_nonneg 0 C' hC')
      (fourierSeminormConstant_nonneg J C' hC')), ?_⟩
  intro a ha t
  let g := compactExpTwist Ω hΩc hΩ (a : ℂ)
  have hseminorm (i : ℕ) (hi : i ≤ J) :
      SchwartzMap.seminorm ℝ 0 i g + SchwartzMap.seminorm ℝ integrationPower i g ≤ C' := by
    have h0 := hb (a : ℂ) ha 0 i hi
    have hp := hb (a : ℂ) ha integrationPower i hi
    simp only [Complex.ofReal_im, abs_zero, add_zero, one_pow, mul_one,
      pow_zero, one_mul] at h0 hp
    dsimp [C']
    linarith
  have h0 : ‖(𝓕 g) t‖ ≤ fourierSeminormConstant 0 C' := by
    have he := SchwartzMap.le_seminorm ℝ 0 0 (𝓕 g) t
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at he
    exact he.trans (fourier_seminorm_le g 0 C' hC' (fun i hi => hseminorm i (by omega)))
  have hJ : ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤ fourierSeminormConstant J C' := by
    have he := SchwartzMap.le_seminorm ℝ J 0 (𝓕 g) t
    simp only [norm_iteratedFDeriv_zero] at he
    exact he.trans (fourier_seminorm_le g J C' hC' hseminorm)
  calc
    _ ≤ ((2 : ℝ) ^ J * (1 + ‖t‖ ^ J)) * ‖(𝓕 g) t‖ :=
      mul_le_mul_of_nonneg_right (one_add_norm_pow_le t J) (norm_nonneg _)
    _ = (2 : ℝ) ^ J * (‖(𝓕 g) t‖ + ‖t‖ ^ J * ‖(𝓕 g) t‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h0 hJ) (by positivity)

end ExpansionRecipe.LogProfile

#print axioms ExpansionRecipe.LogProfile.compact_exp_twist_uniform_seminorm
#print axioms ExpansionRecipe.LogProfile.compact_real_exp_twist_uniform_fourier_decay
