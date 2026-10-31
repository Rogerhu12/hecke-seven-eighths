import HeckeSkeleton.ExpansionModels.LogTwistedProfiles
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SharedFourierPropagation

/-!
# Mixed parameter derivatives and a weighted common Fourier measure

The norm-power profile becomes a linear exponential after logarithmic
coordinates.  Both real and imaginary parameter derivatives are proved
literally below; they insert fixed polynomial factors in the one common
logarithmic window.  The weighted Fourier mass is then derived from the
actual Schwartz Fourier transform.  Its order is chosen from the child
weight before the moving height, and it has explicit polynomial height
growth.  No Fourier mass or row-energy bound is an input to this result.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open _root_.ExpansionRecipe.LogProfile

/-- The scalar cost in the genuine Fourier moment estimate. -/
def profileFourierCost (J : ℕ) (C : ℝ) : ℝ :=
  2 ^ J * (fourierMomentConstant 0 C + fourierMomentConstant J C)

theorem profileFourierCost_nonneg (J : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ profileFourierCost J C := by
  exact mul_nonneg (by positivity)
    (add_nonneg (fourierMomentConstant_nonneg 0 C hC)
      (fourierMomentConstant_nonneg J C hC))

theorem profileFourierCost_mul (J : ℕ) (C D : ℝ) :
    profileFourierCost J (C * D) = profileFourierCost J C * D := by
  unfold profileFourierCost fourierMomentConstant fourierSeminormConstant
  ring

/-- The common weighted Fourier mass for an entire vertical strip.
The exponent `J + integrationPower` is fixed before the height parameter.
In particular the Fourier variable is integrated over the entire line. -/
theorem compact_exp_twist_uniform_fourier_moment (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ H →
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (compactExpTwist Ω hΩc hΩ z)) t‖) ≤
          C * (1 + |z.im|) ^ (J + integrationPower) := by
  obtain ⟨C, hC, hb⟩ := compact_exp_twist_uniform_seminorm Ω hΩc hΩ
    H L hH hL hwindow (J + integrationPower)
  let C' := (1 + L ^ integrationPower) * C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨profileFourierCost J C', profileFourierCost_nonneg J hC', ?_⟩
  intro z hz
  have hbound (j : ℕ) (hj : j ≤ J + integrationPower) :
      SchwartzMap.seminorm ℝ 0 j (compactExpTwist Ω hΩc hΩ z) +
          SchwartzMap.seminorm ℝ integrationPower j (compactExpTwist Ω hΩc hΩ z) ≤
        C' * (1 + |z.im|) ^ (J + integrationPower) := by
    have h0 := hb z hz 0 j hj
    have hp := hb z hz integrationPower j hj
    simp only [pow_zero, one_mul] at h0
    dsimp [C']
    nlinarith
  have h := uniform_fourier_one_plus_moment (compactExpTwist Ω hΩc hΩ z)
    J (C' * (1 + |z.im|) ^ (J + integrationPower)) (by positivity) hbound
  change _ ≤ profileFourierCost J (C' * (1 + |z.im|) ^ (J + integrationPower)) at h
  exact h.trans_eq (profileFourierCost_mul _ _ _)

/-- A generic affine exponential derivative, used to keep both parameter
directions literal rather than introducing an abstract derivative oracle. -/
theorem iteratedDeriv_affine_exp (c b z : ℂ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => c * Complex.exp (b + z * (t : ℂ))) x =
      c * z ^ n * Complex.exp (b + z * (x : ℂ)) := by
  have he : (fun t : ℝ => c * Complex.exp (b + z * (t : ℂ))) =
      fun t => (c * Complex.exp b) * linearExp z t := by
    funext t
    simp only [linearExp, Complex.exp_add]
    ring
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_linearExp]
  simp only [linearExp, Complex.exp_add]
  ring

/-- Mixed derivatives in the real and imaginary norm-power parameters.
The same original window survives, multiplied by fixed log-coordinate
powers; no differentiation of a discrete presentation selector is used. -/
theorem mixed_parameter_derivative (Ω : ℝ → ℂ) (r s : ℕ) (a ν y : ℝ) :
    iteratedDeriv r (fun a' : ℝ => iteratedDeriv s
      (fun ν' : ℝ => Ω y * linearExp ((a' : ℂ) + (ν' : ℂ) * Complex.I) y) ν) a =
      (y : ℂ) ^ r * (Complex.I * (y : ℂ)) ^ s * Ω y *
        linearExp ((a : ℂ) + (ν : ℂ) * Complex.I) y := by
  have hi (a' : ℝ) :
      iteratedDeriv s
        (fun ν' : ℝ => Ω y * linearExp ((a' : ℂ) + (ν' : ℂ) * Complex.I) y) ν =
      Ω y * (Complex.I * (y : ℂ)) ^ s *
        Complex.exp ((ν : ℂ) * Complex.I * (y : ℂ) + (y : ℂ) * (a' : ℂ)) := by
    have he : (fun ν' : ℝ => Ω y * linearExp ((a' : ℂ) + (ν' : ℂ) * Complex.I) y) =
        fun ν' => Ω y * Complex.exp ((a' : ℂ) * (y : ℂ) +
          (Complex.I * (y : ℂ)) * (ν' : ℂ)) := by
      funext ν'
      congr 2
      unfold linearExp
      congr 1
      ring
    rw [he, iteratedDeriv_affine_exp]
    congr 2
    ring
  simp_rw [hi]
  rw [iteratedDeriv_affine_exp]
  unfold linearExp
  have harg : (ν : ℂ) * Complex.I * (y : ℂ) + (y : ℂ) * (a : ℂ) =
      ((a : ℂ) + (ν : ℂ) * Complex.I) * (y : ℂ) := by ring
  rw [harg]
  ring

def mixedLogWindow (Ω : ℝ → ℂ) (r s : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ r * (Complex.I * (y : ℂ)) ^ s * Ω y

theorem mixedLogWindow_smooth (Ω : ℝ → ℂ) (hΩ : ContDiff ℝ ∞ Ω) (r s : ℕ) :
    ContDiff ℝ ∞ (mixedLogWindow Ω r s) := by
  unfold mixedLogWindow
  fun_prop

theorem mixedLogWindow_compact (Ω : ℝ → ℂ) (hΩc : HasCompactSupport Ω) (r s : ℕ) :
    HasCompactSupport (mixedLogWindow Ω r s) := hΩc.mul_left

theorem mixedLogWindow_support (Ω : ℝ → ℂ) (r s : ℕ) :
    tsupport (mixedLogWindow Ω r s) ⊆ tsupport Ω := tsupport_mul_subset_right

/-- Every fixed mixed derivative has one common weighted Fourier measure
with polynomial height growth.  Its constant is uniform in the moving
height, the real strip, and every row in which this profile is used. -/
theorem mixed_parameter_uniform_fourier_moment (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (r s J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ H →
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (compactExpTwist (mixedLogWindow Ω r s)
          (mixedLogWindow_compact Ω hΩc r s)
          (mixedLogWindow_smooth Ω hΩ r s) z)) t‖) ≤
          C * (1 + |z.im|) ^ (J + integrationPower) :=
  compact_exp_twist_uniform_fourier_moment _
    (mixedLogWindow_compact Ω hΩc r s) (mixedLogWindow_smooth Ω hΩ r s)
    H L hH hL ((mixedLogWindow_support Ω r s).trans hwindow) J

def scaledCompactExpTwist (Ω : ℝ → ℂ) (V : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω) (R : ℝ) (z : ℂ) :
    SchwartzMap ℝ ℂ :=
  (hΩc.mul_right.mul_right : HasCompactSupport
    (fun y : ℝ => Ω y * V (R * Real.exp y) * linearExp z y)).toSchwartzMap
      ((hΩ.mul ((V.smooth ⊤).comp (by fun_prop))).mul (linearExp_smooth z))

@[simp] theorem scaledCompactExpTwist_apply (Ω : ℝ → ℂ) (V : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω) (R : ℝ) (z : ℂ) (y : ℝ) :
    scaledCompactExpTwist Ω V hΩc hΩ R z y =
      Ω y * V (R * Real.exp y) * linearExp z y := rfl

/-- The actual two-scale inverse cutoff has no cost in its nonnegative
ratio R.  Only the imaginary norm-power parameter contributes a polynomial
height factor; this is uniform even when R tends to zero or infinity. -/
theorem scaled_compact_exp_twist_uniform_seminorm (Ω : ℝ → ℂ) (V : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ z : ℂ, |z.re| ≤ H →
      ∀ k j : ℕ, j ≤ K →
        SchwartzMap.seminorm ℝ k j (scaledCompactExpTwist Ω V hΩc hΩ R z) ≤
          L ^ k * C * (1 + |z.im|) ^ K := by
  obtain ⟨CΩ, hCΩ, hbΩ⟩ := hΩc.exists_bound_iteratedFDeriv hΩ K
  obtain ⟨CV, hCV, hbV⟩ := scaled_schwartz_derivatives V K
  let CE := (1 + H) ^ K * Real.exp (H * L)
  let CB := (2 : ℝ) ^ K * CΩ * CV
  have hCB : 0 ≤ CB := by dsimp [CB]; positivity
  refine ⟨(2 : ℝ) ^ K * CB * CE, by dsimp [CE]; positivity, ?_⟩
  intro R hR z hz k j hj
  let v : ℝ → ℂ := fun y => V (R * Real.exp y)
  have hv : ContDiff ℝ ∞ v := (V.smooth ⊤).comp (by fun_prop)
  have hbase (i : ℕ) (hi : i ≤ K) (y : ℝ) :
      ‖iteratedFDeriv ℝ i (fun y : ℝ => Ω y * v y) y‖ ≤ CB :=
    product_derivative_bound Ω v hΩ hv CΩ CV hCΩ hCV K i hi y
      (fun q hq => hbΩ q hq y) (fun q hq => hbV R hR q hq y)
  apply SchwartzMap.seminorm_le_bound ℝ k j _ (by dsimp [CE]; positivity)
  intro y
  change ‖y‖ ^ k * ‖iteratedFDeriv ℝ j
    (fun y : ℝ => Ω y * v y * linearExp z y) y‖ ≤ _
  by_cases hzero : ‖iteratedFDeriv ℝ j (fun y : ℝ => Ω y * v y * linearExp z y) y‖ = 0
  · rw [hzero, mul_zero]
    dsimp [CE]
    positivity
  have hs : y ∈ tsupport Ω := (tsupport_mul_subset_left.trans tsupport_mul_subset_left)
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hzero))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hs)
  have hb := product_derivative_bound (fun y : ℝ => Ω y * v y) (linearExp z)
    (hΩ.mul hv) (linearExp_smooth z) CB (CE * (1 + |z.im|) ^ K)
    hCB (by dsimp [CE]; positivity) K j hj y (fun q hq => hbase q hq y)
    (fun q hq => linearExp_window_derivative_le H L hH hL K q hq z hz y hy)
  calc
    _ ≤ L ^ k * ((2 : ℝ) ^ K * CB * (CE * (1 + |z.im|) ^ K)) :=
      mul_le_mul (by simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy k)
        hb (norm_nonneg _) (pow_nonneg hL k)
    _ = _ := by ring

end HeckeSkeleton.Moments.UniformAmplify
