import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileNormTwists

/-!
# Weighted common Fourier propagation for the actual compact profile

A frozen child profile can have arbitrarily large Fourier frequency.  Its
polynomial envelope is included in the one common Fourier kernel before
Minkowski is applied.  No uniform-in-frequency child profile bound or
additional row count is asserted.  The parent derivative order is the
finite order selected by the weighted Fourier theorem.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

open MeasureTheory
open _root_.ExpansionRecipe.LogProfile
open scoped Classical BigOperators ContDiff FourierTransform

/-- The child-frequency weight belongs to the same scalar kernel for all
rows and live labels.  Arithmetic row masks stay in the vector integrand. -/
def weightedProfileFourierKernel (f : SchwartzMap ℝ ℂ) (J : ℕ) (t : ℝ) : ℂ :=
  (((1 + ‖t‖) ^ J : ℝ) : ℂ) * (𝓕 f) t

@[simp] theorem weightedProfileFourierKernel_norm (f : SchwartzMap ℝ ℂ)
    (J : ℕ) (t : ℝ) :
    ‖weightedProfileFourierKernel f J t‖ = (1 + ‖t‖) ^ J * ‖(𝓕 f) t‖ := by
  simp only [weightedProfileFourierKernel, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + ‖t‖) ^ J)]

theorem weightedProfileFourierKernel_integrable (f : SchwartzMap ℝ ℂ) (J : ℕ) :
    Integrable (weightedProfileFourierKernel f J) := by
  apply (schwartz_one_plus_integrable (𝓕 f) J).mono'
  · unfold weightedProfileFourierKernel
    fun_prop
  · filter_upwards [] with t
    exact le_of_eq (weightedProfileFourierKernel_norm f J t)

/-- Exact scalar form of the common-measure inequality, with the full
frequency envelope paid once in its weighted L1 mass. -/
theorem shared_weighted_profile_fourier {ι : Type*} [Fintype ι]
    (f : SchwartzMap ℝ ℂ) (J : ℕ) (g : ℝ → ι → ℂ)
    (hg : ∀ i, Integrable (fun t : ℝ => g t i))
    {E C : ℝ} (hE : 0 ≤ E)
    (hpoint : ∀ t : ℝ, Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤
      ((1 + ‖t‖) ^ J * ‖(𝓕 f) t‖) * E)
    (hmass : (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 f) t‖) ≤ C) :
    Real.sqrt (∑ i, ‖∫ t : ℝ, g t i‖ ^ 2) ≤ E * C := by
  have hp : ∀ t : ℝ, Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤
      ‖weightedProfileFourierKernel f J t‖ * growthEnvelope E 0 0 0 1 0 := by
    intro t
    simpa only [weightedProfileFourierKernel_norm, growthEnvelope, Real.rpow_zero,
      mul_one] using hpoint t
  have hm : (∫ t : ℝ, ‖weightedProfileFourierKernel f J t‖) ≤
      growthEnvelope C 0 0 0 1 0 := by
    simpa only [weightedProfileFourierKernel_norm, growthEnvelope, Real.rpow_zero,
      mul_one] using hmass
  have h := shared_fourier_integral_envelope g hg (weightedProfileFourierKernel f J)
    (weightedProfileFourierKernel_integrable f J) hE (by norm_num : (1 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 0) hp hm
  simpa only [zero_add, growthEnvelope, Real.rpow_zero, mul_one] using h

/-- One genuine Fourier edge with the child envelope integrated over the
entire frequency line.  All constants and the parent's finite derivative
order precede the moving height, source parameters, and Hilbert vector. -/
theorem compact_profile_shared_fourier_envelope (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (R L M : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T → ∀ z : ℂ,
      |z.re| ≤ R → |z.im| ≤ M * (1 + T) →
      ∀ (ι : Type*) [Fintype ι] (g : ℝ → ι → ℂ),
      (∀ i, Integrable (fun t : ℝ => g t i)) →
      ∀ C₀ p B H Z : ℝ, 0 ≤ C₀ → 1 ≤ Z →
      (∀ t : ℝ, Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤
        ((1 + ‖t‖) ^ J * ‖(𝓕 (compactExpTwist Ω hΩc hΩ z)) t‖) *
          growthEnvelope C₀ p B H Z T) →
      Real.sqrt (∑ i, ‖∫ t : ℝ, g t i‖ ^ 2) ≤
        growthEnvelope (C₀ * C) p B (H + (J + integrationPower : ℕ)) Z T := by
  obtain ⟨C, hC, hb⟩ := compact_exp_twist_uniform_fourier_moment
    Ω hΩc hΩ R L hR hL hwindow J
  let n := J + integrationPower
  refine ⟨C * (1 + M) ^ n, by positivity, ?_⟩
  intro T hT z hz him ι _ g hg C₀ p B H Z hC₀ hZ hpoint
  have hm : (∫ t : ℝ, (1 + ‖t‖) ^ J *
      ‖(𝓕 (compactExpTwist Ω hΩc hΩ z)) t‖) ≤
      (C * (1 + M) ^ n) * (1 + T) ^ (n : ℝ) := by
    exact (hb z hz).trans ((mul_le_mul_of_nonneg_left
      (polynomial_twist_height hM hT him n) hC).trans_eq (by ring))
  have h := shared_weighted_profile_fourier (compactExpTwist Ω hΩc hΩ z) J g hg
    (growthEnvelope_nonneg hC₀ hZ hT) hpoint hm
  have ht : 0 < 1 + T := by linarith
  calc
    _ ≤ growthEnvelope C₀ p B H Z T *
        ((C * (1 + M) ^ n) * (1 + T) ^ (n : ℝ)) := h
    _ = growthEnvelope (C₀ * (C * (1 + M) ^ n)) p B
        (H + (J + integrationPower : ℕ)) Z T := by
      simp only [growthEnvelope, Real.rpow_add ht]
      dsimp only [n]
      ring


/-- The independent-scale inverse cutoff uses the same weighted common
kernel argument, with no cost in its arbitrary nonnegative ratio. -/
theorem scaled_profile_shared_fourier_envelope (Ω : ℝ → ℂ) (V : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (R L M : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ratio : ℝ, 0 ≤ ratio → ∀ T : ℝ, 0 ≤ T → ∀ z : ℂ,
      |z.re| ≤ R → |z.im| ≤ M * (1 + T) →
      ∀ (ι : Type*) [Fintype ι] (g : ℝ → ι → ℂ),
      (∀ i, Integrable (fun t : ℝ => g t i)) →
      ∀ C₀ p B H Z : ℝ, 0 ≤ C₀ → 1 ≤ Z →
      (∀ t : ℝ, Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤
        ((1 + ‖t‖) ^ J * ‖(𝓕 (scaledCompactExpTwist Ω V hΩc hΩ ratio z)) t‖) *
          growthEnvelope C₀ p B H Z T) →
      Real.sqrt (∑ i, ‖∫ t : ℝ, g t i‖ ^ 2) ≤
        growthEnvelope (C₀ * C) p B (H + (J + integrationPower : ℕ)) Z T := by
  obtain ⟨C, hC, hb⟩ := scaled_compact_exp_twist_uniform_fourier_moment
    Ω V hΩc hΩ R L hR hL hwindow J
  let n := J + integrationPower
  refine ⟨C * (1 + M) ^ n, by positivity, ?_⟩
  intro ratio hratio T hT z hz him ι _ g hg C₀ p B H Z hC₀ hZ hpoint
  have hm : (∫ t : ℝ, (1 + ‖t‖) ^ J *
      ‖(𝓕 (scaledCompactExpTwist Ω V hΩc hΩ ratio z)) t‖) ≤
      (C * (1 + M) ^ n) * (1 + T) ^ (n : ℝ) := by
    exact (hb ratio hratio z hz).trans ((mul_le_mul_of_nonneg_left
      (polynomial_twist_height hM hT him n) hC).trans_eq (by ring))
  have h := shared_weighted_profile_fourier (scaledCompactExpTwist Ω V hΩc hΩ ratio z) J g hg
    (growthEnvelope_nonneg hC₀ hZ hT) hpoint hm
  have ht : 0 < 1 + T := by linarith
  calc
    _ ≤ growthEnvelope C₀ p B H Z T *
        ((C * (1 + M) ^ n) * (1 + T) ^ (n : ℝ)) := h
    _ = growthEnvelope (C₀ * (C * (1 + M) ^ n)) p B
        (H + (J + integrationPower : ℕ)) Z T := by
      simp only [growthEnvelope, Real.rpow_add ht]
      dsimp only [n]
      ring

end HeckeSkeleton.Moments.UniformAmplify
