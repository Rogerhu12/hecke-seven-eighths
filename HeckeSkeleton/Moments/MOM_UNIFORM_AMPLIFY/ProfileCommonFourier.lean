import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileNormTwists
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# One pointwise Fourier majorant for all rowwise profile parameters

The real and imaginary twists can vary independently from row to row.
Uniform bounds for their separate integrals do not furnish a common
Minkowski measure.  Here finite physical derivative bounds give a single
pointwise tail for every ratio and every twist in the height box.  Its
weighted integral is finite before any rows or parameters are selected.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open MeasureTheory
open _root_.ExpansionRecipe.LogProfile
open scoped Classical BigOperators ContDiff FourierTransform SchwartzMap

def profileFourierTail (N : ℕ) (t : ℝ) : ℝ := (1 + ‖t‖) ^ (-(N : ℝ))

theorem profileFourierTail_nonneg (N : ℕ) (t : ℝ) : 0 ≤ profileFourierTail N t := by
  unfold profileFourierTail
  positivity

theorem profileFourierTail_integrable (N : ℕ) (hN : 1 < N) :
    Integrable (profileFourierTail N) := by
  unfold profileFourierTail
  apply integrable_one_add_norm
  simpa using (show (1 : ℝ) < (N : ℝ) by exact_mod_cast hN)

theorem profileFourierTail_weighted (J : ℕ) (t : ℝ) :
    (1 + ‖t‖) ^ J * profileFourierTail (J + 2) t = profileFourierTail 2 t := by
  unfold profileFourierTail
  rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
  congr 1
  push_cast
  ring

/-- Genuine pointwise Fourier decay, simultaneous in the independent
cutoff ratio and the entire rowwise norm-power box. -/
theorem scaled_common_profile_fourier_decay (Ω : ℝ → ℂ) (V : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L M : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T → ∀ R : ℝ, 0 ≤ R →
      ∀ z : ℂ, |z.re| ≤ H → |z.im| ≤ M * (1 + T) → ∀ t : ℝ,
        ‖(𝓕 (scaledCompactExpTwist Ω V hΩc hΩ R z)) t‖ ≤
          C * (1 + T) ^ (N : ℝ) * profileFourierTail N t := by
  obtain ⟨C, hC, hb⟩ := scaled_compact_exp_twist_uniform_seminorm Ω V hΩc hΩ
    H L hH hL hwindow N
  let C₁ := (1 + L ^ integrationPower) * C
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  let C₂ := (2 : ℝ) ^ N * (fourierSeminormConstant 0 C₁ + fourierSeminormConstant N C₁)
  have hC₂ : 0 ≤ C₂ := mul_nonneg (by positivity)
    (add_nonneg (fourierSeminormConstant_nonneg 0 C₁ hC₁)
      (fourierSeminormConstant_nonneg N C₁ hC₁))
  refine ⟨C₂ * (1 + M) ^ N, by positivity, ?_⟩
  intro T hT R hR z hz him t
  let f := scaledCompactExpTwist Ω V hΩc hΩ R z
  have hseminorm (j : ℕ) (hj : j ≤ N) :
      SchwartzMap.seminorm ℝ 0 j f + SchwartzMap.seminorm ℝ integrationPower j f ≤
        C₁ * (1 + |z.im|) ^ N := by
    have h0 := hb R hR z hz 0 j hj
    have hp := hb R hR z hz integrationPower j hj
    simp only [pow_zero, one_mul] at h0
    dsimp [C₁]
    nlinarith
  have h0 : ‖(𝓕 f) t‖ ≤ fourierSeminormConstant 0 (C₁ * (1 + |z.im|) ^ N) := by
    have he := SchwartzMap.le_seminorm ℝ 0 0 (𝓕 f) t
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at he
    exact he.trans (fourier_seminorm_le f 0 _ (by positivity)
      (fun j hj => hseminorm j (hj.trans (Nat.zero_le N))))
  have hN : ‖t‖ ^ N * ‖(𝓕 f) t‖ ≤
      fourierSeminormConstant N (C₁ * (1 + |z.im|) ^ N) := by
    have he := SchwartzMap.le_seminorm ℝ N 0 (𝓕 f) t
    simp only [norm_iteratedFDeriv_zero] at he
    exact he.trans (fourier_seminorm_le f N _ (by positivity) hseminorm)
  have htail := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := N)
    (norm_nonneg t) (norm_nonneg ((𝓕 f) t)) h0 (by simpa only [zero_add] using hN)
  simp only [pow_zero, one_mul] at htail
  have hraw : ‖(𝓕 f) t‖ ≤ C₂ * (1 + |z.im|) ^ N * profileFourierTail N t := by
    apply htail.trans_eq
    unfold C₂ profileFourierTail fourierSeminormConstant
    ring
  calc
    _ ≤ C₂ * (1 + |z.im|) ^ N * profileFourierTail N t := hraw
    _ ≤ C₂ * ((1 + M) ^ N * (1 + T) ^ (N : ℝ)) * profileFourierTail N t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (polynomial_twist_height hM hT him N) hC₂)
        (profileFourierTail_nonneg N t)
    _ = _ := by ring

/-- The one scalar majorant is selected before every ratio, row and
rowwise twist.  The parent's derivative order is the explicit finite
order J+2, which pays the child-frequency weight and an integrable tail. -/
theorem scaled_common_profile_fourier_majorant (Ω : ℝ → ℂ) (V : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L M : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T → ∃ W : ℝ → ℝ,
      (∀ t : ℝ, 0 ≤ W t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * W t) ∧
      (∫ t : ℝ, (1 + ‖t‖) ^ J * W t) ≤ C * (1 + T) ^ (J + 2 : ℕ) ∧
      ∀ R : ℝ, 0 ≤ R → ∀ z : ℂ, |z.re| ≤ H → |z.im| ≤ M * (1 + T) →
        ∀ t : ℝ, ‖(𝓕 (scaledCompactExpTwist Ω V hΩc hΩ R z)) t‖ ≤ W t := by
  obtain ⟨C, hC, hb⟩ := scaled_common_profile_fourier_decay Ω V hΩc hΩ
    H L M hH hL hM hwindow (J + 2)
  let mass := ∫ t : ℝ, profileFourierTail 2 t
  have hmass : 0 ≤ mass := integral_nonneg (profileFourierTail_nonneg 2)
  refine ⟨C * mass, mul_nonneg hC hmass, ?_⟩
  intro T hT
  let W : ℝ → ℝ := fun t => (C * (1 + T) ^ (J + 2 : ℕ)) * profileFourierTail (J + 2) t
  have he : (fun t : ℝ => (1 + ‖t‖) ^ J * W t) =
      fun t => (C * (1 + T) ^ (J + 2 : ℕ)) * profileFourierTail 2 t := by
    funext t
    dsimp [W]
    rw [← mul_assoc, mul_comm ((1 + ‖t‖) ^ J), mul_assoc, profileFourierTail_weighted]
  refine ⟨W, fun t => mul_nonneg (by positivity) (profileFourierTail_nonneg _ _), ?_, ?_, ?_⟩
  · rw [he]
    exact (profileFourierTail_integrable 2 (by norm_num)).const_mul _
  · rw [he, integral_const_mul]
    exact le_of_eq (by dsimp [mass]; ring)
  · intro R hR z hz him t
    simpa only [Real.rpow_natCast] using hb T hT R hR z hz him t

theorem norm_component_le_finite_l2 {ι : Type*} [Fintype ι] (g : ι → ℂ) (i : ι) :
    ‖g i‖ ≤ Real.sqrt (∑ j, ‖g j‖ ^ 2) :=
  Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))

theorem finite_l2_mul_common_bound {ι : Type*} [Fintype ι]
    (f g : ι → ℂ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ i, ‖f i‖ ≤ B) :
    Real.sqrt (∑ i, ‖f i * g i‖ ^ 2) ≤ B * Real.sqrt (∑ i, ‖g i‖ ^ 2) := by
  have hs : (∑ i, ‖f i * g i‖ ^ 2) ≤ B ^ 2 * ∑ i, ‖g i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf i) 2) (sq_nonneg _)
  exact (Real.sqrt_le_sqrt hs).trans_eq (by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB])

/-- A real nonnegative kernel version of the shared Hilbert integral.
The kernel is common to all components and its mass is paid once. -/
theorem shared_nonnegative_kernel_l2 {ι : Type*} [Fintype ι]
    (g : ℝ → ι → ℂ) (hg : ∀ i, Integrable (fun t : ℝ => g t i))
    (W : ℝ → ℝ) (hW : Integrable W) (hW0 : ∀ t, 0 ≤ W t)
    (E : ℝ) (hE : 0 ≤ E)
    (hpoint : ∀ t : ℝ, Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤ W t * E) :
    Real.sqrt (∑ i, ‖∫ t : ℝ, g t i‖ ^ 2) ≤ E * ∫ t : ℝ, W t := by
  let K : ℝ → ℂ := fun t => (W t : ℂ)
  have hnorm (t : ℝ) : ‖K t‖ = W t := by
    simp only [K, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 t)]
  have hp : ∀ t : ℝ, Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤
      ‖K t‖ * growthEnvelope E 0 0 0 1 0 := by
    intro t
    simpa only [hnorm, growthEnvelope, Real.rpow_zero, mul_one] using hpoint t
  have hm : (∫ t : ℝ, ‖K t‖) ≤ growthEnvelope (∫ t : ℝ, W t) 0 0 0 1 0 := by
    simp only [hnorm, growthEnvelope, Real.rpow_zero, mul_one, le_refl]
  have h := shared_fourier_integral_envelope g hg K hW.ofReal hE
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0) hp hm
  simpa only [growthEnvelope, zero_add, Real.rpow_zero, mul_one] using h

/-- Rowwise Fourier kernels may differ arbitrarily, but are all dominated
by W pointwise.  Arithmetic masks and live labels remain in the child
vector.  Integrability of every product is derived from the same majorant,
and no cardinality factor is introduced. -/
theorem common_profile_fourier_minkowski {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (W : ℝ → ℝ) (hW0 : ∀ t, 0 ≤ W t) (J : ℕ)
    (hW : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * W t))
    (hf : ∀ i t, ‖(𝓕 (f i)) t‖ ≤ W t)
    (child : ℝ → ι → ℂ) (hc : ∀ i, AEStronglyMeasurable (fun t : ℝ => child t i))
    (E : ℝ) (hE : 0 ≤ E)
    (hchild : ∀ t : ℝ, Real.sqrt (∑ i, ‖child t i‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) :
    Real.sqrt (∑ i, ‖∫ t : ℝ, (𝓕 (f i)) t * child t i‖ ^ 2) ≤
      E * ∫ t : ℝ, (1 + ‖t‖) ^ J * W t := by
  let g : ℝ → ι → ℂ := fun t i => (𝓕 (f i)) t * child t i
  have hpoint (t : ℝ) : Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤
      ((1 + ‖t‖) ^ J * W t) * E := by
    calc
      _ ≤ W t * Real.sqrt (∑ i, ‖child t i‖ ^ 2) :=
        finite_l2_mul_common_bound (fun i => (𝓕 (f i)) t) (child t) (W t) (hW0 t)
          (fun i => hf i t)
      _ ≤ W t * (E * (1 + ‖t‖) ^ J) := mul_le_mul_of_nonneg_left (hchild t) (hW0 t)
      _ = _ := by ring
  have hg (i : ι) : Integrable (fun t : ℝ => g t i) := by
    apply (hW.mul_const E).mono'
      ((𝓕 (f i)).continuous.aestronglyMeasurable.mul (hc i))
    filter_upwards [] with t
    exact (norm_component_le_finite_l2 (g t) i).trans (hpoint t)
  exact shared_nonnegative_kernel_l2 g hg (fun t => (1 + ‖t‖) ^ J * W t) hW
    (fun t => mul_nonneg (by positivity) (hW0 t)) E hE hpoint

/-- The common majorant and Minkowski bound for arbitrary rowwise ratios
and twists of the genuine scaled profile.  The constant precedes the
finite row type, every row parameter and the entire child vector. -/
theorem scaled_rowwise_fourier_envelope (Ω : ℝ → ℂ) (V : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L M : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ (ι : Type*) [Fintype ι] (R : ι → ℝ) (z : ι → ℂ),
      (∀ i, 0 ≤ R i) → (∀ i, |(z i).re| ≤ H) → (∀ i, |(z i).im| ≤ M * (1 + T)) →
      ∀ child : ℝ → ι → ℂ, (∀ i, AEStronglyMeasurable (fun t : ℝ => child t i)) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, Real.sqrt (∑ i, ‖child t i‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) →
      Real.sqrt (∑ i, ‖∫ t : ℝ,
        (𝓕 (scaledCompactExpTwist Ω V hΩc hΩ (R i) (z i))) t * child t i‖ ^ 2) ≤
          C * (1 + T) ^ (J + 2 : ℕ) * E := by
  obtain ⟨C, hC, hb⟩ := scaled_common_profile_fourier_majorant Ω V hΩc hΩ
    H L M hH hL hM hwindow J
  refine ⟨C, hC, ?_⟩
  intro T hT ι _ R z hR hz him child hc E hE hchild
  obtain ⟨W, hW0, hWi, hWmass, hWbound⟩ := hb T hT
  have h := common_profile_fourier_minkowski
    (fun i => scaledCompactExpTwist Ω V hΩc hΩ (R i) (z i)) W hW0 J hWi
    (fun i t => hWbound (R i) (hR i) (z i) (hz i) (him i) t) child hc E hE hchild
  exact h.trans ((mul_le_mul_of_nonneg_left hWmass hE).trans_eq (by ring))

end HeckeSkeleton.Moments.UniformAmplify
