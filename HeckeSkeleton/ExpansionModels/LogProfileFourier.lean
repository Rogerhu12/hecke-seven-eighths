import HeckeSkeleton.ExpansionModels.LogProfileUniform

/-!
# Uniform Fourier moments for the actual coupled detector profile

This file fills the missing Fourier bridge using Mathlib's Fourier transform
and its normalization.  Every constant is independent of the nonnegative
physical parameters A, B, D.  No Fourier decay assumption is supplied by the
caller: it is proved from the smooth compact window and Schwartz cutoffs.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe.LogProfile

open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap

def integrationPower : ℕ := (volume : Measure ℝ).integrablePower

def integrationConstant : ℝ :=
  2 ^ integrationPower *
    ∫ x : ℝ, (1 + ‖x‖) ^ (-(integrationPower : ℝ))

lemma integrationConstant_nonneg : 0 ≤ integrationConstant := by
  unfold integrationConstant
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun x => Real.rpow_nonneg (by positivity) _)

def fourierSeminormConstant (n : ℕ) (C : ℝ) : ℝ :=
  2 ^ n * ((n + 1 : ℕ) : ℝ) * integrationConstant * C

lemma fourierSeminormConstant_nonneg (n : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ fourierSeminormConstant n C := by
  dsimp [fourierSeminormConstant]
  exact mul_nonneg (mul_nonneg (by positivity) integrationConstant_nonneg) hC

lemma integral_derivative_le (g : SchwartzMap ℝ ℂ) (j : ℕ) (C : ℝ)
    (h : SchwartzMap.seminorm ℝ 0 j g +
      SchwartzMap.seminorm ℝ integrationPower j g ≤ C) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ j g x‖) ≤ integrationConstant * C := by
  have hi := g.integral_pow_mul_iteratedFDeriv_le ℝ volume 0 j
  simp only [pow_zero, one_mul, zero_add] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left h integrationConstant_nonneg)

/-- A quantitative Fourier seminorm bound using only physical derivatives.
The required spatial decay is the fixed temperate-measure power. -/
theorem fourier_seminorm_le (g : SchwartzMap ℝ ℂ) (m : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hb : ∀ j ≤ m, SchwartzMap.seminorm ℝ 0 j g +
      SchwartzMap.seminorm ℝ integrationPower j g ≤ C) :
    SchwartzMap.seminorm ℝ m 0 (𝓕 g) ≤ fourierSeminormConstant m C := by
  apply SchwartzMap.seminorm_le_bound ℝ m 0 _
    (fourierSeminormConstant_nonneg m C hC)
  intro x
  have hF := Real.pow_mul_norm_iteratedFDeriv_fourier_le (g.smooth ⊤)
    (fun k n _hk _hn => g.integrable_pow_mul_iteratedFDeriv volume k n)
    (k := 0) (n := m) le_top le_top x
  simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
    Finset.range_one, Finset.sum_product, Finset.sum_singleton] at hF
  change ‖x‖ ^ m * ‖iteratedFDeriv ℝ 0 (𝓕 (g : ℝ → ℂ)) x‖ ≤ _
  apply hF.trans
  calc
    _ ≤ (2 : ℝ) ^ m *
        ∑ j ∈ Finset.range (m + 1), integrationConstant * C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      simpa only [pow_zero, one_mul] using
        integral_derivative_le g j C (hb j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = fourierSeminormConstant m C := by
      simp [fourierSeminormConstant, mul_assoc]

def fourierMomentConstant (J : ℕ) (C : ℝ) : ℝ :=
  integrationConstant *
    (fourierSeminormConstant 0 C + fourierSeminormConstant (J + integrationPower) C)

lemma fourierMomentConstant_nonneg (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ fourierMomentConstant J C := by
  exact mul_nonneg integrationConstant_nonneg
    (add_nonneg (fourierSeminormConstant_nonneg 0 C hC)
      (fourierSeminormConstant_nonneg (J + integrationPower) C hC))

theorem fourier_pow_moment_le (g : SchwartzMap ℝ ℂ) (J : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hb : ∀ j ≤ J + integrationPower, SchwartzMap.seminorm ℝ 0 j g +
      SchwartzMap.seminorm ℝ integrationPower j g ≤ C) :
    (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤ fourierMomentConstant J C := by
  have hi := (𝓕 g).integral_pow_mul_iteratedFDeriv_le ℝ volume J 0
  simp only [norm_iteratedFDeriv_zero] at hi
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ integrationConstant_nonneg
  exact add_le_add
    (fourier_seminorm_le g 0 C hC (fun j hj => hb j (hj.trans (Nat.zero_le _))))
    (fourier_seminorm_le g (J + integrationPower) C hC hb)

lemma one_add_norm_pow_le (t : ℝ) (J : ℕ) :
    (1 + ‖t‖) ^ J ≤ (2 : ℝ) ^ J * (1 + ‖t‖ ^ J) := by
  apply (add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg t) J).trans
  simp only [one_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)) (by positivity)

theorem schwartz_one_plus_integrable (g : SchwartzMap ℝ ℂ) (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖g t‖) := by
  have hi : Integrable (fun t : ℝ =>
      (2 : ℝ) ^ J * (‖g t‖ + ‖t‖ ^ J * ‖g t‖)) :=
    (g.integrable.norm.add (g.integrable_pow_mul volume J)).const_mul _
  apply hi.mono' (by fun_prop)
  filter_upwards [] with t
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((2 : ℝ) ^ J * (1 + ‖t‖ ^ J)) * ‖g t‖ :=
      mul_le_mul_of_nonneg_right (one_add_norm_pow_le t J) (norm_nonneg _)
    _ = _ := by ring

theorem uniform_fourier_one_plus_moment (g : SchwartzMap ℝ ℂ) (J : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hb : ∀ j ≤ J + integrationPower, SchwartzMap.seminorm ℝ 0 j g +
      SchwartzMap.seminorm ℝ integrationPower j g ≤ C) :
    (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      (2 : ℝ) ^ J * (fourierMomentConstant 0 C + fourierMomentConstant J C) := by
  have h0 := fourier_pow_moment_le g 0 C hC (fun j hj => hb j (by omega))
  simp only [pow_zero, one_mul] at h0
  have hJ := fourier_pow_moment_le g J C hC hb
  calc
    _ ≤ ∫ t : ℝ, (2 : ℝ) ^ J *
        (‖(𝓕 g) t‖ + ‖t‖ ^ J * ‖(𝓕 g) t‖) := by
      apply integral_mono (schwartz_one_plus_integrable (𝓕 g) J)
        (((𝓕 g).integrable.norm.add ((𝓕 g).integrable_pow_mul volume J)).const_mul _)
      intro t
      calc
        _ ≤ ((2 : ℝ) ^ J * (1 + ‖t‖ ^ J)) * ‖(𝓕 g) t‖ :=
          mul_le_mul_of_nonneg_right (one_add_norm_pow_le t J) (norm_nonneg _)
        _ = _ := by ring
    _ = (2 : ℝ) ^ J * ((∫ t : ℝ, ‖(𝓕 g) t‖) +
        ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) := by
      rw [integral_const_mul, integral_add (𝓕 g).integrable.norm
        ((𝓕 g).integrable_pow_mul volume J)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h0 hJ) (by positivity)

/-- The genuine uniformly bounded Fourier moment of the coupled source
Ω(y) (1-V(Aeʸ)) exp(-Beʸ) T(Deʸ). -/
theorem uniform_fourier_moment (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := logSource_uniform_seminorm Ω V T hΩc hΩ L hL hwindow
    (J + integrationPower)
  let C' := (1 + L ^ integrationPower) * C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ) ^ J * (fourierMomentConstant 0 C' + fourierMomentConstant J C'),
    mul_nonneg (by positivity) (add_nonneg (fourierMomentConstant_nonneg 0 C' hC')
      (fourierMomentConstant_nonneg J C' hC')), ?_⟩
  intro A B D hA hB hD
  apply uniform_fourier_one_plus_moment _ J C' hC'
  intro i hi
  have h0 := hb A B D hA hB hD 0 i hi
  have hp := hb A B D hA hB hD integrationPower i hi
  simp only [pow_zero, one_mul] at h0
  dsimp only [C']
  linarith

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R ^ N * (∫ t : ℝ in {t | R < ‖t‖}, (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1 + ‖t‖) ^ (J + N) * ‖(𝓕 g) t‖ := by
  have hiJ := schwartz_one_plus_integrable (𝓕 g) J
  have hiN := schwartz_one_plus_integrable (𝓕 g) (J + N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R ^ N ≤ (1 + ‖t‖) ^ N :=
    pow_le_pow_left₀ hR.le (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1 + ‖t‖) ^ N * ((1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem uniform_fourier_tail (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ R : ℝ, 0 < R →
      (∫ t : ℝ in {t | R < ‖t‖}, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤
          C / R ^ N := by
  obtain ⟨C, hC, hb⟩ := uniform_fourier_moment Ω V T hΩc hΩ L hL hwindow (J + N)
  refine ⟨C, hC, ?_⟩
  intro A B D hA hB hD R hR
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa [mul_comm] using (schwartz_weighted_tail
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J N R hR).trans
      (hb A B D hA hB hD)

end ExpansionRecipe.LogProfile

#print axioms ExpansionRecipe.LogProfile.fourier_seminorm_le
#print axioms ExpansionRecipe.LogProfile.uniform_fourier_moment
#print axioms ExpansionRecipe.LogProfile.uniform_fourier_tail
