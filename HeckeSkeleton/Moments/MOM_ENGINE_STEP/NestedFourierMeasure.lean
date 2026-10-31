import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFamilyIntegrability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# One positive measure for the two actual Fourier transforms

The second original Schwartz kernel is fixed before the first Fourier
variable.  Both actual kernels therefore define a product of their
positive Fourier measures.  Its density and mass are computed from the
two original Fourier transforms.  No mass or energy integrability bound
is an input.

Actual children may depend on both Fourier variables.  Their finite raw
atom controls on the product space prove polynomial energy growth, and
the two genuine Schwartz decays prove integrability.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap NumberField

namespace HeckeSkeleton.Moments.EngineStep

open MeasureTheory NumberField IsDedekindDomain
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Both original Fourier measures are chosen before any child family. -/
def nestedFourierMeasure (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) : Measure (V × E) :=
  (actualFourierMeasure F₁).prod (actualFourierMeasure F₂)

theorem nestedFourierMeasure_finite (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    IsFiniteMeasure (nestedFourierMeasure F₁ F₂) := by
  letI := actualFourierMeasure_finite F₁
  letI := actualFourierMeasure_finite F₂
  dsimp only [nestedFourierMeasure]
  infer_instance

/-- The product is exactly the density of the two actual Fourier
transforms with respect to the original product Haar measure. -/
theorem nestedFourierMeasure_density (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    nestedFourierMeasure F₁ F₂ =
      ((volume : Measure V).prod (volume : Measure E)).withDensity
        (fun z : V × E => ENNReal.ofReal (‖(𝓕 F₁) z.1‖ * ‖(𝓕 F₂) z.2‖)) := by
  change ((volume : Measure V).withDensity (fun ξ => ENNReal.ofReal ‖(𝓕 F₁) ξ‖)).prod
      ((volume : Measure E).withDensity (fun η => ENNReal.ofReal ‖(𝓕 F₂) η‖)) = _
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  exact (ENNReal.ofReal_mul (norm_nonneg ((𝓕 F₁) z.1))).symm

theorem nestedFourierMeasure_mass_eq (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    (nestedFourierMeasure F₁ F₂).real Set.univ =
      (∫ ξ : V, ‖(𝓕 F₁) ξ‖) * (∫ η : E, ‖(𝓕 F₂) η‖) := by
  letI := actualFourierMeasure_finite F₁
  letI := actualFourierMeasure_finite F₂
  calc
    _ = (actualFourierMeasure F₁).real Set.univ *
        (actualFourierMeasure F₂).real Set.univ := by
      simpa only [nestedFourierMeasure, Set.univ_prod_univ] using
        (measureReal_prod_prod (μ := actualFourierMeasure F₁)
          (ν := actualFourierMeasure F₂) Set.univ Set.univ)
    _ = _ := by rw [actualFourierMeasure_mass_eq, actualFourierMeasure_mass_eq]

/-- All seminorms and the constant precede both kernels and all child
parameters.  The exact two Fourier masses are paid once each. -/
theorem nestedFourierMeasure_uniform_mass :
    ∃ s₁ s₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)),
        (nestedFourierMeasure F₁ F₂).real Set.univ ≤
          C * s₁.sup (schwartzSeminormFamily ℝ V ℂ) F₁ *
            s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := actualFourierMeasure_uniform_mass (V := V)
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := actualFourierMeasure_uniform_mass (V := E)
  refine ⟨s₁, s₂, C₁ * C₂, mul_pos hC₁ hC₂, fun F₁ F₂ => ?_⟩
  have hmass : (nestedFourierMeasure F₁ F₂).real Set.univ =
      (actualFourierMeasure F₁).real Set.univ *
        (actualFourierMeasure F₂).real Set.univ := by
    rw [nestedFourierMeasure_mass_eq, actualFourierMeasure_mass_eq,
      actualFourierMeasure_mass_eq]
  rw [hmass]
  exact (mul_le_mul (h₁ F₁) (h₂ F₂) (by positivity)
    (mul_nonneg hC₁.le (apply_nonneg _ F₁))).trans_eq (by ring)

/-- A scalar branch weight is outside both Fourier variables. -/
theorem nestedFourierMeasure_scaled_integral (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (W : ℝ) (hW : 0 ≤ W) (G : V × E → ℝ) :
    (∫ z, G z ∂ENNReal.ofReal W • nestedFourierMeasure F₁ F₂) =
      W * ∫ z, G z ∂nestedFourierMeasure F₁ F₂ := by
  rw [integral_smul_measure, ENNReal.toReal_ofReal hW, smul_eq_mul]

theorem actualFourierMeasure_polynomial_integrable (F : 𝓢(V, ℂ)) (J : ℕ) :
    Integrable (fun ξ : V => (1 + ‖ξ‖) ^ J) (actualFourierMeasure F) := by
  obtain ⟨s, C, hC, hweight⟩ := joint_fourier_mass_bound (V := V) J
  have hm : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using (hweight F).1

theorem one_add_prod_norm_le (z : V × E) :
    1 + ‖z‖ ≤ (1 + ‖z.1‖) * (1 + ‖z.2‖) := by
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h
  · rw [Prod.norm_def, max_eq_right h]
    nlinarith [norm_nonneg z.1, norm_nonneg z.2,
      mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2)]
  · rw [Prod.norm_def, max_eq_left h]
    nlinarith [norm_nonneg z.1, norm_nonneg z.2,
      mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2)]

theorem nestedFourierMeasure_polynomial_integrable
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (J : ℕ) :
    Integrable (fun z : V × E => (1 + ‖z‖) ^ J) (nestedFourierMeasure F₁ F₂) := by
  letI := actualFourierMeasure_finite F₁
  letI := actualFourierMeasure_finite F₂
  have hmajor := (actualFourierMeasure_polynomial_integrable F₁ J).mul_prod
    (actualFourierMeasure_polynomial_integrable F₂ J)
  apply hmajor.mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun z : V × E => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) _)]
    exact (pow_le_pow_left₀ (by positivity) (one_add_prod_norm_le z) J).trans_eq
      (mul_pow _ _ _)

/-- Fubini for the genuine positive kernels.  The actual child theorem
below supplies its integrability from raw atom information. -/
theorem nestedFourierMeasure_integral_iterated
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (G : V × E → ℝ)
    (hG : Integrable G (nestedFourierMeasure F₁ F₂)) :
    (∫ z, G z ∂nestedFourierMeasure F₁ F₂) =
      ∫ ξ, ∫ η, G (ξ, η) ∂actualFourierMeasure F₂ ∂actualFourierMeasure F₁ := by
  letI := actualFourierMeasure_finite F₁
  letI := actualFourierMeasure_finite F₂
  exact integral_prod G hG

theorem nestedFourierMeasure_integral_density
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (G : V × E → ℝ) :
    (∫ z, G z ∂nestedFourierMeasure F₁ F₂) =
      ∫ z : V × E, (‖(𝓕 F₁) z.1‖ * ‖(𝓕 F₂) z.2‖) * G z := by
  rw [nestedFourierMeasure_density]
  have hm : Measurable (fun z : V × E =>
      ENNReal.ofReal (‖(𝓕 F₁) z.1‖ * ‖(𝓕 F₂) z.2‖)) := by fun_prop
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    smul_eq_mul] using integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall (fun z : V × E => ENNReal.ofReal_lt_top)) G

section ActualChildren

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

theorem actual_nested_paired_family_integrable
    {D : V × E → MomentData K ω ψ} {n : ℕ}
    {hcount : ∀ z, (D z).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V × E → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    Integrable (fun z => pairedEnergy (D z) a Z (t z)) (nestedFourierMeasure F₁ F₂) := by
  have hac : nestedFourierMeasure F₁ F₂ ≪ (volume : Measure (V × E)) := by
    rw [nestedFourierMeasure_density]
    exact withDensity_absolutelyContinuous _ _
  have hmeas := AEStronglyMeasurable.mono_ac hac cal.energy_aestronglyMeasurable
  have hmajor := (nestedFourierMeasure_polynomial_integrable F₁ F₂ cal.energyOrder).const_mul
    cal.energyConstant
  apply hmajor.mono' hmeas
  exact Filter.Eventually.of_forall fun z => by
    have hE : 0 ≤ pairedEnergy (D z) a Z (t z) :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hE]
    exact cal.energy_polynomial_bound z

theorem actual_nested_normalized_family_integrable
    {D : V × E → MomentData K ω ψ} {n : ℕ}
    {hcount : ∀ z, (D z).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V × E → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    Integrable (fun z => normalizedPairedEnergy (D z) a Z (t z))
      (nestedFourierMeasure F₁ F₂) :=
  (actual_nested_paired_family_integrable cal F₁ F₂).div_const (Z ^ (a.m + a.q))

/-- The actual child energy, with both Fourier variables retained, is
one integral over the positive branch space and the original iterated
integral.  Neither integrability nor an energy bound is a premise. -/
theorem actual_nested_normalized_family_integral
    {D : V × E → MomentData K ω ψ} {n : ℕ}
    {hcount : ∀ z, (D z).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V × E → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    (∫ z, normalizedPairedEnergy (D z) a Z (t z) ∂nestedFourierMeasure F₁ F₂) =
      ∫ ξ, ∫ η, normalizedPairedEnergy (D (ξ, η)) a Z (t (ξ, η))
        ∂actualFourierMeasure F₂ ∂actualFourierMeasure F₁ :=
  nestedFourierMeasure_integral_iterated F₁ F₂ _
    (actual_nested_normalized_family_integrable cal F₁ F₂)

theorem actual_nested_normalized_scaled_integrable
    {D : V × E → MomentData K ω ψ} {n : ℕ}
    {hcount : ∀ z, (D z).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V × E → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (W : ℝ) :
    Integrable (fun z => normalizedPairedEnergy (D z) a Z (t z))
      (ENNReal.ofReal W • nestedFourierMeasure F₁ F₂) :=
  (actual_nested_normalized_family_integrable cal F₁ F₂).smul_measure ENNReal.ofReal_ne_top

theorem actual_nested_normalized_cauchy_integrable
    {D₁ D₂ : V × E → MomentData K ω ψ} {n₁ n₂ : ℕ}
    {hc₁ : ∀ z, (D₁ z).geometry.slotCount = n₁}
    {hc₂ : ∀ z, (D₂ z).geometry.slotCount = n₂}
    {a₁ a₂ : RealParameters} {Z : ℝ} (hZ : 0 < Z) {t₁ t₂ : V × E → ℝ}
    (cal₁ : ActualFiniteFamilyControl D₁ n₁ hc₁ a₁ Z t₁)
    (cal₂ : ActualFiniteFamilyControl D₂ n₂ hc₂ a₂ Z t₂)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    Integrable (fun z =>
      Real.sqrt (normalizedPairedEnergy (D₁ z) a₁ Z (t₁ z)) *
        Real.sqrt (normalizedPairedEnergy (D₂ z) a₂ Z (t₂ z)))
      (nestedFourierMeasure F₁ F₂) := by
  have hleft := actual_nested_normalized_family_integrable cal₁ F₁ F₂
  have hright := actual_nested_normalized_family_integrable cal₂ F₁ F₂
  have hmeas := (Real.continuous_sqrt.comp_aestronglyMeasurable hleft.aestronglyMeasurable).mul
    (Real.continuous_sqrt.comp_aestronglyMeasurable hright.aestronglyMeasurable)
  apply ((hleft.add hright).div_const 2).mono' hmeas
  exact Filter.Eventually.of_forall fun z => by
    have hl := normalizedPairedEnergy_nonneg (D₁ z) a₁ Z (t₁ z) hZ
    have hr := normalizedPairedEnergy_nonneg (D₂ z) a₂ Z (t₂ z) hZ
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    nlinarith [Real.sq_sqrt hl, Real.sq_sqrt hr, sq_nonneg
      (Real.sqrt (normalizedPairedEnergy (D₁ z) a₁ Z (t₁ z)) -
        Real.sqrt (normalizedPairedEnergy (D₂ z) a₂ Z (t₂ z)))]

end ActualChildren

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.nestedFourierMeasure_density
#print axioms HeckeSkeleton.Moments.EngineStep.nestedFourierMeasure_uniform_mass
#print axioms HeckeSkeleton.Moments.EngineStep.actual_nested_normalized_family_integral
#print axioms HeckeSkeleton.Moments.EngineStep.actual_nested_normalized_cauchy_integrable

