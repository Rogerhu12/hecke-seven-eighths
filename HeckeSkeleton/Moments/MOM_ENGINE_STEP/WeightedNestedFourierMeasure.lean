import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedFourierMeasure

/-!
# Exact polynomial profile envelopes in the common Fourier kernel

Fourier-frozen child profiles are normalized before the recursive call.
Their exact positive envelope is retained in the original product
Fourier measure. Only the primitive pointwise polynomial envelope
window is assumed; finite mass and actual child integrability follow
from the two original Schwartz kernels.

All controlling seminorms and constants precede both kernels, the
envelope, and every moving child. The exact profile homogeneity is
used through the integral identity below, without discarding its
envelope or charging it a second time.
-/

noncomputable section
open scoped NumberField Classical BigOperators FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def weightedNestedFourierMeasure
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (envelope : V × E → ℝ) : Measure (V × E) :=
  (nestedFourierMeasure F₁ F₂).withDensity (fun z => ENNReal.ofReal (envelope z))

theorem actualFourierMeasure_polynomial_integral
    (F : 𝓢(V, ℂ)) (J : ℕ) :
    (∫ ξ, (1 + ‖ξ‖) ^ J ∂actualFourierMeasure F) =
      ∫ ξ : V, ‖(𝓕 F) ξ‖ * (1 + ‖ξ‖) ^ J := by
  have hm : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) := by fun_prop
  simpa only [actualFourierMeasure, ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure V)) hm
      (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top))
      (fun ξ : V => (1 + ‖ξ‖) ^ J))

theorem nestedFourierMeasure_mixed_polynomial_integrable
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (J₁ J₂ : ℕ) :
    Integrable (fun z : V × E => (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)
      (nestedFourierMeasure F₁ F₂) := by
  letI := actualFourierMeasure_finite F₁
  letI := actualFourierMeasure_finite F₂
  exact (actualFourierMeasure_polynomial_integrable F₁ J₁).mul_prod
    (actualFourierMeasure_polynomial_integrable F₂ J₂)

theorem nestedFourierMeasure_weighted_mass_bound (J₁ J₂ : ℕ) :
    ∃ s₁ s₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)),
        (∫ z : V × E, (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂
          ∂nestedFourierMeasure F₁ F₂) ≤
        C * s₁.sup (schwartzSeminormFamily ℝ V ℂ) F₁ *
          s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := joint_fourier_mass_bound (V := V) J₁
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := joint_fourier_mass_bound (V := E) J₂
  refine ⟨s₁, s₂, C₁ * C₂, mul_pos hC₁ hC₂, fun F₁ F₂ => ?_⟩
  letI := actualFourierMeasure_finite F₁
  letI := actualFourierMeasure_finite F₂
  have heq :
      (∫ z : V × E, (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂
        ∂nestedFourierMeasure F₁ F₂) =
      (∫ ξ, (1 + ‖ξ‖) ^ J₁ ∂actualFourierMeasure F₁) *
        (∫ η, (1 + ‖η‖) ^ J₂ ∂actualFourierMeasure F₂) := by
    unfold nestedFourierMeasure
    exact integral_prod_mul (μ := actualFourierMeasure F₁) (ν := actualFourierMeasure F₂)
      (fun ξ : V => (1 + ‖ξ‖) ^ J₁) (fun η : E => (1 + ‖η‖) ^ J₂)
  rw [heq, actualFourierMeasure_polynomial_integral,
    actualFourierMeasure_polynomial_integral]
  exact (mul_le_mul (h₁ F₁).2 (h₂ F₂).2
    (integral_nonneg fun η => mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
    (mul_nonneg hC₁.le (apply_nonneg _ F₁))).trans_eq (by ring)

/-- The envelope is original profile data, never an estimate of an
aggregate child energy. -/
theorem actual_profile_envelope_integrable
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (envelope : V × E → ℝ)
    (hmeas : Measurable envelope) (hnonneg : ∀ z, 0 ≤ envelope z)
    (B : ℝ) (J₁ J₂ : ℕ)
    (hbound : ∀ z, envelope z ≤ B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    Integrable envelope (nestedFourierMeasure F₁ F₂) := by
  apply ((nestedFourierMeasure_mixed_polynomial_integrable F₁ F₂ J₁ J₂).const_mul B).mono'
    hmeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
    exact hbound z

theorem weightedNestedFourierMeasure_finite
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (envelope : V × E → ℝ)
    (hmeas : Measurable envelope) (hnonneg : ∀ z, 0 ≤ envelope z)
    (B : ℝ) (J₁ J₂ : ℕ)
    (hbound : ∀ z, envelope z ≤ B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    IsFiniteMeasure (weightedNestedFourierMeasure F₁ F₂ envelope) := by
  have hi := actual_profile_envelope_integrable F₁ F₂ envelope hmeas hnonneg B J₁ J₂ hbound
  apply isFiniteMeasure_withDensity
  exact ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)).mp
    hi.hasFiniteIntegral).ne

theorem weightedNestedFourierMeasure_mass_eq
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (envelope : V × E → ℝ)
    (hmeas : Measurable envelope) (hnonneg : ∀ z, 0 ≤ envelope z) :
    (weightedNestedFourierMeasure F₁ F₂ envelope).real Set.univ =
      ∫ z, envelope z ∂nestedFourierMeasure F₁ F₂ := by
  have he : (weightedNestedFourierMeasure F₁ F₂ envelope) Set.univ =
      ∫⁻ z, ENNReal.ofReal (envelope z) ∂nestedFourierMeasure F₁ F₂ := by
    exact density_univ_eq_lintegral (nestedFourierMeasure F₁ F₂)
      (fun z => ENNReal.ofReal (envelope z))
  calc
    _ = (∫⁻ z, ENNReal.ofReal (envelope z) ∂nestedFourierMeasure F₁ F₂).toReal :=
      congrArg ENNReal.toReal he
    _ = _ := (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hnonneg) hmeas.aestronglyMeasurable).symm

/-- Weighted Fourier L1 controls the exact absorbed profile envelope.
The constants and seminorm sets are fixed before any moving data. -/
theorem weightedNestedFourierMeasure_uniform_mass (J₁ J₂ : ℕ) :
    ∃ s₁ s₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (B : ℝ), 0 ≤ B →
    ∀ envelope : V × E → ℝ, Measurable envelope →
      (∀ z, 0 ≤ envelope z) →
      (∀ z, envelope z ≤ B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) →
      IsFiniteMeasure (weightedNestedFourierMeasure F₁ F₂ envelope) ∧
      (weightedNestedFourierMeasure F₁ F₂ envelope).real Set.univ ≤
        B * C * s₁.sup (schwartzSeminormFamily ℝ V ℂ) F₁ *
          s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  obtain ⟨s₁, s₂, C, hC, hmoment⟩ := nestedFourierMeasure_weighted_mass_bound (V := V) (E := E) J₁ J₂
  refine ⟨s₁, s₂, C, hC, ?_⟩
  intro F₁ F₂ B hB envelope hmeas hnonneg hbound
  refine ⟨weightedNestedFourierMeasure_finite F₁ F₂ envelope hmeas hnonneg B J₁ J₂ hbound, ?_⟩
  rw [weightedNestedFourierMeasure_mass_eq F₁ F₂ envelope hmeas hnonneg]
  calc
    _ ≤ ∫ z : V × E, B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)
        ∂nestedFourierMeasure F₁ F₂ :=
      integral_mono
        (actual_profile_envelope_integrable F₁ F₂ envelope hmeas hnonneg B J₁ J₂ hbound)
        ((nestedFourierMeasure_mixed_polynomial_integrable F₁ F₂ J₁ J₂).const_mul B) hbound
    _ = B * ∫ z : V × E, (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂
        ∂nestedFourierMeasure F₁ F₂ := integral_const_mul _ _
    _ ≤ B * (C * s₁.sup (schwartzSeminormFamily ℝ V ℂ) F₁ *
        s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂) :=
      mul_le_mul_of_nonneg_left (hmoment F₁ F₂) hB
    _ = _ := by ring

/-- Exact transfer of the normalized profiles' envelope into the
positive kernel; this is an equality, before any absolute estimate. -/
theorem weightedNestedFourierMeasure_integral
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (envelope : V × E → ℝ)
    (hmeas : Measurable envelope) (hnonneg : ∀ z, 0 ≤ envelope z) (G : V × E → ℝ) :
    (∫ z, G z ∂weightedNestedFourierMeasure F₁ F₂ envelope) =
      ∫ z, envelope z * G z ∂nestedFourierMeasure F₁ F₂ := by
  have hm : Measurable (fun z => ENNReal.ofReal (envelope z)) := by fun_prop
  simpa only [weightedNestedFourierMeasure, ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul (μ := nestedFourierMeasure F₁ F₂) hm
      (Filter.Eventually.of_forall (fun z : V × E => ENNReal.ofReal_lt_top)) G)

section Children

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

theorem actual_weighted_nested_paired_integrable
    {D : V × E → MomentData K ω ψ} {n : ℕ}
    {hcount : ∀ z, (D z).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V × E → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (envelope : V × E → ℝ)
    (hmeas : Measurable envelope) (hnonneg : ∀ z, 0 ≤ envelope z)
    (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ)
    (hbound : ∀ z, envelope z ≤ B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    Integrable (fun z => pairedEnergy (D z) a Z (t z))
      (weightedNestedFourierMeasure F₁ F₂ envelope) := by
  have hac : nestedFourierMeasure F₁ F₂ ≪ (volume : Measure (V × E)) := by
    rw [nestedFourierMeasure_density]
    exact withDensity_absolutelyContinuous _ _
  have henergyMeas := AEStronglyMeasurable.mono_ac hac cal.energy_aestronglyMeasurable
  have hmajor := (nestedFourierMeasure_mixed_polynomial_integrable F₁ F₂
    (J₁ + cal.energyOrder) (J₂ + cal.energyOrder)).const_mul (B * cal.energyConstant)
  have hweighted : Integrable (fun z => envelope z * pairedEnergy (D z) a Z (t z))
      (nestedFourierMeasure F₁ F₂) := by
    apply hmajor.mono' (hmeas.aestronglyMeasurable.mul henergyMeas)
    exact Filter.Eventually.of_forall fun z => by
      have hE : 0 ≤ pairedEnergy (D z) a Z (t z) :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hnorm : (1 + ‖z‖) ^ cal.energyOrder ≤
          (1 + ‖z.1‖) ^ cal.energyOrder * (1 + ‖z.2‖) ^ cal.energyOrder :=
        (pow_le_pow_left₀ (by positivity) (one_add_prod_norm_le z) _).trans_eq (mul_pow _ _ _)
      have hpoly := (cal.energy_polynomial_bound z).trans
        (mul_le_mul_of_nonneg_left hnorm cal.energyConstant_nonneg)
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnonneg z) hE)]
      apply (mul_le_mul (hbound z) hpoly hE (by positivity)).trans_eq
      rw [pow_add, pow_add]
      ring
  have hm : Measurable (fun z => ENNReal.ofReal (envelope z)) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun z : V × E => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul] using hweighted

theorem actual_weighted_nested_normalized_integrable
    {D : V × E → MomentData K ω ψ} {n : ℕ}
    {hcount : ∀ z, (D z).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V × E → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (envelope : V × E → ℝ)
    (hmeas : Measurable envelope) (hnonneg : ∀ z, 0 ≤ envelope z)
    (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ)
    (hbound : ∀ z, envelope z ≤ B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    Integrable (fun z => normalizedPairedEnergy (D z) a Z (t z))
      (weightedNestedFourierMeasure F₁ F₂ envelope) :=
  (actual_weighted_nested_paired_integrable cal F₁ F₂ envelope hmeas hnonneg
    B hB J₁ J₂ hbound).div_const (Z ^ (a.m + a.q))

end Children

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.weightedNestedFourierMeasure_uniform_mass
#print axioms HeckeSkeleton.Moments.EngineStep.weightedNestedFourierMeasure_integral
#print axioms HeckeSkeleton.Moments.EngineStep.actual_weighted_nested_normalized_integrable

