import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileNormalizationInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WeightedNestedFourierMeasure

/-!
# Canonically normalized children under the exact common Fourier kernel

The original single-profile seminorm window grows polynomially in the
two Fourier variables. We choose the positive envelope 1 plus that
window, normalize the actual profiles, and retain exactly the square
root of each energy's homogeneity factor in one common positive kernel.
This proves membership in a fixed profile unit ball, finite kernel mass,
and integrability of the actual normalized children from the original
raw finite-atom control. No aggregate energy or family estimate is an
input, and neither Fourier variable is discretized.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def profilePolynomialWindow (J₁ J₂ : ℕ) (z : V × E) : ℝ :=
  (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂

theorem profilePolynomialWindow_one_le (J₁ J₂ : ℕ) (z : V × E) :
    1 ≤ profilePolynomialWindow J₁ J₂ z := by
  have h₁ : 1 ≤ (1 + ‖z.1‖) ^ J₁ := one_le_pow₀ (by linarith [norm_nonneg z.1])
  have h₂ : 1 ≤ (1 + ‖z.2‖) ^ J₂ := one_le_pow₀ (by linarith [norm_nonneg z.2])
  simpa only [one_mul] using mul_le_mul h₁ h₂ zero_le_one (by positivity)

def canonicalProfileAmplitude (B : ℝ) (J₁ J₂ : ℕ) (z : V × E) : ℝ :=
  1 + B * profilePolynomialWindow J₁ J₂ z

theorem canonicalProfileAmplitude_one_le (B : ℝ) (hB : 0 ≤ B)
    (J₁ J₂ : ℕ) (z : V × E) : 1 ≤ canonicalProfileAmplitude B J₁ J₂ z := by
  have h := mul_nonneg hB (zero_le_one.trans (profilePolynomialWindow_one_le J₁ J₂ z))
  dsimp only [canonicalProfileAmplitude]
  linarith

theorem canonicalProfileAmplitude_pos (B : ℝ) (hB : 0 ≤ B)
    (J₁ J₂ : ℕ) (z : V × E) : 0 < canonicalProfileAmplitude B J₁ J₂ z :=
  zero_lt_one.trans_le (canonicalProfileAmplitude_one_le B hB J₁ J₂ z)

theorem canonicalProfileAmplitude_measurable (B : ℝ) (J₁ J₂ : ℕ) :
    Measurable (canonicalProfileAmplitude (V := V) (E := E) B J₁ J₂) := by
  unfold canonicalProfileAmplitude profilePolynomialWindow
  fun_prop

theorem canonicalProfileAmplitude_le (B : ℝ) (J₁ J₂ : ℕ) (z : V × E) :
    canonicalProfileAmplitude B J₁ J₂ z ≤
      (1 + B) * profilePolynomialWindow J₁ J₂ z := by
  calc
    _ ≤ profilePolynomialWindow J₁ J₂ z + B * profilePolynomialWindow J₁ J₂ z :=
      add_le_add_right (profilePolynomialWindow_one_le J₁ J₂ z) _
    _ = _ := by ring

/-- This is the exact square-root energy envelope, not its square. -/
def canonicalPairEnvelope (n₁ n₂ : ℕ) (B₁ B₂ : ℝ) (J₁ J₂ : ℕ) (z : V × E) : ℝ :=
  canonicalProfileAmplitude B₁ J₁ J₂ z ^ (n₁ + 2) *
    canonicalProfileAmplitude B₂ J₁ J₂ z ^ (n₂ + 2)

theorem canonicalPairEnvelope_measurable (n₁ n₂ : ℕ) (B₁ B₂ : ℝ) (J₁ J₂ : ℕ) :
    Measurable (canonicalPairEnvelope (V := V) (E := E) n₁ n₂ B₁ B₂ J₁ J₂) :=
  ((canonicalProfileAmplitude_measurable B₁ J₁ J₂).pow_const _).mul
    ((canonicalProfileAmplitude_measurable B₂ J₁ J₂).pow_const _)

theorem canonicalPairEnvelope_nonneg (n₁ n₂ : ℕ) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ) (z : V × E) :
    0 ≤ canonicalPairEnvelope n₁ n₂ B₁ B₂ J₁ J₂ z :=
  mul_nonneg (pow_nonneg (canonicalProfileAmplitude_pos B₁ hB₁ J₁ J₂ z).le _)
    (pow_nonneg (canonicalProfileAmplitude_pos B₂ hB₂ J₁ J₂ z).le _)

theorem canonicalPairEnvelope_bound (n₁ n₂ : ℕ) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ) (z : V × E) :
    canonicalPairEnvelope n₁ n₂ B₁ B₂ J₁ J₂ z ≤
      ((1 + B₁) ^ (n₁ + 2) * (1 + B₂) ^ (n₂ + 2)) *
        ((1 + ‖z.1‖) ^ (J₁ * ((n₁ + 2) + (n₂ + 2))) *
          (1 + ‖z.2‖) ^ (J₂ * ((n₁ + 2) + (n₂ + 2)))) := by
  calc
    _ ≤ ((1 + B₁) * profilePolynomialWindow J₁ J₂ z) ^ (n₁ + 2) *
        ((1 + B₂) * profilePolynomialWindow J₁ J₂ z) ^ (n₂ + 2) :=
      mul_le_mul
        (pow_le_pow_left₀ (canonicalProfileAmplitude_pos B₁ hB₁ J₁ J₂ z).le
          (canonicalProfileAmplitude_le B₁ J₁ J₂ z) _)
        (pow_le_pow_left₀ (canonicalProfileAmplitude_pos B₂ hB₂ J₁ J₂ z).le
          (canonicalProfileAmplitude_le B₂ J₁ J₂ z) _)
        (pow_nonneg (canonicalProfileAmplitude_pos B₂ hB₂ J₁ J₂ z).le _)
        (by positivity)
    _ = _ := by
      dsimp only [profilePolynomialWindow]
      simp only [mul_pow, pow_mul, pow_add]
      ring

def normalizedPairMeasure (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (n₁ n₂ : ℕ) (B₁ B₂ : ℝ) (J₁ J₂ : ℕ) : Measure (V × E) :=
  weightedNestedFourierMeasure F₁ F₂ (canonicalPairEnvelope n₁ n₂ B₁ B₂ J₁ J₂)

/-- The seminorms and constant precede both original Fourier kernels,
both raw profile windows and the actual moving child families. -/
theorem normalizedPairMeasure_uniform_mass (n₁ n₂ J₁ J₂ : ℕ) :
    ∃ s₁ s₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      IsFiniteMeasure (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂) ∧
      (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂).real Set.univ ≤
        ((1 + B₁) ^ (n₁ + 2) * (1 + B₂) ^ (n₂ + 2)) * C *
          s₁.sup (schwartzSeminormFamily ℝ V ℂ) F₁ *
            s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  obtain ⟨s₁, s₂, C, hC, hmass⟩ := weightedNestedFourierMeasure_uniform_mass (V := V) (E := E)
    (J₁ * ((n₁ + 2) + (n₂ + 2))) (J₂ * ((n₁ + 2) + (n₂ + 2)))
  refine ⟨s₁, s₂, C, hC, fun F₁ F₂ B₁ B₂ hB₁ hB₂ => ?_⟩
  exact hmass F₁ F₂ ((1 + B₁) ^ (n₁ + 2) * (1 + B₂) ^ (n₂ + 2)) (by positivity)
    (canonicalPairEnvelope n₁ n₂ B₁ B₂ J₁ J₂)
    (canonicalPairEnvelope_measurable n₁ n₂ B₁ B₂ J₁ J₂)
    (canonicalPairEnvelope_nonneg n₁ n₂ B₁ B₂ hB₁ hB₂ J₁ J₂)
    (canonicalPairEnvelope_bound n₁ n₂ B₁ B₂ hB₁ hB₂ J₁ J₂)

/-- One seminorm window and constant work for every branch slot count
up to the original fixed cap. The choices do not depend on a deletion,
allocation, finite label, or either Fourier parameter. -/
theorem normalizedPairMeasure_uniform_mass_upto (N J₁ J₂ : ℕ) :
    ∃ s₁ s₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (n₁ n₂ : ℕ), n₁ ≤ N → n₂ ≤ N →
      ∀ (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      IsFiniteMeasure (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂) ∧
      (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂).real Set.univ ≤
        ((1 + B₁) ^ (N + 2) * (1 + B₂) ^ (N + 2)) * C *
          s₁.sup (schwartzSeminormFamily ℝ V ℂ) F₁ *
            s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  obtain ⟨s₁, s₂, C, hC, hmass⟩ := weightedNestedFourierMeasure_uniform_mass (V := V) (E := E)
    (J₁ * ((N + 2) + (N + 2))) (J₂ * ((N + 2) + (N + 2)))
  refine ⟨s₁, s₂, C, hC, fun n₁ n₂ hn₁ hn₂ F₁ F₂ B₁ B₂ hB₁ hB₂ => ?_⟩
  apply hmass F₁ F₂ ((1 + B₁) ^ (N + 2) * (1 + B₂) ^ (N + 2)) (by positivity)
    (canonicalPairEnvelope n₁ n₂ B₁ B₂ J₁ J₂)
    (canonicalPairEnvelope_measurable n₁ n₂ B₁ B₂ J₁ J₂)
    (canonicalPairEnvelope_nonneg n₁ n₂ B₁ B₂ hB₁ hB₂ J₁ J₂)
  intro z
  apply le_trans (b := canonicalPairEnvelope N N B₁ B₂ J₁ J₂ z)
  · exact mul_le_mul
      (pow_le_pow_right₀ (canonicalProfileAmplitude_one_le B₁ hB₁ J₁ J₂ z)
        (Nat.add_le_add_right hn₁ 2))
      (pow_le_pow_right₀ (canonicalProfileAmplitude_one_le B₂ hB₂ J₁ J₂ z)
        (Nat.add_le_add_right hn₂ 2))
      (pow_nonneg (canonicalProfileAmplitude_pos B₂ hB₂ J₁ J₂ z).le _)
      (pow_nonneg (canonicalProfileAmplitude_pos B₁ hB₁ J₁ J₂ z).le _)
  · exact canonicalPairEnvelope_bound N N B₁ B₂ hB₁ hB₂ J₁ J₂ z

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

def canonicalNormalizedFamily (P : ProfileNormalizationInput K ω ψ)
    (D : V × E → MomentData K ω ψ) (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ)
    (z : V × E) : MomentData K ω ψ :=
  P.normalizeData (D z) (canonicalProfileAmplitude B J₁ J₂ z)
    (canonicalProfileAmplitude_pos B hB J₁ J₂ z)

theorem canonicalNormalizedFamily_count (P : ProfileNormalizationInput K ω ψ)
    (D : V × E → MomentData K ω ψ) (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ) (z : V × E) :
    (canonicalNormalizedFamily P D B hB J₁ J₂ z).geometry.slotCount =
      (D z).geometry.slotCount := P.normalized_count _ _ _

/-- The raw seminorm growth is normalized internally into one fixed
profile family on the original row/height/support windows. -/
theorem canonicalNormalizedFamily_in_fixed_window
    (P : ProfileNormalizationInput K ω ψ) (D : V × E → MomentData K ω ψ)
    (rowDomain : Set (NonzeroIdeal K)) (heightDomain window : Set ℝ)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ)
    (raw : ∀ z, RawProfileWindow rowDomain heightDomain window s (D z)
      (B * profilePolynomialWindow J₁ J₂ z)) :
    ∀ z, InFixedProfileWindow rowDomain heightDomain window s
      (canonicalNormalizedFamily P D B hB J₁ J₂ z) := by
  intro z
  exact P.normalized_in_fixed_window (canonicalProfileAmplitude_pos B hB J₁ J₂ z)
    ((raw z).mono (by unfold canonicalProfileAmplitude; linarith))

theorem canonical_normalized_pair_identity
    (P : ProfileNormalizationInput K ω ψ)
    (D₁ D₂ : V × E → MomentData K ω ψ) (n₁ n₂ : ℕ)
    (hc₁ : ∀ z, (D₁ z).geometry.slotCount = n₁)
    (hc₂ : ∀ z, (D₂ z).geometry.slotCount = n₂)
    (a₁ a₂ : RealParameters) (Z : ℝ) (t₁ t₂ : V × E → ℝ)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ) (z : V × E) :
    Real.sqrt (normalizedPairedEnergy (D₁ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy (D₂ z) a₂ Z (t₂ z)) =
      canonicalPairEnvelope n₁ n₂ B₁ B₂ J₁ J₂ z *
        (Real.sqrt (normalizedPairedEnergy
          (canonicalNormalizedFamily P D₁ B₁ hB₁ J₁ J₂ z) a₁ Z (t₁ z)) *
        Real.sqrt (normalizedPairedEnergy
          (canonicalNormalizedFamily P D₂ B₂ hB₂ J₁ J₂ z) a₂ Z (t₂ z))) := by
  rw [P.sqrt_energy_recover (D₁ z) a₁ (canonicalProfileAmplitude B₁ J₁ J₂ z)
    (canonicalProfileAmplitude_pos B₁ hB₁ J₁ J₂ z) Z (t₁ z),
    P.sqrt_energy_recover (D₂ z) a₂ (canonicalProfileAmplitude B₂ J₁ J₂ z)
      (canonicalProfileAmplitude_pos B₂ hB₂ J₁ J₂ z) Z (t₂ z), hc₁ z, hc₂ z]
  unfold canonicalPairEnvelope canonicalNormalizedFamily
  ring

private theorem normalized_energy_integrable_of_raw {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (P : ProfileNormalizationInput K ω ψ)
    (D : X → MomentData K ω ψ) (n : ℕ) (hc : ∀ z, (D z).geometry.slotCount = n)
    (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) (t A : X → ℝ)
    (hA : ∀ z, 1 ≤ A z) (hmeas : Measurable A)
    (hraw : Integrable (fun z => normalizedPairedEnergy (D z) a Z (t z)) μ) :
    Integrable (fun z => normalizedPairedEnergy
      (P.normalizeData (D z) (A z) (zero_lt_one.trans_le (hA z))) a Z (t z)) μ := by
  have he : (fun z => normalizedPairedEnergy
      (P.normalizeData (D z) (A z) (zero_lt_one.trans_le (hA z))) a Z (t z)) =
      fun z => (A z)⁻¹ ^ ((n + 2) * 2) * normalizedPairedEnergy (D z) a Z (t z) := by
    funext z
    rw [P.normalized_energy, hc z]
  rw [he]
  apply hraw.mono' ((hmeas.inv.pow_const _).aestronglyMeasurable.mul hraw.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    have hpos : 0 < A z := zero_lt_one.trans_le (hA z)
    have hinv : (A z)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (hA z)
    have hp : (A z)⁻¹ ^ ((n + 2) * 2) ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hinv ((n + 2) * 2)
    have hE := normalizedPairedEnergy_nonneg (D z) a Z (t z) hZ
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr hpos.le) _) hE)]
    exact (mul_le_mul_of_nonneg_right hp hE).trans_eq (one_mul _)

/-- Integrability comes from the actual raw finite atoms and the two
Schwartz kernels. Neither a moment bound nor integrability of the
normalized child is a primitive input. -/
theorem canonical_normalized_pair_integrable_with_budget
    (P : ProfileNormalizationInput K ω ψ)
    {D₁ D₂ : V × E → MomentData K ω ψ} {n₁ n₂ : ℕ}
    {hc₁ : ∀ z, (D₁ z).geometry.slotCount = n₁}
    {hc₂ : ∀ z, (D₂ z).geometry.slotCount = n₂}
    {a₁ a₂ : RealParameters} {Z : ℝ} (hZ : 0 < Z) {t₁ t₂ : V × E → ℝ}
    (cal₁ : ActualFiniteFamilyControl D₁ n₁ hc₁ a₁ Z t₁)
    (cal₂ : ActualFiniteFamilyControl D₂ n₂ hc₂ a₂ Z t₂)
    (budget₁ budget₂ : ℕ) (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ) :
    Integrable (fun z => normalizedPairedEnergy
      (canonicalNormalizedFamily P D₁ B₁ hB₁ J₁ J₂ z) a₁ Z (t₁ z))
        (normalizedPairMeasure F₁ F₂ budget₁ budget₂ B₁ B₂ J₁ J₂) ∧
    Integrable (fun z => normalizedPairedEnergy
      (canonicalNormalizedFamily P D₂ B₂ hB₂ J₁ J₂ z) a₂ Z (t₂ z))
        (normalizedPairMeasure F₁ F₂ budget₁ budget₂ B₁ B₂ J₁ J₂) ∧
    Integrable (fun z =>
      Real.sqrt (normalizedPairedEnergy
        (canonicalNormalizedFamily P D₁ B₁ hB₁ J₁ J₂ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy
        (canonicalNormalizedFamily P D₂ B₂ hB₂ J₁ J₂ z) a₂ Z (t₂ z)))
        (normalizedPairMeasure F₁ F₂ budget₁ budget₂ B₁ B₂ J₁ J₂) := by
  let env := canonicalPairEnvelope (V := V) (E := E) budget₁ budget₂ B₁ B₂ J₁ J₂
  let bound : ℝ := (1 + B₁) ^ (budget₁ + 2) * (1 + B₂) ^ (budget₂ + 2)
  have hm := canonicalPairEnvelope_measurable (V := V) (E := E) budget₁ budget₂ B₁ B₂ J₁ J₂
  have hn := canonicalPairEnvelope_nonneg (V := V) (E := E) budget₁ budget₂ B₁ B₂ hB₁ hB₂ J₁ J₂
  have hb := canonicalPairEnvelope_bound (V := V) (E := E) budget₁ budget₂ B₁ B₂ hB₁ hB₂ J₁ J₂
  have raw₁ := actual_weighted_nested_normalized_integrable cal₁ F₁ F₂ env hm hn
    bound (by dsimp [bound]; positivity)
    (J₁ * ((budget₁ + 2) + (budget₂ + 2))) (J₂ * ((budget₁ + 2) + (budget₂ + 2))) hb
  have raw₂ := actual_weighted_nested_normalized_integrable cal₂ F₁ F₂ env hm hn
    bound (by dsimp [bound]; positivity)
    (J₁ * ((budget₁ + 2) + (budget₂ + 2))) (J₂ * ((budget₁ + 2) + (budget₂ + 2))) hb
  have left := normalized_energy_integrable_of_raw _ P D₁ n₁ hc₁ a₁ Z hZ t₁
    (canonicalProfileAmplitude B₁ J₁ J₂) (canonicalProfileAmplitude_one_le B₁ hB₁ J₁ J₂)
    (canonicalProfileAmplitude_measurable B₁ J₁ J₂) raw₁
  have right := normalized_energy_integrable_of_raw _ P D₂ n₂ hc₂ a₂ Z hZ t₂
    (canonicalProfileAmplitude B₂ J₁ J₂) (canonicalProfileAmplitude_one_le B₂ hB₂ J₁ J₂)
    (canonicalProfileAmplitude_measurable B₂ J₁ J₂) raw₂
  refine ⟨left, right, ?_⟩
  have hmeas := (Real.continuous_sqrt.comp_aestronglyMeasurable left.aestronglyMeasurable).mul
    (Real.continuous_sqrt.comp_aestronglyMeasurable right.aestronglyMeasurable)
  apply ((left.add right).div_const 2).mono' hmeas
  exact Filter.Eventually.of_forall fun z => by
    have hl := normalizedPairedEnergy_nonneg
      (canonicalNormalizedFamily P D₁ B₁ hB₁ J₁ J₂ z) a₁ Z (t₁ z) hZ
    have hr := normalizedPairedEnergy_nonneg
      (canonicalNormalizedFamily P D₂ B₂ hB₂ J₁ J₂ z) a₂ Z (t₂ z) hZ
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    nlinarith [Real.sq_sqrt hl, Real.sq_sqrt hr, sq_nonneg
      (Real.sqrt (normalizedPairedEnergy
        (canonicalNormalizedFamily P D₁ B₁ hB₁ J₁ J₂ z) a₁ Z (t₁ z)) -
      Real.sqrt (normalizedPairedEnergy
        (canonicalNormalizedFamily P D₂ B₂ hB₂ J₁ J₂ z) a₂ Z (t₂ z)))]

/-- The exact homogeneity degree is the budget when no slots were removed. -/
theorem canonical_normalized_pair_integrable
    (P : ProfileNormalizationInput K ω ψ)
    {D₁ D₂ : V × E → MomentData K ω ψ} {n₁ n₂ : ℕ}
    {hc₁ : ∀ z, (D₁ z).geometry.slotCount = n₁}
    {hc₂ : ∀ z, (D₂ z).geometry.slotCount = n₂}
    {a₁ a₂ : RealParameters} {Z : ℝ} (hZ : 0 < Z) {t₁ t₂ : V × E → ℝ}
    (cal₁ : ActualFiniteFamilyControl D₁ n₁ hc₁ a₁ Z t₁)
    (cal₂ : ActualFiniteFamilyControl D₂ n₂ hc₂ a₂ Z t₂)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ) :
    Integrable (fun z => normalizedPairedEnergy
      (canonicalNormalizedFamily P D₁ B₁ hB₁ J₁ J₂ z) a₁ Z (t₁ z))
        (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂) ∧
    Integrable (fun z => normalizedPairedEnergy
      (canonicalNormalizedFamily P D₂ B₂ hB₂ J₁ J₂ z) a₂ Z (t₂ z))
        (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂) ∧
    Integrable (fun z =>
      Real.sqrt (normalizedPairedEnergy
        (canonicalNormalizedFamily P D₁ B₁ hB₁ J₁ J₂ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy
        (canonicalNormalizedFamily P D₂ B₂ hB₂ J₁ J₂ z) a₂ Z (t₂ z)))
        (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂) :=
  canonical_normalized_pair_integrable_with_budget P hZ cal₁ cal₂ n₁ n₂
    F₁ F₂ B₁ B₂ hB₁ hB₂ J₁ J₂

/-- Exact common-kernel replacement. The preceding theorem proves the
three required integrability statements from the original family. -/
theorem canonical_normalized_pair_integral
    (P : ProfileNormalizationInput K ω ψ)
    (D₁ D₂ : V × E → MomentData K ω ψ) (n₁ n₂ : ℕ)
    (hc₁ : ∀ z, (D₁ z).geometry.slotCount = n₁)
    (hc₂ : ∀ z, (D₂ z).geometry.slotCount = n₂)
    (a₁ a₂ : RealParameters) (Z : ℝ) (t₁ t₂ : V × E → ℝ)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ) :
    (∫ z, Real.sqrt (normalizedPairedEnergy (D₁ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy (D₂ z) a₂ Z (t₂ z)) ∂nestedFourierMeasure F₁ F₂) =
    ∫ z, Real.sqrt (normalizedPairedEnergy
        (canonicalNormalizedFamily P D₁ B₁ hB₁ J₁ J₂ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy
        (canonicalNormalizedFamily P D₂ B₂ hB₂ J₁ J₂ z) a₂ Z (t₂ z))
      ∂normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂ := by
  rw [normalizedPairMeasure, weightedNestedFourierMeasure_integral F₁ F₂ _
    (canonicalPairEnvelope_measurable n₁ n₂ B₁ B₂ J₁ J₂)
    (canonicalPairEnvelope_nonneg n₁ n₂ B₁ B₂ hB₁ hB₂ J₁ J₂)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (canonical_normalized_pair_identity P D₁ D₂ n₁ n₂ hc₁ hc₂ a₁ a₂ Z t₁ t₂
      B₁ B₂ hB₁ hB₂ J₁ J₂)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.canonicalNormalizedFamily_in_fixed_window
#print axioms HeckeSkeleton.Moments.EngineStep.canonical_normalized_pair_identity
#print axioms HeckeSkeleton.Moments.EngineStep.canonical_normalized_pair_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.canonical_normalized_pair_integrable_with_budget
#print axioms HeckeSkeleton.Moments.EngineStep.canonical_normalized_pair_integral
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedPairMeasure_uniform_mass
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedPairMeasure_uniform_mass_upto
