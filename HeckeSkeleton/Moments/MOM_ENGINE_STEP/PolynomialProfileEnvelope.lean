import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WeightedNestedFourierMeasure
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# A measurable common envelope for normalized Fourier profiles

The radii are explicit positive polynomials in the two Fourier norms.
Each radius dominates every requested profile seminorm.  A child with
`k` prime slots extracts the amplitude power `k + 2`; the pair therefore
contributes the product of the two exact amplitude powers to the same
Fourier measure.  The required weighted Fourier orders are computed
before any original kernel, coefficient, row or moving frequency.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open MeasureTheory

variable {V E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup E]

/-- The child dictionaries use the Hilbert product, but the Fourier
measure is the original product measure.  Its two norm weights dominate
the Hilbert norm without changing either measure or metric. -/
theorem one_add_hilbert_product_norm_le (z : V × E) :
    1 + ‖WithLp.toLp 2 z‖ ≤ (1 + ‖z.1‖) * (1 + ‖z.2‖) := by
  have hn : ‖WithLp.toLp 2 z‖ ≤ ‖z.1‖ + ‖z.2‖ := by
    rw [WithLp.prod_norm_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd]
    calc
      _ ≤ Real.sqrt ((‖z.1‖ + ‖z.2‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2)])
      _ = _ := Real.sqrt_sq (add_nonneg (norm_nonneg z.1) (norm_nonneg z.2))
  nlinarith [mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2)]

theorem hilbert_product_polynomial_le (J : ℕ) (z : V × E) :
    (1 + ‖WithLp.toLp 2 z‖) ^ J ≤ (1 + ‖z.1‖) ^ J * (1 + ‖z.2‖) ^ J :=
  (pow_le_pow_left₀ (by positivity) (one_add_hilbert_product_norm_le z) J).trans_eq
    (mul_pow _ _ _)

def polynomialProfileRadius (B : ℝ) (J₁ J₂ : ℕ) (z : V × E) : ℝ :=
  1 + B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)

theorem polynomialProfileRadius_one_le (B : ℝ) (hB : 0 ≤ B)
    (J₁ J₂ : ℕ) (z : V × E) : 1 ≤ polynomialProfileRadius B J₁ J₂ z := by
  unfold polynomialProfileRadius
  exact le_add_of_nonneg_right
    (mul_nonneg hB (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)))

theorem polynomialProfileRadius_pos (B : ℝ) (hB : 0 ≤ B)
    (J₁ J₂ : ℕ) (z : V × E) : 0 < polynomialProfileRadius B J₁ J₂ z :=
  zero_lt_one.trans_le (polynomialProfileRadius_one_le B hB J₁ J₂ z)

theorem polynomialProfileRadius_continuous (B : ℝ) (J₁ J₂ : ℕ) :
    Continuous (polynomialProfileRadius (V := V) (E := E) B J₁ J₂) := by
  unfold polynomialProfileRadius
  fun_prop

theorem polynomialProfileRadius_le (B : ℝ) (J₁ J₂ : ℕ) (z : V × E) :
    polynomialProfileRadius B J₁ J₂ z ≤
      (1 + B) * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂) := by
  have h₁ : 1 ≤ (1 + ‖z.1‖) ^ J₁ :=
    one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
  have h₂ : 1 ≤ (1 + ‖z.2‖) ^ J₂ :=
    one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
  have hprod : 1 ≤ (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂ :=
    one_le_mul_of_one_le_of_one_le h₁ h₂
  unfold polynomialProfileRadius
  nlinarith

/-- Finitely many original seminorm orders are combined before any
frequency is chosen.  This uses the sum of their constants and maximum
of their two polynomial orders, including an empty order set. -/
theorem finite_polynomial_profile_bound {ι : Type*}
    (orders : Finset ι) (B : ι → ℝ) (J₁ J₂ : ι → ℕ)
    (hB : ∀ q ∈ orders, 0 ≤ B q) (f : ι → V × E → ℝ)
    (hbound : ∀ q ∈ orders, ∀ z, f q z ≤
      B q * ((1 + ‖z.1‖) ^ J₁ q * (1 + ‖z.2‖) ^ J₂ q)) :
    ∀ q ∈ orders, ∀ z, f q z ≤
      (∑ p ∈ orders, B p) *
        ((1 + ‖z.1‖) ^ orders.sup J₁ * (1 + ‖z.2‖) ^ orders.sup J₂) := by
  intro q hq z
  have hb : B q ≤ ∑ p ∈ orders, B p := Finset.single_le_sum hB hq
  have hp₁ := pow_le_pow_right₀
    (le_add_of_nonneg_right (norm_nonneg z.1)) (Finset.le_sup (f := J₁) hq)
  have hp₂ := pow_le_pow_right₀
    (le_add_of_nonneg_right (norm_nonneg z.2)) (Finset.le_sup (f := J₂) hq)
  have hp := mul_le_mul hp₁ hp₂ (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)
  exact (hbound q hq z).trans (mul_le_mul hb hp
    (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _))
    (Finset.sum_nonneg hB))

def pairedProfileEnvelope (B₁ B₂ : ℝ) (k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (z : V × E) : ℝ :=
  polynomialProfileRadius B₁ J₁₁ J₁₂ z ^ (k₁ + 2) *
    polynomialProfileRadius B₂ J₂₁ J₂₂ z ^ (k₂ + 2)

def pairedProfileEnvelopeConstant (B₁ B₂ : ℝ) (k₁ k₂ : ℕ) : ℝ :=
  (1 + B₁) ^ (k₁ + 2) * (1 + B₂) ^ (k₂ + 2)

def pairedProfileEnvelopeOrder (k₁ k₂ J₁ J₂ : ℕ) : ℕ :=
  J₁ * (k₁ + 2) + J₂ * (k₂ + 2)

theorem pairedProfileEnvelope_nonneg (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (z : V × E) :
    0 ≤ pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ z := by
  exact mul_nonneg
    (pow_nonneg (polynomialProfileRadius_pos B₁ hB₁ J₁₁ J₁₂ z).le _)
    (pow_nonneg (polynomialProfileRadius_pos B₂ hB₂ J₂₁ J₂₂ z).le _)

theorem pairedProfileEnvelope_constant_nonneg (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (k₁ k₂ : ℕ) :
    0 ≤ pairedProfileEnvelopeConstant B₁ B₂ k₁ k₂ := by
  unfold pairedProfileEnvelopeConstant
  positivity

theorem pairedProfileEnvelope_continuous (B₁ B₂ : ℝ)
    (k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) :
    Continuous (pairedProfileEnvelope (V := V) (E := E)
      B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂) :=
  ((polynomialProfileRadius_continuous B₁ J₁₁ J₁₂).pow _).mul
    ((polynomialProfileRadius_continuous B₂ J₂₁ J₂₂).pow _)

/-- The precise amplitude powers are paid once, with separate polynomial
orders for the first and second continuous parameters. -/
theorem pairedProfileEnvelope_bound (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (z : V × E) :
    pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ z ≤
      pairedProfileEnvelopeConstant B₁ B₂ k₁ k₂ *
        ((1 + ‖z.1‖) ^ pairedProfileEnvelopeOrder k₁ k₂ J₁₁ J₂₁ *
          (1 + ‖z.2‖) ^ pairedProfileEnvelopeOrder k₁ k₂ J₁₂ J₂₂) := by
  have hleft := pow_le_pow_left₀
    (polynomialProfileRadius_pos B₁ hB₁ J₁₁ J₁₂ z).le
    (polynomialProfileRadius_le B₁ J₁₁ J₁₂ z) (k₁ + 2)
  have hright := pow_le_pow_left₀
    (polynomialProfileRadius_pos B₂ hB₂ J₂₁ J₂₂ z).le
    (polynomialProfileRadius_le B₂ J₂₁ J₂₂ z) (k₂ + 2)
  have h := mul_le_mul hleft hright
    (pow_nonneg (polynomialProfileRadius_pos B₂ hB₂ J₂₁ J₂₂ z).le _)
    (pow_nonneg (by positivity :
      0 ≤ (1 + B₁) * ((1 + ‖z.1‖) ^ J₁₁ * (1 + ‖z.2‖) ^ J₁₂)) _)
  convert h using 1 <;>
    simp only [pairedProfileEnvelope, pairedProfileEnvelopeConstant, pairedProfileEnvelopeOrder,
      mul_pow, pow_add, pow_mul] <;> ring

/-- A fixed slot cap controls every subsequent allocation and deletion.
The density itself retains its exact smaller amplitude powers. -/
theorem pairedProfileEnvelope_le_cap (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (k₁ k₂ cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (hk₁ : k₁ ≤ cap) (hk₂ : k₂ ≤ cap)
    (z : V × E) :
    pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ z ≤
      pairedProfileEnvelope B₁ B₂ cap cap J₁₁ J₁₂ J₂₁ J₂₂ z := by
  apply mul_le_mul
    (pow_le_pow_right₀ (polynomialProfileRadius_one_le B₁ hB₁ J₁₁ J₁₂ z)
      (Nat.add_le_add_right hk₁ 2))
    (pow_le_pow_right₀ (polynomialProfileRadius_one_le B₂ hB₂ J₂₁ J₂₂ z)
      (Nat.add_le_add_right hk₂ 2))
    (pow_nonneg (polynomialProfileRadius_pos B₂ hB₂ J₂₁ J₂₂ z).le _)
    (pow_nonneg (polynomialProfileRadius_pos B₁ hB₁ J₁₁ J₁₂ z).le _)

theorem pairedProfileEnvelope_bound_with_cap (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (k₁ k₂ cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (hk₁ : k₁ ≤ cap) (hk₂ : k₂ ≤ cap)
    (z : V × E) :
    pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ z ≤
      pairedProfileEnvelopeConstant B₁ B₂ cap cap *
        ((1 + ‖z.1‖) ^ pairedProfileEnvelopeOrder cap cap J₁₁ J₂₁ *
          (1 + ‖z.2‖) ^ pairedProfileEnvelopeOrder cap cap J₁₂ J₂₂) :=
  (pairedProfileEnvelope_le_cap B₁ B₂ hB₁ hB₂ k₁ k₂ cap J₁₁ J₁₂ J₂₁ J₂₂ hk₁ hk₂ z).trans
    (pairedProfileEnvelope_bound B₁ B₂ hB₁ hB₂ cap cap J₁₁ J₁₂ J₂₁ J₂₂ z)

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Original Fourier seminorm orders and constants are fixed before
both original kernels and both moving-profile constants. -/
theorem normalized_profile_kernel_uniform_mass
    (k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) :
    ∃ s₁ s₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      IsFiniteMeasure (weightedNestedFourierMeasure F₁ F₂
        (pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)) ∧
      (weightedNestedFourierMeasure F₁ F₂
        (pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)).real Set.univ ≤
        pairedProfileEnvelopeConstant B₁ B₂ k₁ k₂ * C *
          s₁.sup (schwartzSeminormFamily ℝ V ℂ) F₁ *
            s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  obtain ⟨s₁, s₂, C, hC, hmass⟩ :=
    weightedNestedFourierMeasure_uniform_mass (V := V) (E := E)
      (pairedProfileEnvelopeOrder k₁ k₂ J₁₁ J₂₁)
      (pairedProfileEnvelopeOrder k₁ k₂ J₁₂ J₂₂)
  refine ⟨s₁, s₂, C, hC, ?_⟩
  intro F₁ F₂ B₁ B₂ hB₁ hB₂
  exact hmass F₁ F₂ (pairedProfileEnvelopeConstant B₁ B₂ k₁ k₂)
    (pairedProfileEnvelope_constant_nonneg B₁ B₂ hB₁ hB₂ k₁ k₂)
    (pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)
    (pairedProfileEnvelope_continuous B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂).measurable
    (pairedProfileEnvelope_nonneg B₁ B₂ hB₁ hB₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)
    (pairedProfileEnvelope_bound B₁ B₂ hB₁ hB₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)

/-- One common pair of original seminorms works for every branch whose
slot counts obey the previously fixed cap.  In particular the orders
are not reselected after a divisor allocation or a removed set. -/
theorem normalized_profile_kernel_uniform_mass_up_to
    (cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) :
    ∃ s₁ s₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
    ∀ k₁ k₂ : ℕ, k₁ ≤ cap → k₂ ≤ cap →
      IsFiniteMeasure (weightedNestedFourierMeasure F₁ F₂
        (pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)) ∧
      (weightedNestedFourierMeasure F₁ F₂
        (pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)).real Set.univ ≤
        pairedProfileEnvelopeConstant B₁ B₂ cap cap * C *
          s₁.sup (schwartzSeminormFamily ℝ V ℂ) F₁ *
            s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  obtain ⟨s₁, s₂, C, hC, hmass⟩ :=
    weightedNestedFourierMeasure_uniform_mass (V := V) (E := E)
      (pairedProfileEnvelopeOrder cap cap J₁₁ J₂₁)
      (pairedProfileEnvelopeOrder cap cap J₁₂ J₂₂)
  refine ⟨s₁, s₂, C, hC, ?_⟩
  intro F₁ F₂ B₁ B₂ hB₁ hB₂ k₁ k₂ hk₁ hk₂
  exact hmass F₁ F₂ (pairedProfileEnvelopeConstant B₁ B₂ cap cap)
    (pairedProfileEnvelope_constant_nonneg B₁ B₂ hB₁ hB₂ cap cap)
    (pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)
    (pairedProfileEnvelope_continuous B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂).measurable
    (pairedProfileEnvelope_nonneg B₁ B₂ hB₁ hB₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)
    (pairedProfileEnvelope_bound_with_cap B₁ B₂ hB₁ hB₂ k₁ k₂ cap
      J₁₁ J₁₂ J₂₁ J₂₂ hk₁ hk₂)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.pairedProfileEnvelope_bound
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_profile_kernel_uniform_mass
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_profile_kernel_uniform_mass_up_to
