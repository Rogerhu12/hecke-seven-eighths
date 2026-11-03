import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFiniteKernelMass

/-!
# Fixed powers of the common original profile control

The slot cap, polynomial Fourier orders and four natural power degrees
are fixed first. The original control P is at least one. Individual
bounds for the two radius constants and the two original Schwartz
seminorms then bound the exact profile envelope by one fixed power of P.

The family theorem keeps the original active carrier, actual normalized
children, original two Fourier kernels and literal arithmetic sum. No
total kernel mass or arithmetic sum estimate is supplied as an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

/-- The control degree is chosen before every moving original profile
or actual source family. -/
def originalProfilePowerDegree (cap dBL dBR dF₁ dF₂ : ℕ) : ℕ :=
  (cap + 2) * (dBL + dBR) + dF₁ + dF₂

/-- Each side contributes its original live-count envelope once, and
each original Fourier seminorm contributes once. -/
theorem original_profile_envelope_power_bound
    (cap dBL dBR dF₁ dF₂ : ℕ)
    (P B₁ B₂ S₁ S₂ : ℝ) (hP : 1 ≤ P)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hBL : B₁ ≤ P ^ dBL) (hBR : B₂ ≤ P ^ dBR)
    (hF₁ : S₁ ≤ P ^ dF₁) (hF₂ : S₂ ≤ P ^ dF₂) :
    pairedProfileEnvelopeConstant B₁ B₂ cap cap * S₁ * S₂ ≤
      (2 : ℝ) ^ (2 * cap + 4) *
        P ^ originalProfilePowerDegree cap dBL dBR dF₁ dF₂ := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hleft : 1 + B₁ ≤ 2 * P ^ dBL := by
    have hpow : 1 ≤ P ^ dBL := one_le_pow₀ hP
    linarith
  have hright : 1 + B₂ ≤ 2 * P ^ dBR := by
    have hpow : 1 ≤ P ^ dBR := one_le_pow₀ hP
    linarith
  have hleftPow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + B₁) hleft (cap + 2)
  have hrightPow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + B₂) hright (cap + 2)
  have hpair := mul_le_mul hleftPow hrightPow
    (pow_nonneg (by linarith : 0 ≤ 1 + B₂) _)
    (pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hP0 _)) _)
  have hpair0 : 0 ≤ (2 * P ^ dBL) ^ (cap + 2) * (2 * P ^ dBR) ^ (cap + 2) :=
    mul_nonneg
      (pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hP0 _)) _)
      (pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hP0 _)) _)
  have hfirst := mul_le_mul hpair hF₁ hS₁ hpair0
  have hsecond := mul_le_mul hfirst hF₂ hS₂
    (mul_nonneg hpair0 (pow_nonneg hP0 _))
  change pairedProfileEnvelopeConstant B₁ B₂ cap cap * S₁ * S₂ ≤ _ at hsecond
  apply hsecond.trans_eq
  have he₂ : 2 * cap + 4 = (cap + 2) + (cap + 2) := by omega
  have heP : originalProfilePowerDegree cap dBL dBR dF₁ dF₂ =
      (dBL * (cap + 2) + dBR * (cap + 2)) + dF₁ + dF₂ := by
    unfold originalProfilePowerDegree
    ring
  rw [he₂, heP]
  simp only [pow_add, mul_pow, pow_mul]
  ring

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]

/-- The same actual kernel family has an original-profile power bound.
The finite seminorms and constant precede P, the two original kernels,
every moving label and every capacity choice. The remaining sum is the
literal arithmetic weight of these same children. -/
theorem actual_finite_normalized_kernel_mass_original_profiles
    (cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ : ℕ) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ {Λ : Type*} (Z : ℝ) (hZ : 0 < Z) (P : ℝ), 1 ≤ P →
    ∀ s : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z,
    ∀ (labels : Finset Λ) (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ))
      (outer B₁ B₂ : Λ → ℝ) (parentWidth : ℝ),
      (∀ b ∈ labels, 0 ≤ outer b) →
      (∀ b ∈ labels, 0 ≤ B₁ b) → (∀ b ∈ labels, 0 ≤ B₂ b) →
      (∀ b ∈ labels, (s.leftSource b).allocation.keep.card ≤ cap) →
      (∀ b ∈ labels, (s.rightSource b).allocation.keep.card ≤ cap) →
      (∀ b ∈ labels, ∀ z,
        (s.leftCapacity b).radius (WithLp.toLp 2 z) = polynomialProfileRadius (B₁ b) J₁₁ J₁₂ z) →
      (∀ b ∈ labels, ∀ z,
        (s.rightCapacity b).radius (WithLp.toLp 2 z) = polynomialProfileRadius (B₂ b) J₂₁ J₂₂ z) →
      (∀ b ∈ labels, B₁ b ≤ P ^ dBL) →
      (∀ b ∈ labels, B₂ b ≤ P ^ dBR) →
      (∀ b ∈ labels,
        seminorms₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b) ≤ P ^ dF₁) →
      (∀ b ∈ labels,
        seminorms₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b) ≤ P ^ dF₂) →
      (∀ b : s.active labels,
        IsFiniteMeasure (s.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : s.active labels,
        (s.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
          C * P ^ originalProfilePowerDegree cap dBL dBR dF₁ dF₂ *
            ∑ b : s.active labels, outer b.val * s.weight labels parentWidth b := by
  obtain ⟨seminorms₁, seminorms₂, C, hC, hm⟩ :=
    actual_finite_normalized_kernel_mass (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      (U := U) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂
  refine ⟨seminorms₁, seminorms₂, C * (2 : ℝ) ^ (2 * cap + 4),
    mul_pos hC (pow_pos (by norm_num) _), ?_⟩
  intro Λ Z hZ P hP s labels F₁ F₂ outer B₁ B₂ parentWidth
    houter hB₁ hB₂ hcapL hcapR hradiusL hradiusR hBL hBR hF₁ hF₂
  have hprofiles (b : Λ) (hb : b ∈ labels) :
      pairedProfileEnvelopeConstant (B₁ b) (B₂ b) cap cap *
        seminorms₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b) *
          seminorms₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b) ≤
      (2 : ℝ) ^ (2 * cap + 4) *
        P ^ originalProfilePowerDegree cap dBL dBR dF₁ dF₂ :=
    original_profile_envelope_power_bound cap dBL dBR dF₁ dF₂ P (B₁ b) (B₂ b) _ _ hP
      (hB₁ b hb) (hB₂ b hb) (apply_nonneg _ _) (apply_nonneg _ _)
      (hBL b hb) (hBR b hb) (hF₁ b hb) (hF₂ b hb)
  have hh := hm Z hZ s labels F₁ F₂ outer B₁ B₂ parentWidth
    ((2 : ℝ) ^ (2 * cap + 4) * P ^ originalProfilePowerDegree cap dBL dBR dF₁ dF₂)
    houter hB₁ hB₂ hcapL hcapR hradiusL hradiusR hprofiles
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_profile_envelope_power_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_finite_normalized_kernel_mass_original_profiles

