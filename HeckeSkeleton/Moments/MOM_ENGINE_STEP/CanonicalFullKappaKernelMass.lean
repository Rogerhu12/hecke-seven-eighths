import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaNormalization

/-!
# The enlarged full-kappa profiles pay their actual common-kernel mass

This is the existing finite-family mass theorem applied to the literal
polynomial radii constructed by the full-kappa side constructor. The
two original Fourier kernels, the same active carrier, chosen children,
outer scalar and arithmetic weights stay fixed.

The analytic contour and Fourier orders are chosen first. Individual
original radius coefficients and the two original kernel seminorms
are the only profile windows. Every pre-removal slot and both plain
profiles on both sides are charged, including all retained slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open MeasureTheory NumberField
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

namespace CanonicalFullKappaPrime

/-- Uniform original single-profile coefficients bound the original
paired envelope with its complete, explicit degree. -/
theorem paired_envelopeConstant_le_bound (B₁ B₂ B : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (h₁ : B₁ ≤ B) (h₂ : B₂ ≤ B)
    (n₁ n₂ : ℕ) :
    pairedProfileEnvelopeConstant B₁ B₂ n₁ n₂ ≤
      (1 + B) ^ ((n₁ + 2) + (n₂ + 2)) := by
  rw [pow_add]
  exact mul_le_mul
    (pow_le_pow_left₀ (by linarith) (add_le_add le_rfl h₁) _)
    (pow_le_pow_left₀ (by linarith) (add_le_add le_rfl h₂) _)
    (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]

/-- The full-kappa normalization is integrated on its own actual family.
The remaining finite sum is the exact arithmetic mass of those same
children, for subsequent use by the actual index-mass theorem. No mass
estimate or child-energy bound is a premise. -/
theorem actual_finite_kernel_mass
    (cap J₁₁ J₁₂ J₂₁ J₂₂ h : ℕ) (ε lengthBound H₀ widthBound : ℝ)
    (hε : 0 < ε) (hL : 0 ≤ lengthBound) (hwidth : 0 ≤ widthBound) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ δ Cmass : ℝ,
      0 < δ ∧ δ ≤ 1 / 4 ∧ 0 < Cmass ∧
      ∀ Z T width height : ℝ, 1 ≤ Z → 0 ≤ T → width ≤ widthBound →
        height ≤ H₀ * (1 + Real.log Z) * (1 + T) ^ h →
      ∀ {Λ : Type*} (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
        (labels : Finset Λ) (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ))
        (outer B₁ B₂ : Λ → ℝ) (parentWidth B Fbound₁ Fbound₂ : ℝ),
        0 ≤ B → 0 ≤ Fbound₁ → 0 ≤ Fbound₂ →
        (∀ b ∈ labels, 0 ≤ outer b) →
        (∀ b ∈ labels, 0 ≤ B₁ b ∧ B₁ b ≤ B) →
        (∀ b ∈ labels, 0 ≤ B₂ b ∧ B₂ b ≤ B) →
        (∀ b ∈ labels, (family.leftSource b).allocation.keep.card ≤ cap) →
        (∀ b ∈ labels, (family.rightSource b).allocation.keep.card ≤ cap) →
        (∀ b ∈ labels, ∀ z,
          (family.leftCapacity b).radius (WithLp.toLp 2 z) =
            polynomialProfileRadius (enlargedCoefficient (B₁ b)
              (radiusFactor K Z δ lengthBound (CanonicalHeckePrimeAnalytic.degreeBound K)
                height (CompleteMovingRowRecipe.primeMaskLogBound A Z width))) J₁₁ J₁₂ z) →
        (∀ b ∈ labels, ∀ z,
          (family.rightCapacity b).radius (WithLp.toLp 2 z) =
            polynomialProfileRadius (enlargedCoefficient (B₂ b)
              (radiusFactor K Z δ lengthBound (CanonicalHeckePrimeAnalytic.degreeBound K)
                height (CompleteMovingRowRecipe.primeMaskLogBound A Z width))) J₂₁ J₂₂ z) →
        (∀ b ∈ labels, seminorms₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b) ≤ Fbound₁) →
        (∀ b ∈ labels, seminorms₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b) ≤ Fbound₂) →
        (∀ b : family.active labels,
          IsFiniteMeasure (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer)
            parentWidth b)) ∧
        (∑ b : family.active labels,
          (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer)
            parentWidth b).real Set.univ) ≤
          Cmass * (1 + B) ^ ((cap + 2) + (cap + 2)) * Fbound₁ * Fbound₂ *
            (1 + T) ^ (h * ((cap + 2) + (cap + 2))) * Z ^ ε *
              ∑ b : family.active labels, outer b.val * family.weight labels parentWidth b := by
  let N := (cap + 2) + (cap + 2)
  obtain ⟨δ, Cr, hδ, hδhi, hCr, hr⟩ := exists_complete_profile_radius_bound
    A N h ε lengthBound (CanonicalHeckePrimeAnalytic.degreeBound K) H₀ widthBound
    hε CanonicalHeckePrimeAnalytic.degreeBound_pos.le hwidth
  obtain ⟨s₁, s₂, Cf, hCf, hm⟩ := actual_finite_normalized_kernel_mass
    (F := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := U) (E := E)
    cap J₁₁ J₁₂ J₂₁ J₂₂
  refine ⟨s₁, s₂, δ, Cf * (2 * Cr) ^ N, hδ, hδhi,
    mul_pos hCf (pow_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hCr)) _), ?_⟩
  intro Z T width height hZ hT hbox hheight Λ family labels F₁ F₂ outer B₁ B₂
    parentWidth B Fbound₁ Fbound₂ hB hF₁ hF₂ houter hB₁ hB₂ hcapL hcapR hradL hradR
    hkernel₁ hkernel₂
  let R := radiusFactor K Z δ lengthBound (CanonicalHeckePrimeAnalytic.degreeBound K)
    height (CompleteMovingRowRecipe.primeMaskLogBound A Z width)
  have hR : 1 ≤ R := one_le_radiusFactor _ _ _ _ _ _ hZ hδ.le hL
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hRp : (2 * R) ^ N ≤ (2 * Cr) ^ N * (1 + T) ^ (h * N) * Z ^ ε := by
    have hb := mul_le_mul_of_nonneg_left (hr Z T width height hZ hT hbox hheight)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N)
    simpa only [mul_pow, mul_assoc] using hb
  let control := (2 * Cr) ^ N * (1 + B) ^ N * Fbound₁ * Fbound₂ *
    (1 + T) ^ (h * N) * Z ^ ε
  have hprofiles : ∀ b ∈ labels,
      pairedProfileEnvelopeConstant (enlargedCoefficient (B₁ b) R)
        (enlargedCoefficient (B₂ b) R) cap cap *
        s₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b) *
        s₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b) ≤ control := by
    intro b hb
    have henv := (paired_envelopeConstant_le (B₁ b) (B₂ b) R
      (hB₁ b hb).1 (hB₂ b hb).1 hR cap cap).trans
        (mul_le_mul_of_nonneg_left
          (paired_envelopeConstant_le_bound (B₁ b) (B₂ b) B
            (hB₁ b hb).1 (hB₂ b hb).1 (hB₁ b hb).2 (hB₂ b hb).2 cap cap)
          (pow_nonneg (mul_nonneg (by norm_num) hR0) _))
    have hs₁ : 0 ≤ s₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b) := by positivity
    have hs₂ : 0 ≤ s₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b) := by positivity
    calc
      _ ≤ ((2 * R) ^ N * (1 + B) ^ N) * Fbound₁ * Fbound₂ :=
        mul_le_mul
          (mul_le_mul henv (hkernel₁ b hb) hs₁ (by positivity))
          (hkernel₂ b hb) hs₂ (by positivity)
      _ ≤ (((2 * Cr) ^ N * (1 + T) ^ (h * N) * Z ^ ε) * (1 + B) ^ N) *
          Fbound₁ * Fbound₂ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hRp (pow_nonneg (by linarith) N)) hF₁) hF₂
      _ = control := by dsimp only [control]; ring
  have hout := hm Z (zero_lt_one.trans_le hZ) family labels F₁ F₂ outer
    (fun b => enlargedCoefficient (B₁ b) R) (fun b => enlargedCoefficient (B₂ b) R)
    parentWidth control houter
    (fun b hb => enlargedCoefficient_nonneg (hB₁ b hb).1 hR0)
    (fun b hb => enlargedCoefficient_nonneg (hB₂ b hb).1 hR0)
    hcapL hcapR hradL hradR hprofiles
  refine ⟨hout.1, hout.2.trans_eq ?_⟩
  dsimp only [control, N]
  ring

end CanonicalFullKappaPrime
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.paired_envelopeConstant_le_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.actual_finite_kernel_mass
