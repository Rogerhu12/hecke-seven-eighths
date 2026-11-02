import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRadiusBound

set_option linter.unusedSectionVars false

/-!
# Profile mass on the same actual nonzero carrier

All literal rectangles receive their computed normalization before
source activity is tested. Identically zero sides need not have a
uniform quotient-scale or clipping bound. The exact kernel family
only contains labels for which both original sources are nonzero.

The two results below integrate that very family. They use the fixed
profile coefficient bound only on its existing `active` subtype;
no labels, radii, removed sets, kernels or chosen children are changed.
The full-kappa enlargement still pays every pre-removal slot and both
plain profiles on both sides. Its Fourier orders and small exponent
are chosen before the moving family.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ} {ω ψ : HeckeCharacter F}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]

namespace ActualNormalizedPairFamily

variable {Λ : Type*} {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
variable (labels : Finset Λ)

/-- Activity supplies a genuine raw nonzero member through the actual
term calibration; no extra child-energy hypothesis is needed. -/
theorem active_left_raw_nonzero (b : family.active labels) :
    ∃ ξ, pairedEnergy ((family.leftCalibration b.val).data ξ)
      (family.leftCalibration b.val).parameters (family.leftSource b.val).base
      ((family.leftCalibration b.val).height ξ) ≠ 0 := by
  sorry

theorem active_right_raw_nonzero (b : family.active labels) :
    ∃ ξ, pairedEnergy ((family.rightCalibration b.val).data ξ)
      (family.rightCalibration b.val).parameters (family.rightSource b.val).base
      ((family.rightCalibration b.val).height ξ) ≠ 0 := by
  sorry

end ActualNormalizedPairFamily

/-- The original arithmetic weight sum is left exact. Only the
profile envelope estimate is needed on nonzero original labels. -/
theorem actual_finite_normalized_kernel_mass_active
    (cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ {Λ : Type*} (Z : ℝ) (hZ : 0 < Z),
    ∀ s : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z,
    ∀ (labels : Finset Λ) (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ))
      (outer B₁ B₂ : Λ → ℝ) (parentWidth control : ℝ),
      (∀ b ∈ labels, 0 ≤ outer b) →
      (∀ b ∈ labels, 0 ≤ B₁ b) → (∀ b ∈ labels, 0 ≤ B₂ b) →
      (∀ b ∈ labels, (s.leftSource b).allocation.keep.card ≤ cap) →
      (∀ b ∈ labels, (s.rightSource b).allocation.keep.card ≤ cap) →
      (∀ b ∈ labels, ∀ z,
        (s.leftCapacity b).radius (WithLp.toLp 2 z) = polynomialProfileRadius (B₁ b) J₁₁ J₁₂ z) →
      (∀ b ∈ labels, ∀ z,
        (s.rightCapacity b).radius (WithLp.toLp 2 z) = polynomialProfileRadius (B₂ b) J₂₁ J₂₂ z) →
      (∀ b : s.active labels,
        pairedProfileEnvelopeConstant (B₁ b.val) (B₂ b.val) cap cap *
          seminorms₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b.val) *
            seminorms₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b.val) ≤ control) →
      (∀ b : s.active labels,
        IsFiniteMeasure (s.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : s.active labels,
        (s.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
          C * control * ∑ b : s.active labels, outer b.val * s.weight labels parentWidth b := by
  sorry

namespace CanonicalFullKappaPrime

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}

/-- The fixed coefficient furnished by the original active summand
bounds is used only on the existing active carrier. Inactive sources
retain their actual computed radii without being charged by this sum. -/
theorem actual_finite_kernel_mass_active
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
        (∀ b ∈ labels, 0 ≤ B₁ b) →
        (∀ b ∈ labels, 0 ≤ B₂ b) →
        (∀ b : family.active labels, B₁ b.val ≤ B) →
        (∀ b : family.active labels, B₂ b.val ≤ B) →
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
  sorry

end CanonicalFullKappaPrime
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_finite_normalized_kernel_mass_active
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.actual_finite_kernel_mass_active
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.active_left_raw_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.active_right_raw_nonzero
