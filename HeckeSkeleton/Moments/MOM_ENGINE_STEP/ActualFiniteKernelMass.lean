import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityProfileMass

/-!
# Uniform Fourier mass for the same actual finite child family

Each original leaf has its own two original Schwartz kernels and its
literal nonnegative arithmetic weight. The profile radius is the actual
polynomial radius used to normalize that leaf. The finite family removes
only source pairs that vanish identically, before either Fourier
parameter. The theorem below integrates the exact common density of
every retained leaf and bounds the total by its exact arithmetic sum.

The only profile bound is a bound on the two individual original
Schwartz seminorms and their radius constants. The theorem does not take
a child moment estimate, a total Fourier mass, or a final arithmetic
mass bound as an input.
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

def actualNestedLabelMeasure {Λ : Type*}
    (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ) (b : Λ) :
    Measure (WithLp 2 (U × E)) :=
  ENNReal.ofReal (outer b) •
    Measure.map (WithLp.toLp 2) (nestedFourierMeasure (F₁ b) (F₂ b))

namespace ActualNormalizedPairFamily

variable {Λ : Type*} {Z : ℝ}
variable (s : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
variable (labels : Finset Λ)

theorem kernel_actualNestedLabelMeasure
    (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ)
    (parentWidth : ℝ) (b : s.active labels) :
    s.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b =
      ENNReal.ofReal (outer b.val) •
        normalizedCapacityPairKernel
          (Measure.map (WithLp.toLp 2) (nestedFourierMeasure (F₁ b.val) (F₂ b.val)))
          (s.leftChild labels b) (s.rightChild labels b)
          (s.leftNormalizer b.val) (s.rightNormalizer b.val) Z parentWidth :=
  normalizedCapacityPairKernel_smul_measure _ _ _ _ _ _ _ _

end ActualNormalizedPairFamily

/-- The finite seminorm orders and Fourier constant are chosen before
all moving source families, labels, profiles, scales and child choices.
The remaining sum is the literal arithmetic weight of these children. -/
theorem actual_finite_normalized_kernel_mass
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
      (∀ b ∈ labels,
        pairedProfileEnvelopeConstant (B₁ b) (B₂ b) cap cap *
          seminorms₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b) *
            seminorms₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b) ≤ control) →
      (∀ b : s.active labels,
        IsFiniteMeasure (s.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : s.active labels,
        (s.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
          C * control * ∑ b : s.active labels, outer b.val * s.weight labels parentWidth b := by
  obtain ⟨seminorms₁, seminorms₂, C, hC, hm⟩ :=
    normalized_capacity_nested_kernel_uniform_mass (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      (U := U) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂
  refine ⟨seminorms₁, seminorms₂, C, hC, ?_⟩
  intro Λ Z hZ s labels F₁ F₂ outer B₁ B₂ parentWidth control
    houter hB₁ hB₂ hcapL hcapR hradiusL hradiusR hprofiles
  have hb (b : s.active labels) : b.val ∈ labels := (Finset.mem_filter.mp b.property).1
  have hsingle (b : s.active labels) :=
    hm (F₁ b.val) (F₂ b.val) (B₁ b.val) (B₂ b.val)
      (hB₁ b.val (hb b)) (hB₂ b.val (hb b))
      (s.leftSource b.val) (s.rightSource b.val)
      (s.leftCalibration b.val) (s.rightCalibration b.val)
      (s.leftCapacity b.val) (s.rightCapacity b.val)
      (hcapL b.val (hb b)) (hcapR b.val (hb b))
      (hradiusL b.val (hb b)) (hradiusR b.val (hb b))
      (s.leftChild labels b) (s.rightChild labels b)
      (s.leftNormalizer b.val) (s.rightNormalizer b.val) Z parentWidth hZ
  constructor
  · intro b
    rw [s.kernel_actualNestedLabelMeasure labels F₁ F₂ outer parentWidth b]
    letI := (hsingle b).1
    infer_instance
  · calc
      _ ≤ ∑ b : s.active labels,
          C * control * (outer b.val * s.weight labels parentWidth b) := by
        apply Finset.sum_le_sum
        intro b _
        rw [s.kernel_actualNestedLabelMeasure labels F₁ F₂ outer parentWidth b]
        change (ENNReal.ofReal (outer b.val) * _).toReal ≤ _
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (houter b.val (hb b))]
        calc
          _ ≤ outer b.val *
              (s.weight labels parentWidth b *
                pairedProfileEnvelopeConstant (B₁ b.val) (B₂ b.val) cap cap * C *
                  seminorms₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b.val) *
                    seminorms₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b.val)) :=
            mul_le_mul_of_nonneg_left (hsingle b).2 (houter b.val (hb b))
          _ = (outer b.val * s.weight labels parentWidth b) * C *
              (pairedProfileEnvelopeConstant (B₁ b.val) (B₂ b.val) cap cap *
                seminorms₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b.val) *
                  seminorms₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b.val)) := by ring
          _ ≤ (outer b.val * s.weight labels parentWidth b) * C * control :=
            mul_le_mul_of_nonneg_left (hprofiles b.val (hb b))
              (mul_nonneg (mul_nonneg (houter b.val (hb b))
                (s.weight_nonneg labels parentWidth b hZ)) hC.le)
          _ = _ := by ring
      _ = _ := (Finset.mul_sum _ _ _).symm

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_finite_normalized_kernel_mass
