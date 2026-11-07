module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9RadiusData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaKernelMass

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fourier integration with the already selected full-kappa radius

The contour and its radius factor are inputs from the normalization
construction.  This file never selects a second contour.  It pays the
whole pre-removal envelope, including both plain profiles on both sides,
and retains the literal outer-times-family-weight sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep CanonicalFullKappaPrime

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

namespace KernelRadiusData

variable {N : NormalizedData call} {cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ} {B radius : ℝ}
variable (D : KernelRadiusData N cap J₁₁ J₁₂ J₂₁ J₂₂ B radius)


theorem envelope_eq (b : N.Active) (z : ℝ × ℝ) :
    normalizedCapacityPairEnvelope (N.family.leftCapacity b.val)
      (N.family.rightCapacity b.val) (WithLp.toLp 2 z) = D.envelope b z := by
  simp only [normalizedCapacityPairEnvelope, envelope, pairedProfileEnvelope,
    D.left_radius, D.right_radius]

theorem envelope_integrable (hradius : 0 ≤ radius) (b : N.Active) :
    Integrable (D.envelope b)
      (nestedFourierMeasure (N.firstKernel b.val) (N.secondKernel b.val)) := by
  have hL := enlargedCoefficient_nonneg (D.left_nonneg b) hradius
  have hR := enlargedCoefficient_nonneg (D.right_nonneg b) hradius
  exact actual_profile_envelope_integrable (N.firstKernel b.val) (N.secondKernel b.val)
    (D.envelope b)
    (pairedProfileEnvelope_continuous _ _ _ _ _ _ _ _).measurable
    (pairedProfileEnvelope_nonneg _ _ hL hR _ _ _ _ _ _)
    (pairedProfileEnvelopeConstant
      (enlargedCoefficient (D.leftCoefficient b.val) radius)
      (enlargedCoefficient (D.rightCoefficient b.val) radius)
      (N.family.leftSource b.val).allocation.keep.card
      (N.family.rightSource b.val).allocation.keep.card)
    (pairedProfileEnvelopeOrder (N.family.leftSource b.val).allocation.keep.card
      (N.family.rightSource b.val).allocation.keep.card J₁₁ J₂₁)
    (pairedProfileEnvelopeOrder (N.family.leftSource b.val).allocation.keep.card
      (N.family.rightSource b.val).allocation.keep.card J₁₂ J₂₂)
    (pairedProfileEnvelope_bound _ _ hL hR _ _ _ _ _ _)

end KernelRadiusData

/-- A uniform Fourier constant for two fixed original Schwartz kernels.
The arbitrary `radius` is not an enlarged free normalizer: the input
records literal equality with every capacity radius, and its same full
power is paid by the displayed N6 bound. -/
theorem fixed_radius_kernel_mass
    (cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (F₁ F₂ : SchwartzMap ℝ ℂ) :
    ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ (call : Call c) (N : NormalizedData call) (B radius radiusCost loss : ℝ),
        0 ≤ B → 1 ≤ radius → 0 ≤ radiusCost →
        radius ^ ((cap + 2) + (cap + 2)) ≤ radiusCost * call.base ^ loss →
        (∀ b, N.firstKernel b = F₁) → (∀ b, N.secondKernel b = F₂) →
        ∀ D : KernelRadiusData N cap J₁₁ J₁₂ J₂₁ J₂₂ B radius,
          (∀ b, Integrable (D.envelope b)
            (nestedFourierMeasure (N.firstKernel b.val) (N.secondKernel b.val))) ∧
          (∀ b : N.Active, IsFiniteMeasure (N.kernel b)) ∧
          N.kernelMass ≤ coefficient * radiusCost *
            (1 + B) ^ ((cap + 2) + (cap + 2)) * call.base ^ loss * N.arithmeticMass := by
  obtain ⟨s₁, s₂, Cf, hCf, hm⟩ := normalized_capacity_nested_kernel_uniform_mass
    (F := K) (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
    (ω := c.family.omega) (ψ := targetCharacter K c) (U := ℝ) (E := ℝ)
    cap J₁₁ J₁₂ J₂₁ J₂₂
  let n := (cap + 2) + (cap + 2)
  let Fbound₁ := 1 + s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) F₁
  let Fbound₂ := 1 + s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) F₂
  have hF₁ : 0 < Fbound₁ := by dsimp only [Fbound₁]; positivity
  have hF₂ : 0 < Fbound₂ := by dsimp only [Fbound₂]; positivity
  refine ⟨Cf * (2 : ℝ) ^ n * Fbound₁ * Fbound₂, by positivity, ?_⟩
  intro call N B radius radiusCost loss hB hradius hcost hpower hkernel₁ hkernel₂ D
  have hradius0 : 0 ≤ radius := zero_le_one.trans hradius
  have hp : (2 * radius) ^ n ≤
      (2 : ℝ) ^ n * radiusCost * call.base ^ loss := by
    have h := mul_le_mul_of_nonneg_left hpower
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    simpa only [mul_pow, mul_assoc] using h
  let control := (2 : ℝ) ^ n * radiusCost * call.base ^ loss *
    (1 + B) ^ n * Fbound₁ * Fbound₂
  have hprofiles : ∀ b : N.Active,
      pairedProfileEnvelopeConstant (enlargedCoefficient (D.leftCoefficient b.val) radius)
        (enlargedCoefficient (D.rightCoefficient b.val) radius) cap cap *
        s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.firstKernel b.val) *
        s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.secondKernel b.val) ≤ control := by
    intro b
    have henv := (paired_envelopeConstant_le (D.leftCoefficient b.val)
      (D.rightCoefficient b.val) radius (D.left_nonneg b) (D.right_nonneg b)
      hradius cap cap).trans
        (mul_le_mul_of_nonneg_left
          (paired_envelopeConstant_le_bound (D.leftCoefficient b.val) (D.rightCoefficient b.val) B
            (D.left_nonneg b) (D.right_nonneg b) (D.left_le b) (D.right_le b) cap cap)
          (pow_nonneg (mul_nonneg (by norm_num) hradius0) _))
    have hseminorm₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.firstKernel b.val) ≤ Fbound₁ := by
      rw [hkernel₁]
      dsimp only [Fbound₁]
      linarith
    have hseminorm₂ : s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.secondKernel b.val) ≤ Fbound₂ := by
      rw [hkernel₂]
      dsimp only [Fbound₂]
      linarith
    have hs₁ : 0 ≤ s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.firstKernel b.val) := by positivity
    have hs₂ : 0 ≤ s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.secondKernel b.val) := by positivity
    calc
      _ ≤ ((2 * radius) ^ n * (1 + B) ^ n) * Fbound₁ * Fbound₂ :=
        mul_le_mul (mul_le_mul henv hseminorm₁ hs₁ (by positivity))
          hseminorm₂ hs₂ (by positivity)
      _ ≤ (((2 : ℝ) ^ n * radiusCost * call.base ^ loss) * (1 + B) ^ n) *
          Fbound₁ * Fbound₂ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hp (pow_nonneg (by linarith) n)) hF₁.le) hF₂.le
      _ = control := rfl
  have hsingle (b : N.Active) :=
    hm (N.firstKernel b.val) (N.secondKernel b.val)
      (enlargedCoefficient (D.leftCoefficient b.val) radius)
      (enlargedCoefficient (D.rightCoefficient b.val) radius)
      (enlargedCoefficient_nonneg (D.left_nonneg b) hradius0)
      (enlargedCoefficient_nonneg (D.right_nonneg b) hradius0)
      (N.family.leftSource b.val) (N.family.rightSource b.val)
      (N.family.leftCalibration b.val) (N.family.rightCalibration b.val)
      (N.family.leftCapacity b.val) (N.family.rightCapacity b.val)
      (D.left_slots b) (D.right_slots b) (D.left_radius b) (D.right_radius b)
      (N.family.leftChild N.labels b) (N.family.rightChild N.labels b)
      (N.family.leftNormalizer b.val) (N.family.rightNormalizer b.val)
      call.base N.parentWidth call.base_pos
  have hfinite (b : N.Active) : IsFiniteMeasure (N.kernel b) := by
    rw [NormalizedData.kernel, N.family.kernel_actualNestedLabelMeasure]
    letI := (hsingle b).1
    exact Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hmass : N.kernelMass ≤ Cf * control * N.arithmeticMass := by
    change (∑ b : N.Active, (N.kernel b).real Set.univ) ≤ _
    calc
      _ ≤ ∑ b : N.Active,
          Cf * control * (N.outer b.val * N.family.weight N.labels N.parentWidth b) := by
        apply Finset.sum_le_sum
        intro b _
        rw [NormalizedData.kernel, N.family.kernel_actualNestedLabelMeasure]
        change (ENNReal.ofReal (N.outer b.val) * _).toReal ≤ _
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (N.outer_nonneg b.val)]
        calc
          _ ≤ N.outer b.val *
              (N.family.weight N.labels N.parentWidth b *
                pairedProfileEnvelopeConstant (enlargedCoefficient (D.leftCoefficient b.val) radius)
                  (enlargedCoefficient (D.rightCoefficient b.val) radius) cap cap * Cf *
                s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.firstKernel b.val) *
                s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.secondKernel b.val)) :=
            mul_le_mul_of_nonneg_left (hsingle b).2 (N.outer_nonneg b.val)
          _ = (N.outer b.val * N.family.weight N.labels N.parentWidth b) * Cf *
              (pairedProfileEnvelopeConstant (enlargedCoefficient (D.leftCoefficient b.val) radius)
                (enlargedCoefficient (D.rightCoefficient b.val) radius) cap cap *
                s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.firstKernel b.val) *
                s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) (N.secondKernel b.val)) := by ring
          _ ≤ (N.outer b.val * N.family.weight N.labels N.parentWidth b) * Cf * control :=
            mul_le_mul_of_nonneg_left (hprofiles b)
              (mul_nonneg (mul_nonneg (N.outer_nonneg b.val)
                (N.family.weight_nonneg N.labels N.parentWidth b call.base_pos)) hCf.le)
          _ = _ := by ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  refine ⟨fun b => D.envelope_integrable hradius0 b, hfinite, hmass.trans_eq ?_⟩
  dsimp only [control, n, NormalizedData.arithmeticMass]
  ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.KernelRadiusData.envelope_integrable
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.fixed_radius_kernel_mass
