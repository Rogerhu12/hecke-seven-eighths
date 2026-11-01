import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRadiusBound

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
  obtain ⟨ξ, hξ⟩ := not_forall.mp (Finset.mem_filter.mp b.property).2.1
  refine ⟨ξ, ?_⟩
  intro he
  have h := (family.leftCalibration b.val).energy_le ξ
  rw [he, mul_zero] at h
  exact hξ (le_antisymm h ((family.leftSource b.val).energy_nonneg (σ := σ) ξ))

theorem active_right_raw_nonzero (b : family.active labels) :
    ∃ ξ, pairedEnergy ((family.rightCalibration b.val).data ξ)
      (family.rightCalibration b.val).parameters (family.rightSource b.val).base
      ((family.rightCalibration b.val).height ξ) ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := not_forall.mp (Finset.mem_filter.mp b.property).2.2
  refine ⟨ξ, ?_⟩
  intro he
  have h := (family.rightCalibration b.val).energy_le ξ
  rw [he, mul_zero] at h
  exact hξ (le_antisymm h ((family.rightSource b.val).energy_nonneg (σ := σ) ξ))

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
            mul_le_mul_of_nonneg_left (hprofiles b)
              (mul_nonneg (mul_nonneg (houter b.val (hb b))
                (s.weight_nonneg labels parentWidth b hZ)) hC.le)
          _ = _ := by ring
      _ = _ := (Finset.mul_sum _ _ _).symm

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
  let N := (cap + 2) + (cap + 2)
  obtain ⟨δ, Cr, hδ, hδhi, hCr, hr⟩ := exists_complete_profile_radius_bound
    A N h ε lengthBound (CanonicalHeckePrimeAnalytic.degreeBound K) H₀ widthBound
    hε CanonicalHeckePrimeAnalytic.degreeBound_pos.le hwidth
  obtain ⟨s₁, s₂, Cf, hCf, hm⟩ := actual_finite_normalized_kernel_mass_active
    (F := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := U) (E := E)
    cap J₁₁ J₁₂ J₂₁ J₂₂
  refine ⟨s₁, s₂, δ, Cf * (2 * Cr) ^ N, hδ, hδhi,
    mul_pos hCf (pow_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hCr)) _), ?_⟩
  intro Z T width height hZ hT hbox hheight Λ family labels F₁ F₂ outer B₁ B₂
    parentWidth B Fbound₁ Fbound₂ hB hF₁ hF₂ houter hB₁ hB₂ hboundL hboundR hcapL hcapR hradL hradR
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
  have hprofiles : ∀ b : family.active labels,
      pairedProfileEnvelopeConstant (enlargedCoefficient (B₁ b.val) R)
        (enlargedCoefficient (B₂ b.val) R) cap cap *
        s₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b.val) *
        s₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b.val) ≤ control := by
    intro b
    have hb : b.val ∈ labels := (Finset.mem_filter.mp b.property).1
    have henv := (paired_envelopeConstant_le (B₁ b.val) (B₂ b.val) R
      (hB₁ b.val hb) (hB₂ b.val hb) hR cap cap).trans
        (mul_le_mul_of_nonneg_left
          (paired_envelopeConstant_le_bound (B₁ b.val) (B₂ b.val) B
            (hB₁ b.val hb) (hB₂ b.val hb) (hboundL b) (hboundR b) cap cap)
          (pow_nonneg (mul_nonneg (by norm_num) hR0) _))
    have hs₁ : 0 ≤ s₁.sup (schwartzSeminormFamily ℝ U ℂ) (F₁ b.val) := by positivity
    have hs₂ : 0 ≤ s₂.sup (schwartzSeminormFamily ℝ E ℂ) (F₂ b.val) := by positivity
    calc
      _ ≤ ((2 * R) ^ N * (1 + B) ^ N) * Fbound₁ * Fbound₂ :=
        mul_le_mul
          (mul_le_mul henv (hkernel₁ b.val hb) hs₁ (by positivity))
          (hkernel₂ b.val hb) hs₂ (by positivity)
      _ ≤ (((2 * Cr) ^ N * (1 + T) ^ (h * N) * Z ^ ε) * (1 + B) ^ N) *
          Fbound₁ * Fbound₂ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hRp (pow_nonneg (by linarith) N)) hF₁) hF₂
      _ = control := by dsimp only [control]; ring
  have hout := hm Z (zero_lt_one.trans_le hZ) family labels F₁ F₂ outer
    (fun b => enlargedCoefficient (B₁ b) R) (fun b => enlargedCoefficient (B₂ b) R)
    parentWidth control houter
    (fun b hb => enlargedCoefficient_nonneg (hB₁ b hb) hR0)
    (fun b hb => enlargedCoefficient_nonneg (hB₂ b hb) hR0)
    hcapL hcapR hradL hradR hprofiles
  refine ⟨hout.1, hout.2.trans_eq ?_⟩
  dsimp only [control, N]
  ring

end CanonicalFullKappaPrime
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_finite_normalized_kernel_mass_active
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.actual_finite_kernel_mass_active
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.active_left_raw_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.active_right_raw_nonzero
