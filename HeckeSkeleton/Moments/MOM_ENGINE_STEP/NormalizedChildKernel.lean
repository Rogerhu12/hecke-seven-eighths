import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedCapacityChild
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstWeightedReduction

/-!
# The exact profile-weighted kernel of normalized capacity children

The profile density uses each side's live slot count before deletion.
The scalar factor contains each original Gauss normalizer, source mass,
fixed deletion cost and child-width normalization once.  This separates
the exact finite arithmetic weight from the integrable Fourier envelope.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V HL HR : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k l : ℕ}
variable {sL : ActualAllocatedSource A V HL k} {sR : ActualAllocatedSource A V HR l}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {«GL» : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}

def normalizedCapacityPairWeight (left : «GL».Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) : ℝ :=
  ‖originalLeft‖ * ‖originalRight‖ * Real.sqrt left.weight * Real.sqrt right.weight *
    Real.sqrt (Z ^ (left.parameters.m + left.parameters.q)) *
      Real.sqrt (Z ^ (right.parameters.m + right.parameters.q)) / Z ^ parentWidth

def normalizedCapacityPairEnvelope («GL» : DL.NormalizedCapacityData)
    (GR : DR.NormalizedCapacityData) (ξ : V) : ℝ :=
  («GL».radius ξ) ^ (sL.allocation.keep.card + 2) *
    (GR.radius ξ) ^ (sR.allocation.keep.card + 2)

theorem normalizedCapacityPairWeight_nonneg (left : «GL».Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) (hZ : 0 < Z) :
    0 ≤ normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth := by
  unfold normalizedCapacityPairWeight
  positivity

theorem normalizedCapacityPairEnvelope_nonneg (ξ : V) :
    0 ≤ normalizedCapacityPairEnvelope «GL» GR ξ :=
  mul_nonneg (pow_nonneg («GL».radius_pos ξ).le _) (pow_nonneg (GR.radius_pos ξ).le _)

private theorem sqrt_energy_normalization
    (d : MomentData F ω ψ) (a : RealParameters) (Z t : ℝ) (hZ : 0 < Z) :
    Real.sqrt (pairedEnergy d a Z t) =
      Real.sqrt (Z ^ (a.m + a.q)) * Real.sqrt (normalizedPairedEnergy d a Z t) := by
  rw [← Real.sqrt_mul (Real.rpow_pos_of_pos hZ _).le]
  congr 1
  unfold normalizedPairedEnergy
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hZ (a.m + a.q))]

theorem normalized_capacity_pair_pointwise
    (left : «GL».Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) (hZ : 0 < Z)
    (hleft : sL.base = Z) (hright : sR.base = Z) (ξ : V) :
    (Real.sqrt (‖originalLeft‖ ^ 2 * sL.energy (σ := σ) ξ) *
      Real.sqrt (‖originalRight‖ ^ 2 * sR.energy (σ := σ) ξ)) / Z ^ parentWidth ≤
      normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth *
        normalizedCapacityPairEnvelope «GL» GR ξ *
        (Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) *
          Real.sqrt (normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ))) := by
  have hl := left.sqrt_energy_le ξ
  have hr := right.sqrt_energy_le ξ
  rw [hleft] at hl
  rw [hright] at hr
  rw [sqrt_energy_normalization _ _ _ _ hZ] at hl hr
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
  have hBL : 0 ≤ «GL».radius ξ := («GL».radius_pos ξ).le
  have hleftBound : 0 ≤ ‖originalLeft‖ *
      (Real.sqrt left.weight * («GL».radius ξ) ^ (sL.allocation.keep.card + 2) *
        (Real.sqrt (Z ^ (left.parameters.m + left.parameters.q)) *
          Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)))) := by
    positivity
  apply (div_le_div_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hl (norm_nonneg originalLeft))
      (mul_le_mul_of_nonneg_left hr (norm_nonneg originalRight))
      (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hleftBound)
    (Real.rpow_pos_of_pos hZ _).le).trans_eq
  unfold normalizedCapacityPairWeight normalizedCapacityPairEnvelope
  ring

variable [MeasurableSpace V]

def normalizedCapacityPairKernel (μ : Measure V) (left : «GL».Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) : Measure V :=
  ENNReal.ofReal (normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth) •
    μ.withDensity (fun ξ => ENNReal.ofReal (normalizedCapacityPairEnvelope «GL» GR ξ))

theorem normalizedCapacityPairKernel_finite (μ : Measure V)
    (left : «GL».Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ)
    (hprofile : Integrable (normalizedCapacityPairEnvelope «GL» GR) μ) :
    IsFiniteMeasure (normalizedCapacityPairKernel μ left right originalLeft originalRight Z parentWidth) := by
  haveI : IsFiniteMeasure (μ.withDensity
      (fun ξ => ENNReal.ofReal (normalizedCapacityPairEnvelope «GL» GR ξ))) := by
    apply isFiniteMeasure_withDensity
    exact ((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun ξ => normalizedCapacityPairEnvelope_nonneg («GL» := «GL») (GR := GR) ξ))).mp
        hprofile.hasFiniteIntegral).ne
  unfold normalizedCapacityPairKernel
  infer_instance

theorem normalizedCapacityPairKernel_mass (μ : Measure V)
    (left : «GL».Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) (hZ : 0 < Z)
    (hprofile : AEStronglyMeasurable (normalizedCapacityPairEnvelope «GL» GR) μ) :
    (normalizedCapacityPairKernel μ left right originalLeft originalRight Z parentWidth).real Set.univ =
      normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth *
        ∫ ξ, normalizedCapacityPairEnvelope «GL» GR ξ ∂μ := by
  rw [normalizedCapacityPairKernel]
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (normalizedCapacityPairWeight_nonneg left right originalLeft originalRight Z parentWidth hZ)]
  rw [density_univ_eq_lintegral]
  congr 1
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun ξ => normalizedCapacityPairEnvelope_nonneg («GL» := «GL») (GR := GR) ξ))
    hprofile).symm

theorem normalizedCapacityPairKernel_integral (μ : Measure V)
    (left : «GL».Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) (hZ : 0 < Z)
    (hprofile : Measurable (normalizedCapacityPairEnvelope «GL» GR)) (f : V → ℝ) :
    (∫ ξ, f ξ ∂normalizedCapacityPairKernel μ left right originalLeft originalRight Z parentWidth) =
      normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth *
        ∫ ξ, normalizedCapacityPairEnvelope «GL» GR ξ * f ξ ∂μ := by
  rw [normalizedCapacityPairKernel, integral_smul_measure, ENNReal.toReal_ofReal
    (normalizedCapacityPairWeight_nonneg left right originalLeft originalRight Z parentWidth hZ), smul_eq_mul]
  congr 1
  simpa only [ENNReal.toReal_ofReal (normalizedCapacityPairEnvelope_nonneg («GL» := «GL») (GR := GR) _),
    smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul hprofile.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ : V => ENNReal.ofReal_lt_top) f

theorem normalized_capacity_pair_integral
    (μ : Measure V) (left : «GL».Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) (hZ : 0 < Z)
    (hleft : sL.base = Z) (hright : sR.base = Z)
    (hprofile : Measurable (normalizedCapacityPairEnvelope «GL» GR))
    (hsource : Integrable (fun ξ =>
      (Real.sqrt (‖originalLeft‖ ^ 2 * sL.energy (σ := σ) ξ) *
        Real.sqrt (‖originalRight‖ ^ 2 * sR.energy (σ := σ) ξ)) / Z ^ parentWidth) μ)
    (hchild : Integrable (fun ξ => normalizedCapacityPairEnvelope «GL» GR ξ *
      (Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) *
        Real.sqrt (normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ)))) μ) :
    (∫ ξ, (Real.sqrt (‖originalLeft‖ ^ 2 * sL.energy (σ := σ) ξ) *
      Real.sqrt (‖originalRight‖ ^ 2 * sR.energy (σ := σ) ξ)) / Z ^ parentWidth ∂μ) ≤
      ∫ ξ,
        Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) *
          Real.sqrt (normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ))
          ∂normalizedCapacityPairKernel μ left right originalLeft originalRight Z parentWidth := by
  rw [normalizedCapacityPairKernel_integral _ _ _ _ _ _ _ hZ hprofile, ← integral_const_mul]
  apply integral_mono hsource (hchild.const_mul _)
  intro ξ
  exact (normalized_capacity_pair_pointwise left right originalLeft originalRight Z parentWidth hZ
    hleft hright ξ).trans_eq (by ring)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.normalized_capacity_pair_pointwise
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedCapacityPairKernel_mass
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_capacity_pair_integral
