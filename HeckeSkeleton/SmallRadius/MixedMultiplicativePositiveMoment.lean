import HeckeSkeleton.SmallRadius.MixedPositiveMomentSeminorm
import HeckeSkeleton.SmallRadius.TotallyComplexMixedHaarProduct
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
Actual multiplicative Haar positive moments for
arbitrary mixed Schwartz inputs over a totally complex number field.

The auxiliary complex-unit Borel structure is fixed to its actual Borel
sigma algebra. The actual mixed-unit Borel structure may be any compatible
one. All Haar comparisons retain their genuinely constructed positive
scalars. No value of such a scalar is asserted to be one.

The single-complex envelope is transported through the punctured additive
density before taking a finite product. Only the envelope is a product;
the Schwartz input is arbitrary. The original finite seminorm family and
positive bound are chosen before that input. The actual mixed norm, whose
complex factors are squared norms, is used literally in the conclusion.
-/

noncomputable section

namespace HeckeGeneral.Analysis.MixedPositiveHaarDraft

open NumberField NumberField.InfinitePlace HeckeGeneral.Arithmetic MeasureTheory
open MixedPositiveMomentDraft SmallPositiveArchimedeanMomentDraft
open SLocalRadialHaarDraft SLocalRadialHaarDraft.ComplexHaarDensityDraft
open SLocalRadialHaarDraft.TotallyComplexHaarDraft
open scoped Classical BigOperators ENNReal NNReal

local instance complexUnitsMeasurableSpace : MeasurableSpace ℂˣ := borel ℂˣ
local instance complexUnitsBorelSpace : BorelSpace ℂˣ := ⟨rfl⟩
local instance complexUnitsSecondCountable : SecondCountableTopology ℂˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

/-- The fixed complex multiplicative envelope, with the actual modulus weight. -/
def complexUnitEnvelope (σ : ℝ) (u : ℂˣ) : ℝ :=
  (1 + ‖(u : ℂ)‖) ^ (-3 : ℝ) * ‖(u : ℂ)‖ ^ (2 * σ)

theorem complexUnitEnvelope_nonneg (σ : ℝ) (u : ℂˣ) :
    0 ≤ complexUnitEnvelope σ u := by
  unfold complexUnitEnvelope
  positivity

/-- Integrability includes the approach to zero; separation from zero is
not assumed. The complex Haar density and its normalizing scalar are real. -/
theorem integrable_complexUnitEnvelope (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (complexUnitEnvelope σ) (Measure.haar : Measure ℂˣ) := by
  let f : ℂ → ℝ := fun z => (1 + ‖z‖) ^ (-3 : ℝ) * ‖z‖ ^ (2 * σ)
  have hlocal : Integrable
      (fun z : ℂ => (1 + ‖z‖) ^ (-3 : ℝ) * ‖z‖ ^ (2 * σ - 2)) volume := by
    simpa only [Complex.finrank_real_complex, Nat.cast_ofNat, mul_sub, mul_one] using
      integrable_small_positive_moment_envelope (E := ℂ)
        (by norm_num [Complex.finrank_real_complex]) 3
        (by norm_num [Complex.finrank_real_complex]) σ hσ hσ1
  have hae : (fun z : ℂ => ((‖z‖₊ ^ 2 : ℝ≥0∞))⁻¹)
      =ᵐ[(volume : Measure ℂ).restrict {0}ᶜ]
        fun z : ℂ => (((‖z‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem (MeasurableSet.singleton (0 : ℂ)).compl] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hn0 : ‖z‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hz0
    simpa only [ENNReal.coe_pow] using (ENNReal.coe_inv (pow_ne_zero 2 hn0)).symm
  have hm : Measurable (fun z : ℂ => (‖z‖₊ ^ 2)⁻¹) :=
    (measurable_nnnorm.pow_const 2).inv
  have hdensity : Integrable f complexAdditiveDensity := by
    unfold complexAdditiveDensity
    rw [withDensity_congr_ae hae]
    apply (integrable_withDensity_iff_integrable_smul hm).mpr
    apply hlocal.integrableOn.congr
    filter_upwards [ae_restrict_mem (MeasurableSet.singleton (0 : ℂ)).compl] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    simp only [NNReal.smul_def, NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm, f]
    rw [Real.rpow_sub hn, Real.rpow_two]
    simp only [div_eq_mul_inv]
    ring
  have hval : MeasurableEmbedding (Units.val : ℂˣ → ℂ) :=
    Units.isOpenEmbedding_val.measurableEmbedding
  have hcomap : Integrable (complexUnitEnvelope σ) complexDensityHaar := by
    change Integrable (f ∘ Units.val) (Measure.comap Units.val complexAdditiveDensity)
    rw [← hval.integrable_map_iff, hval.map_comap,
      P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.NumberField.TateGlobal.range_units_val]
    exact hdensity.integrableOn
  rw [complexHaar_eq_smul_density]
  exact hcomap.smul_measure_nnreal

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K

local instance realCoordsEmpty : IsEmpty (RealCoord K) :=
  ⟨fun v => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.val)) v.prop⟩

variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]

local instance mixedUnitsSecondCountable : SecondCountableTopology Wˣ := by
  letI : SecondCountableTopology Wᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-- This fixed envelope is measured with the actual default mixed-unit Haar. -/
def mixedHaarEnvelope (σ : ℝ) (u : Wˣ) : ℝ :=
  ∏ v : ComplexPlace K, complexUnitEnvelope σ (mixedComplexUnitsEquiv K u v)

theorem mixedHaarEnvelope_nonneg (σ : ℝ) (u : Wˣ) :
    0 ≤ mixedHaarEnvelope K σ u := by
  exact Finset.prod_nonneg fun _ _ => complexUnitEnvelope_nonneg _ _

/-- The literal mixed norm weight is the product of complex squared-modulus weights. -/
theorem mixedNorm_rpow_complexProduct (σ : ℝ) (u : Wˣ) :
    (mixedEmbedding.norm (u : W)) ^ σ =
      ∏ v : ComplexPlace K, ‖(mixedComplexUnitsEquiv K u v : ℂ)‖ ^ (2 * σ) := by
  have ht (t : ComplexPlace K → ℂˣ) :
      (mixedEmbedding.norm ((mixedComplexUnitsEquiv K).symm t : W)) ^ σ =
        ∏ v : ComplexPlace K, ‖(t v : ℂ)‖ ^ (2 * σ) := by
    rw [mixedNorm_symm_complexUnits]
    rw [← Real.finsetProd_rpow Finset.univ
      (fun v : ComplexPlace K => ‖(t v : ℂ)‖ ^ 2) (fun _ _ => sq_nonneg _) σ]
    apply Finset.prod_congr rfl
    intro v _
    simpa only [Real.rpow_two] using
      (Real.rpow_mul (norm_nonneg (t v : ℂ)) 2 σ).symm
  simpa only [ContinuousMulEquiv.symm_apply_apply] using ht (mixedComplexUnitsEquiv K u)

theorem mixedHaarEnvelope_eq_decay_weight (σ : ℝ) (u : Wˣ) :
    mixedHaarEnvelope K σ u =
      mixedArchDecay K (u : W) * (mixedEmbedding.norm (u : W)) ^ σ := by
  rw [mixedNorm_rpow_complexProduct]
  have hreal : (∏ v : RealCoord K, (1 + ‖(u : W).1 v‖) ^ (-3 : ℝ)) = 1 := by simp
  simp only [mixedHaarEnvelope, complexUnitEnvelope, mixedArchDecay,
    mixedComplexUnitsEquiv_apply, hreal, one_mul, Finset.prod_mul_distrib]

/-- Finite-product integrability transports through the actual topological
unit equivalence and the constructed mixed Haar comparison scalar. -/
theorem integrable_mixedHaarEnvelope (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (mixedHaarEnvelope K σ) (mixedMultiplicativeHaar K) := by
  have hpi : Integrable
      (fun t : ComplexPlace K → ℂˣ => ∏ v, complexUnitEnvelope σ (t v))
      (complexUnitsProductHaar K) :=
    Integrable.fintype_prod_dep (fun _ => integrable_complexUnitEnvelope σ hσ hσ1)
  rw [mixedMultiplicativeHaar_eq_complexProduct K]
  apply Integrable.smul_measure_nnreal
  have hemb : MeasurableEmbedding
      ((mixedComplexUnitsEquiv K).symm : (ComplexPlace K → ℂˣ) → Wˣ) :=
    (mixedComplexUnitsEquiv K).symm.toHomeomorph.measurableEmbedding
  apply hemb.integrable_map_iff.mpr
  simpa only [Function.comp_def, mixedHaarEnvelope,
    ContinuousMulEquiv.apply_symm_apply] using hpi

/-- The actual absolute mixed test and actual multiplicative norm weight. -/
def mixedWeightedAbsoluteTest (φ : SchwartzMap V ℂ) (σ : ℝ) (u : Wˣ) : ℝ :=
  ‖φ ((traceToMixed K).symm (u : W))‖ * (mixedEmbedding.norm (u : W)) ^ σ

theorem mixedWeightedAbsoluteTest_nonneg (φ : SchwartzMap V ℂ) (σ : ℝ) (u : Wˣ) :
    0 ≤ mixedWeightedAbsoluteTest K φ σ u :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _)

/-- No tensor restriction on phi. The finite original trace-space seminorm
family and bound precede phi. All Haar normalizations remain in the actual
fixed envelope integral used to construct the positive constant. -/
theorem exists_mixed_multiplicative_positive_moment_seminorm_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap V ℂ,
      Integrable (mixedWeightedAbsoluteTest K φ σ) (mixedMultiplicativeHaar K) ∧
      (∫ u : Wˣ, mixedWeightedAbsoluteTest K φ σ u ∂mixedMultiplicativeHaar K) ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s, A, hA, hmajor⟩ := exists_trace_mixed_product_majorant K
  have henv := integrable_mixedHaarEnvelope K σ hσ hσ1
  have hI : 0 ≤ ∫ u, mixedHaarEnvelope K σ u ∂mixedMultiplicativeHaar K :=
    integral_nonneg (mixedHaarEnvelope_nonneg K σ)
  refine ⟨s, A * ((∫ u, mixedHaarEnvelope K σ u ∂mixedMultiplicativeHaar K) + 1),
    by positivity, ?_⟩
  intro φ
  let B : ℝ := A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpoint (u : Wˣ) : mixedWeightedAbsoluteTest K φ σ u ≤ B * mixedHaarEnvelope K σ u := by
    rw [mixedWeightedAbsoluteTest, mixedHaarEnvelope_eq_decay_weight]
    calc
      _ ≤ (A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * mixedArchDecay K (u : W)) *
          (mixedEmbedding.norm (u : W)) ^ σ :=
        mul_le_mul_of_nonneg_right (hmajor φ (u : W))
          (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _)
      _ = _ := by dsimp only [B]; ring
  have hmeas : AEStronglyMeasurable (mixedWeightedAbsoluteTest K φ σ)
      (mixedMultiplicativeHaar K) := by
    have hm : Measurable (fun u : Wˣ => mixedEmbedding.norm (u : W)) :=
      ((mixedEmbedding.continuous_norm K).comp Units.continuous_val).measurable
    exact (((φ.continuous.comp ((traceToMixed K).symm.continuous.comp
      Units.continuous_val)).norm.measurable).mul (hm.pow_const σ)).aestronglyMeasurable
  have hint : Integrable (mixedWeightedAbsoluteTest K φ σ) (mixedMultiplicativeHaar K) := by
    apply (henv.const_mul B).mono' hmeas
    exact Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mixedWeightedAbsoluteTest_nonneg K φ σ u)]
      exact hpoint u
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ u : Wˣ, B * mixedHaarEnvelope K σ u ∂mixedMultiplicativeHaar K :=
      integral_mono hint (henv.const_mul B) hpoint
    _ = B * ∫ u : Wˣ, mixedHaarEnvelope K σ u ∂mixedMultiplicativeHaar K :=
      integral_const_mul _ _
    _ ≤ B * ((∫ u : Wˣ, mixedHaarEnvelope K σ u ∂mixedMultiplicativeHaar K) + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hB
    _ = _ := by dsimp only [B]; ring

end HeckeGeneral.Analysis.MixedPositiveHaarDraft
