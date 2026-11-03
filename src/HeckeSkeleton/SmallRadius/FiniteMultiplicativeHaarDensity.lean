import HeckeSkeleton.SmallRadius.SLocalProductHaarMellin
import FLTReuse.M00c7be4ee0b6591d
import FLTReuse.M2a2f532b3e0b3dc8
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
For the actual finite completion its norm is already the additive-Haar
modulus (the FLT theorem below); no additional local-degree exponent occurs.
The actual density measure restricts away from zero before division by norm.
Its pullback to units is Haar by the existing FLT proof, including existence
of an irreducible in the completion integers. Haar uniqueness supplies a
strictly positive scalar, which is retained in every integral formula.

The physical finite Fourier transform has its original negative sign and
its original division by mu(O_v). No Fourier functional equation is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SLocalRadialHaarDraft.FiniteHaarDensityDraft

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open LanglandsTunnell.TateLocal
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.Arithmetic
open HeckeGeneral.Characters NumberField.AdelicFourier
open scoped NNReal ENNReal Classical

variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))
variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
variable [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
variable (μ : Measure (v.adicCompletion K)) [hμ : μ.IsAddHaarMeasure]

local instance : SecondCountableTopology (v.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

/-- The completion norm is the Haar modulus, including at zero. -/
theorem finite_modulus_eq_nnnorm (x : v.adicCompletion K) :
    modulus x = ‖x‖₊ :=
  LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x

/-- Literal additive density on the punctured completion. -/
def finiteAdditiveDensity : Measure (v.adicCompletion K) :=
  (μ.restrict {0}ᶜ).withDensity (fun x => ((‖x‖₊ : ℝ≥0∞))⁻¹)

theorem finiteAdditiveDensity_eq_mulMeasure :
    finiteAdditiveDensity K v μ = mulMeasure μ := by
  unfold finiteAdditiveDensity mulMeasure
  simp_rw [finite_modulus_eq_nnnorm K v]

/-- Actual density Haar measure, on the actual group of nonzero elements. -/
def finiteDensityHaar : Measure (v.adicCompletion K)ˣ :=
  Measure.comap Units.val (finiteAdditiveDensity K v μ)

include hμ in
instance finiteDensityHaar_isHaar : IsHaarMeasure (finiteDensityHaar K v μ) := by
  obtain ⟨ϖ, hϖ, -⟩ :=
    P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.M4aLocalCFT.ValuedOrdBridge.exists_irreducible_valued
      (F := K) (v := v)
  change IsHaarMeasure (Measure.comap Units.val (finiteAdditiveDensity K v μ))
  rw [finiteAdditiveDensity_eq_mulMeasure K v μ]
  exact P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.M4aLocalCFT.MulHaarFromAdditive.isHaarMeasure_mulHaar
    μ hϖ

def finiteHaarDensityScalar : ℝ≥0 :=
  haarScalarFactor (Measure.haar : Measure (v.adicCompletion K)ˣ)
    (finiteDensityHaar K v μ)

theorem finiteHaarDensityScalar_pos : 0 < finiteHaarDensityScalar K v μ :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

theorem finiteHaar_eq_smul_density :
    (Measure.haar : Measure (v.adicCompletion K)ˣ) =
      finiteHaarDensityScalar K v μ • finiteDensityHaar K v μ :=
  isMulLeftInvariant_eq_smul _ _

theorem integral_finiteDensityHaar (f : v.adicCompletion K → ℂ) :
    (∫ u : (v.adicCompletion K)ˣ, f (u : v.adicCompletion K)
      ∂finiteDensityHaar K v μ) = ∫ x, f x ∂mulMeasure μ := by
  have hval :=
    P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.M4aLocalCFT.MulHaarFromAdditive.measurableEmbedding_val
      (F := K) (v := v)
  unfold finiteDensityHaar
  rw [finiteAdditiveDensity_eq_mulMeasure K v μ,
    ← hval.integral_map, hval.map_comap,
    P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.NumberField.TateGlobal.range_units_val,
    P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.NumberField.TateGlobal.mulMeasure_restrict_compl_zero]

theorem integral_finiteHaar_eq_mulMeasure (f : v.adicCompletion K → ℂ) :
    (∫ u : (v.adicCompletion K)ˣ, f (u : v.adicCompletion K)
      ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) =
      ((finiteHaarDensityScalar K v μ : ℝ) : ℂ) * ∫ x, f x ∂mulMeasure μ := by
  rw [finiteHaar_eq_smul_density K v μ, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul, integral_finiteDensityHaar K v μ]

/-- A literal Tate-density integrability proof transfers to default units Haar. -/
theorem integrable_finiteHaar_of_mulMeasure (f : v.adicCompletion K → ℂ)
    (hf : Integrable f (mulMeasure μ)) :
    Integrable (fun u : (v.adicCompletion K)ˣ => f (u : v.adicCompletion K))
      (Measure.haar : Measure (v.adicCompletion K)ˣ) := by
  rw [finiteHaar_eq_smul_density K v μ]
  apply Integrable.smul_measure_nnreal
  change Integrable (fun u : (v.adicCompletion K)ˣ => f (u : v.adicCompletion K))
    (Measure.comap Units.val (finiteAdditiveDensity K v μ))
  rw [finiteAdditiveDensity_eq_mulMeasure K v μ]
  exact
    (P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.NumberField.TateGlobal.integrable_comp_val_comap_mulMeasure_iff
      (P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.M4aLocalCFT.MulHaarFromAdditive.measurableEmbedding_val
        (F := K) (v := v)) μ f).mpr hf

/-- Bochner equality valid also when both integral conventions return zero. -/
theorem integral_mulMeasure_eq_normDensity (f : v.adicCompletion K → ℂ) :
    (∫ x, f x ∂mulMeasure μ) =
      ∫ x in ({0}ᶜ : Set (v.adicCompletion K)), (‖x‖₊⁻¹ : ℝ≥0) • f x ∂μ := by
  have hae : (fun x : v.adicCompletion K => ((modulus x : ℝ≥0∞))⁻¹)
      =ᵐ[μ.restrict {0}ᶜ]
        (fun x : v.adicCompletion K => ((‖x‖₊⁻¹ : ℝ≥0) : ℝ≥0∞)) := by
    refine (ae_restrict_iff' (MeasurableSet.singleton (0 : v.adicCompletion K)).compl).mpr ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : x ≠ 0 := by simpa using hx
    change ((modulus x : ℝ≥0∞))⁻¹ = ((‖x‖₊⁻¹ : ℝ≥0) : ℝ≥0∞)
    rw [finite_modulus_eq_nnnorm K v, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hx0)]
  rw [mulMeasure, withDensity_congr_ae hae]
  have hdensity : AEMeasurable (fun x : v.adicCompletion K => ‖x‖₊⁻¹)
      (μ.restrict {0}ᶜ) := measurable_nnnorm.inv.aemeasurable
  exact integral_withDensity_eq_integral_smul₀ hdensity f

/-- Multiplicative Haar weight z becomes additive Haar weight z-1. -/
theorem integral_finiteHaar_weighted (f : v.adicCompletion K → ℂ) (z : ℂ) :
    (∫ u : (v.adicCompletion K)ˣ,
        f (u : v.adicCompletion K) * (‖(u : v.adicCompletion K)‖ : ℂ) ^ z
        ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) =
      ((finiteHaarDensityScalar K v μ : ℝ) : ℂ) *
        ∫ x in ({0}ᶜ : Set (v.adicCompletion K)),
          f x * (‖x‖ : ℂ) ^ (z - 1) ∂μ := by
  rw [finiteHaar_eq_smul_density K v μ, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul,
    integral_finiteDensityHaar K v μ (fun x => f x * (‖x‖ : ℂ) ^ z),
    integral_mulMeasure_eq_normDensity K v μ]
  congr 1
  apply setIntegral_congr_fun (MeasurableSet.singleton (0 : v.adicCompletion K)).compl
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hn : (‖x‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx0)
  change ‖x‖₊⁻¹ • (f x * (‖x‖ : ℂ) ^ z) = f x * (‖x‖ : ℂ) ^ (z - 1)
  rw [Complex.cpow_sub z 1 hn, Complex.cpow_one]
  simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
    coe_nnnorm, Complex.ofReal_inv]
  ring

section PhysicalFactor

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ]
variable (μf : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μf p).IsAddHaarMeasure]

/-- Exact physical factor: negative Fourier kernel and mu(O_v) inverse remain. -/
theorem integral_weightedFiniteFourierFactor
    (W : AdditiveProbeTest K S) (z : ℂ) (p : S) :
    (∫ u : (p.val.adicCompletion K)ˣ,
      weightedFiniteFourierFactor K S μf W z p u
      ∂(Measure.haar : Measure (p.val.adicCompletion K)ˣ)) =
    ((finiteHaarDensityScalar K p.val (μf p) : ℝ) : ℂ) *
      ∫ x in ({0}ᶜ : Set (p.val.adicCompletion K)),
        (((μf p).real
          (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) : ℂ))⁻¹ *
          fourierIntegral (StandardAddChar.psiLocal K p.val) (μf p) (W.finiteTest p) x *
          (‖x‖ : ℂ) ^ (z - 1) ∂μf p := by
  unfold weightedFiniteFourierFactor
  exact integral_finiteHaar_weighted K p.val (μf p)
    (fun x => (((μf p).real
      (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) : ℂ))⁻¹ *
      fourierIntegral (StandardAddChar.psiLocal K p.val) (μf p) (W.finiteTest p) x) z

end PhysicalFactor

end HeckeGeneral.Analysis.SLocalRadialHaarDraft.FiniteHaarDensityDraft
