import HeckeSkeleton.SmallRadius.SLocalRadialMellinIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
A concrete product of actual multiplicative Haar measures, and factorization
of the literal physical Fourier-weighted integrand. Each finite Fourier
factor retains the physical division by its additive Haar mass of O_v.
Local weighted integrability is explicit; no local Fourier/Riesz identity
or desired nonzero moment is assumed or concluded here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SLocalRadialHaarDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton.Physical
open NumberField.AdelicFourier HeckeGeneral.Characters
open MeasureTheory MeasureTheory.Measure
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

-- Supply second countability of each factor explicitly for Haar Fubini.
local instance : SecondCountableTopology (mixedEmbedding.mixedSpace K)ˣ := by
  letI : SecondCountableTopology (mixedEmbedding.mixedSpace K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
  [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ]

def mixedMultiplicativeHaar : Measure (mixedEmbedding.mixedSpace K)ˣ := Measure.haar

def finiteMultiplicativeHaar : Measure ((p : S) → (p.val.adicCompletion K)ˣ) :=
  Measure.pi (fun p : S => (Measure.haar : Measure (p.val.adicCompletion K)ˣ))

def sLocalProductMultiplicativeHaar : Measure (sLocalMultiplicativeGroup K S) :=
  (mixedMultiplicativeHaar K).prod (finiteMultiplicativeHaar K S)

instance mixedMultiplicativeHaar_isHaar : IsHaarMeasure (mixedMultiplicativeHaar K) := by
  unfold mixedMultiplicativeHaar
  infer_instance

instance finiteMultiplicativeHaar_isHaar : IsHaarMeasure (finiteMultiplicativeHaar K S) := by
  unfold finiteMultiplicativeHaar
  infer_instance

instance sLocalProductMultiplicativeHaar_isHaar :
    IsHaarMeasure (sLocalProductMultiplicativeHaar K S) := by
  letI : SigmaFinite (mixedMultiplicativeHaar K) := by
    unfold mixedMultiplicativeHaar
    infer_instance
  letI : SigmaFinite (finiteMultiplicativeHaar K S) := by
    unfold finiteMultiplicativeHaar
    infer_instance
  unfold sLocalProductMultiplicativeHaar
  infer_instance

theorem radialMeasure_eq_positiveScalar_productHaar :
    sLocalRadialMeasure K S =
      radialHaarScalar K S (sLocalProductMultiplicativeHaar K S) •
        sLocalProductMultiplicativeHaar K S :=
  sLocalRadialMeasure_eq_smul K S _

theorem radialProductHaarScalar_pos :
    0 < radialHaarScalar K S (sLocalProductMultiplicativeHaar K S) :=
  radialHaarScalar_pos K S _

variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
  [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))

def weightedMixedFourierFactor (W : AdditiveProbeTest K S) (z : ℂ)
    (x : (mixedEmbedding.mixedSpace K)ˣ) : ℂ :=
  fourierIntegral (HeckeGeneral.Bridge.standardMixedAddCharacter K) volume
      (fun y => W.infiniteTest ((traceToMixed K).symm y)) x.val *
    (mixedEmbedding.norm (x : mixedEmbedding.mixedSpace K) : ℂ) ^ z

def weightedFiniteFourierFactor (W : AdditiveProbeTest K S) (z : ℂ)
    (p : S) (x : (p.val.adicCompletion K)ˣ) : ℂ :=
  (((μ p).real (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) : ℂ))⁻¹ *
    fourierIntegral (StandardAddChar.psiLocal K p.val) (μ p) (W.finiteTest p) x.val *
      (‖x.val‖ : ℂ) ^ z

private theorem ofReal_finset_prod_cpow {ι : Type*} (t : Finset ι)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (z : ℂ) :
    ((∏ i ∈ t, f i : ℝ) : ℂ) ^ z = ∏ i ∈ t, (f i : ℂ) ^ z := by
  induction t using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Complex.ofReal_one, Complex.one_cpow]
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hf i) (Finset.prod_nonneg (fun j _ => hf j)), ih]

theorem weightedAdditiveFourier_eq_product (W : AdditiveProbeTest K S) (z : ℂ)
    (x : sLocalMultiplicativeGroup K S) :
    additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z =
      weightedMixedFourierFactor K S W z x.1 *
        ∏ p : S, weightedFiniteFourierFactor K S μ W z p (x.2 p) := by
  unfold additiveFourier weightedMixedFourierFactor weightedFiniteFourierFactor
  rw [sLocalProductNorm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg _)
      (Finset.prod_nonneg (fun p _ => norm_nonneg _)),
    ofReal_finset_prod_cpow Finset.univ _ (fun p => norm_nonneg _) z]
  simp only [Finset.prod_mul_distrib]
  ring

theorem weightedAdditiveFourier_integrable_of_local
    (W : AdditiveProbeTest K S) (z : ℂ)
    (harch : Integrable (weightedMixedFourierFactor K S W z) (mixedMultiplicativeHaar K))
    (hfin : ∀ p : S, Integrable (weightedFiniteFourierFactor K S μ W z p)
      (Measure.haar : Measure (p.val.adicCompletion K)ˣ)) :
    Integrable
      (fun x : sLocalMultiplicativeGroup K S =>
        additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z)
      (sLocalProductMultiplicativeHaar K S) := by
  have hp : Integrable
      (fun t : (p : S) → (p.val.adicCompletion K)ˣ =>
        ∏ p : S, weightedFiniteFourierFactor K S μ W z p (t p))
      (finiteMultiplicativeHaar K S) := Integrable.fintype_prod_dep hfin
  exact (harch.mul_prod hp).congr (Filter.Eventually.of_forall fun x =>
    (weightedAdditiveFourier_eq_product K S μ W z x).symm)

theorem additiveMellin_eq_productHaar_localFactors
    (W : AdditiveProbeTest K S) (z : ℂ)
    (harch : Integrable (weightedMixedFourierFactor K S W z) (mixedMultiplicativeHaar K))
    (hfin : ∀ p : S, Integrable (weightedFiniteFourierFactor K S μ W z p)
      (Measure.haar : Measure (p.val.adicCompletion K)ˣ)) :
    additiveMellin K S μ W z =
      ((radialHaarScalar K S (sLocalProductMultiplicativeHaar K S) : ℝ) : ℂ) *
        ((∫ x, weightedMixedFourierFactor K S W z x ∂mixedMultiplicativeHaar K) *
          ∏ p : S, ∫ x, weightedFiniteFourierFactor K S μ W z p x
            ∂(Measure.haar : Measure (p.val.adicCompletion K)ˣ)) := by
  rw [additiveMellin_eq_positiveScalar_mul_integral_of_integrable K S μ
    (sLocalProductMultiplicativeHaar K S) W z
    (weightedAdditiveFourier_integrable_of_local K S μ W z harch hfin)]
  congr 1
  simp_rw [weightedAdditiveFourier_eq_product K S μ W z]
  rw [sLocalProductMultiplicativeHaar]
  rw [integral_prod_mul (weightedMixedFourierFactor K S W z)
    (fun t : (p : S) → (p.val.adicCompletion K)ˣ =>
      ∏ p : S, weightedFiniteFourierFactor K S μ W z p (t p))]
  congr 1
  exact integral_fintype_prod_eq_prod _

end HeckeGeneral.Analysis.SLocalRadialHaarDraft
