import HeckeGeneral.Bridge.SIntegerAdelicPoisson
import HeckeGeneral.Characters.StandardFiniteFactorization
import FLTReuse.M18c509625f9eb716
import FLTReuse.Mdd4e907a696a6974
import FLTReuse.M843899312a51c0f5

/-!
# Actual local factors in S-integer Poisson summation

The finite adelic Fourier transform factors into normalized local transforms
at S and the actual annihilator indicator outside S. The archimedean factor
uses the standard positive trace character and the Fourier convention
psi(-x*y). The mixed-space covolume contributes 2^r2 / sqrt(|disc K|).
No self-duality of the integral lattice is asserted at different primes.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain NumberField.AdelicFourier
  NumberField.StandardAddChar HeckeGeneral.Characters MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The actual standard character on the mixed archimedean algebra. -/
def standardMixedAddCharacter : AddChar (mixedEmbedding.mixedSpace K) ℂ :=
  (stdAddChar K).compAddMonoidHom ((AddMonoidHom.inl _ _).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toAddMonoidHom)

theorem standardMixedAddCharacter_apply (x : mixedEmbedding.mixedSpace K) :
    standardMixedAddCharacter K x =
      (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace K) x) : ℂ) := by
  change stdAddChar K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x, 0) = _
  rw [stdAddChar_apply_mk_zero_eq_fourierChar_trace,
    RingEquiv.apply_symm_apply]

/-- This is the genuine outside-S dual support, before any identification
with an inverse-different localization. -/
def outsideSStandardAnnihilator (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : FiniteAdeleRing (𝓞 K) K) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ z : v.adicCompletion K, z ∈ v.adicCompletionIntegers K →
      psiLocal K v (z * w v) = 1

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Each local transform retains its actual additive-Haar normalization. -/
def sIntegerLocalFourierProduct (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (w : FiniteAdeleRing (𝓞 K) K) : ℂ :=
  ∏ v ∈ S, (((μv v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
    fourierIntegral (psiLocal K v) (μv v) (h v) (w v)

/-- The finite transform is a product at S and the true annihilator away from S. -/
theorem sIntegerFiniteMask_fourier_factorization
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (w : FiniteAdeleRing (𝓞 K) K) :
    ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
      fourierIntegral (standardFiniteAddCharacter K) ν (sIntegerFiniteMask K S h) w =
    sIntegerLocalFourierProduct K μv S h w *
      (if outsideSStandardAnnihilator K S w then 1 else 0) := by
  have hcont : Continuous (standardFiniteAddCharacter K) :=
    (isGlobalAddChar_stdAddChar K).continuous.comp (continuous_const.prodMk continuous_id)
  exact inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq K ν μv
    (standardFiniteAddCharacter K) hcont (psiLocal K) (continuous_psiLocal K)
    (stdAddChar_finite_eq_finprod_psiLocal K)
    (Filter.Eventually.of_forall (fun v z hz =>
      LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v z hz))
    S h hlc hcs w

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν in
/-- Complete tensor factorization with the discriminant and complex-place
volume factors, and with no change of the actual Fourier character. -/
theorem sIntegerAdelicTestFunction_fourier_factorization
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (w : AdeleRing (𝓞 K) K) :
    ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ *
      fourierIntegral (stdAddChar K) μ (sIntegerAdelicTestFunction K S φ h) w =
    (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      (fourierIntegral (standardMixedAddCharacter K) volume φ
          (InfiniteAdeleRing.ringEquiv_mixedSpace K w.1) *
        (sIntegerLocalFourierProduct K μv S h w.2 *
          (if outsideSStandardAnnihilator K S w.2 then 1 else 0))) := by
  have hsplit := EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    K μ ν (stdAddChar K) φ (sIntegerFiniteMask K S h) w
  rw [show ((ν (AdelicBox.integralFiniteAdeles (𝓞 K) K)).toReal : ℂ)⁻¹ *
      fourierIntegral ((stdAddChar K).compAddMonoidHom (AddMonoidHom.inr _ _))
        ν (sIntegerFiniteMask K S h) w.2 =
      sIntegerLocalFourierProduct K μv S h w.2 *
        (if outsideSStandardAnnihilator K S w.2 then 1 else 0) from
      sIntegerFiniteMask_fourier_factorization K ν μv S h hlc hcs w.2] at hsplit
  exact hsplit

include μ ν in
/-- S-integer Poisson with fully factored local transforms. The outside-S
annihilator and both zero frequencies remain in the displayed full sums. -/
theorem sIntegerLocalPoisson
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    (∑' a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K,
      sIntegerTensorTerm K S φ h a.val) =
    (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      ∑' a : K,
        let w := algebraMap K (AdeleRing (𝓞 K) K) a
        fourierIntegral (standardMixedAddCharacter K) volume φ
          (InfiniteAdeleRing.ringEquiv_mixedSpace K w.1) *
          (sIntegerLocalFourierProduct K μv S h w.2 *
            (if outsideSStandardAnnihilator K S w.2 then 1 else 0)) := by
  rw [sIntegerAdelicPoisson K μ S φ h hlc hcs, ← tsum_mul_left]
  calc
    _ = ∑' a : K,
        (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
          (fourierIntegral (standardMixedAddCharacter K) volume φ
              (InfiniteAdeleRing.ringEquiv_mixedSpace K
                (algebraMap K (AdeleRing (𝓞 K) K) a).1) *
            (sIntegerLocalFourierProduct K μv S h
                (algebraMap K (AdeleRing (𝓞 K) K) a).2 *
              (if outsideSStandardAnnihilator K S
                (algebraMap K (AdeleRing (𝓞 K) K) a).2 then 1 else 0))) := by
      apply tsum_congr
      intro a
      exact sIntegerAdelicTestFunction_fourier_factorization K ν μv μ S φ h hlc hcs _
    _ = _ := tsum_mul_left

end HeckeGeneral.Bridge
