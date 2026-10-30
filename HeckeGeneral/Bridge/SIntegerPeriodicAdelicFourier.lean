import HeckeGeneral.Bridge.SIntegerPeriodicAdelicTest
import HeckeGeneral.Bridge.SIntegerPeriodicFiniteFourier
import HeckeGeneral.Bridge.SIntegerPeriodicFourierSupport

/-!
# Actual periodic adelic Fourier transforms at S-local scaled frequencies

The finite coefficient is evaluated on the original principal quotient,
while the archimedean and original S-local Fourier factors retain the
actual multiplicative base point. The finite exceptional primes only
determine additive cosets. The formula preserves the adelic box mass,
the mixed-space discriminant factor, and the inverse modulus norm.

The support statement is containment: no nonvanishing inside the inverse
modulus lattice is asserted. All field and quotient frequencies include zero.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  NumberField.StandardAddChar NumberField.AdelicFourier MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "G" => sLocalMultiplicativeGroup K (S : Set (HeightOneSpectrum (𝓞 K)))

variable (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)



variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν in
/-- The literal divisor transform multiplies the original scaled dual tensor.
The tensor is defined at every field frequency, including nonintegral `a/c`. -/
theorem sIntegerPeriodicAdelicTest_fourier_scaled_div
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d a : OS) (p : G) :
    ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ *
        fourierIntegral (stdAddChar K) μ (sIntegerPeriodicAdelicTest K S c hc φ h f d)
          (sLocalScaledPrincipal K S p ((a : K) / (c : K))) =
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹ *
        sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
          (Ideal.Quotient.mk _ a) *
        sIntegerScaledDualTensorTerm K S μv φ h p ((a : K) / (c : K)) := by
  have hw (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
      (sLocalScaledPrincipal K S p ((a : K) / (c : K))).2 v =
        algebraMap K (v.adicCompletion K) ((a : K) / (c : K)) :=
    sLocalScaledPrincipal_finite_not_mem K S p _ v hv
  have hsplit := EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    K μ ν (stdAddChar K) φ (sIntegerPeriodicFiniteTest K S c hc h f d)
      (sLocalScaledPrincipal K S p ((a : K) / (c : K)))
  rw [show ((ν (AdelicBox.integralFiniteAdeles (𝓞 K) K)).toReal : ℂ)⁻¹ *
      fourierIntegral ((stdAddChar K).compAddMonoidHom (AddMonoidHom.inr _ _)) ν
        (sIntegerPeriodicFiniteTest K S c hc h f d)
        (sLocalScaledPrincipal K S p ((a : K) / (c : K))).2 =
      ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹ *
        sIntegerLocalFourierProduct K μv S h
          (sLocalScaledPrincipal K S p ((a : K) / (c : K))).2 *
        sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
          (Ideal.Quotient.mk _ a) from
    sIntegerPeriodicFiniteTest_fourier_div K S hS c hc ν μv h hlc hcs f d a _ hw] at hsplit
  calc
    _ = (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        (fourierIntegral (standardMixedAddCharacter K) volume φ
            (InfiniteAdeleRing.ringEquiv_mixedSpace K
              (sLocalScaledPrincipal K S p ((a : K) / (c : K))).1) *
          (((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹ *
            sIntegerLocalFourierProduct K μv S h
              (sLocalScaledPrincipal K S p ((a : K) / (c : K))).2 *
            sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
              (Ideal.Quotient.mk _ a))) := hsplit
    _ = _ := by unfold sIntegerScaledDualTensorTerm; ring

include hS ν μv in
/-- Scaling by the original S-local group preserves the inverse-modulus support. -/
theorem sIntegerPeriodicAdelicTest_fourier_scaled_zero_of_not_support
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (p : G) (ξ : K)
    (hξ : (c : K) * ξ ∉ OS) :
    ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ *
      fourierIntegral (stdAddChar K) μ (sIntegerPeriodicAdelicTest K S c hc φ h f d)
        (sLocalScaledPrincipal K S p ξ) = 0 := by
  have hw (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
      (sLocalScaledPrincipal K S p ξ).2 v = algebraMap K (v.adicCompletion K) ξ :=
    sLocalScaledPrincipal_finite_not_mem K S p ξ v hv
  have hsplit := EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    K μ ν (stdAddChar K) φ (sIntegerPeriodicFiniteTest K S c hc h f d)
      (sLocalScaledPrincipal K S p ξ)
  rw [show ((ν (AdelicBox.integralFiniteAdeles (𝓞 K) K)).toReal : ℂ)⁻¹ *
      fourierIntegral ((stdAddChar K).compAddMonoidHom (AddMonoidHom.inr _ _)) ν
        (sIntegerPeriodicFiniteTest K S c hc h f d) (sLocalScaledPrincipal K S p ξ).2 = 0 from
    sIntegerPeriodicFiniteTest_fourier_zero_of_not_support K S hS c hc ν μv
      h hlc hcs f d ξ _ hw hξ, mul_zero, mul_zero] at hsplit
  exact hsplit

end HeckeGeneral.Bridge

