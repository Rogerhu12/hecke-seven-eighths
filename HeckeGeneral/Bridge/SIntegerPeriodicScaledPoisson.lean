import HeckeGeneral.Bridge.SIntegerPeriodicAdelicFourier
import HeckeGeneral.Arithmetic.SIntegerModulusFrequencyReindex
import HeckeGeneral.Bridge.SIntegerModulusScaling

/-! Periodic Poisson on the original S-integer ring with its actual finite
divisor transform. Reindexing the supported field frequencies contributes
no Jacobian. The inverse modulus norm comes from the finite Fourier masses.
Both sums include zero, and the divisor need not be a unit. -/

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

include ν μ in
/-- The full periodic identity before orbit integration and zero subtraction. -/
theorem sIntegerPeriodicScaledPoisson
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (p : G) :
    (∑' a : OS, f (Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) (d * a)) *
      sIntegerScaledTensorTerm K S φ h p a.val) =
      (sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) p : ℂ)⁻¹ *
        (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹ *
        ∑' a : OS,
          sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
            (Ideal.Quotient.mk _ a) *
          sIntegerScaledDualTensorTerm K S μv φ h
            (p⁻¹ * (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K)))
              ⟨c, hc⟩)⁻¹) a.val := by
  let b : ℂ := ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹
  let n : ℂ := (sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) p : ℂ)⁻¹
  let C : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
    Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
  let q : ℂ := ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨c, hc⟩).val : ℂ)⁻¹
  let F : K → ℂ := fun ξ => b * fourierIntegral (stdAddChar K) μ
    (sIntegerPeriodicAdelicTest K S c hc φ h f d) (sLocalScaledPrincipal K S p⁻¹ ξ)
  have hF : ∀ ξ : K, (c : K) * ξ ∉ OS → F ξ = 0 := by
    intro ξ hξ
    exact sIntegerPeriodicAdelicTest_fourier_scaled_zero_of_not_support
      K S hS c hc ν μv μ φ h hlc hcs f d p⁻¹ ξ hξ
  have hvalue (a : OS) : F ((a : K) / (c : K)) =
      (C * q) * (sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K)))
        hS c hc f d (Ideal.Quotient.mk _ a) *
        sIntegerScaledDualTensorTerm K S μv φ h
          (p⁻¹ * (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K)))
            ⟨c, hc⟩)⁻¹) a.val) := by
    dsimp only [F, b]
    rw [sIntegerPeriodicAdelicTest_fourier_scaled_div K S hS c hc ν μv μ
      φ h hlc hcs f d a p⁻¹,
      sIntegerScaledDualTensorTerm_div_modulus K S c hc μv φ h p⁻¹ a.val]
    dsimp only [C, q]
    ring
  calc
    _ = b * n * ∑' ξ : K, fourierIntegral (stdAddChar K) μ
        (sIntegerPeriodicAdelicTest K S c hc φ h f d)
        (sLocalScaledPrincipal K S p⁻¹ ξ) :=
      sIntegerPeriodicScaledAdelicPoisson K S c hc μ φ h hlc hcs f d p
    _ = n * ∑' ξ : K, F ξ := by dsimp only [F]; rw [tsum_mul_left]; ring
    _ = n * ∑' a : OS, F ((a : K) / (c : K)) := by
      rw [tsum_sIntegerModulusFrequency_eq K (S : Set (HeightOneSpectrum (𝓞 K))) c hc F hF]
    _ = n * ∑' a : OS, (C * q) *
        (sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
          (Ideal.Quotient.mk _ a) *
          sIntegerScaledDualTensorTerm K S μv φ h
            (p⁻¹ * (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K)))
              ⟨c, hc⟩)⁻¹) a.val) := by
      congr 1
      exact tsum_congr hvalue
    _ = _ := by rw [tsum_mul_left]; dsimp only [n, C, q]; ring

end HeckeGeneral.Bridge

