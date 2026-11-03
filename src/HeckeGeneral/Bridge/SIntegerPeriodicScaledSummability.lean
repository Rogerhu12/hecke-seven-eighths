import HeckeGeneral.Bridge.SIntegerPeriodicScaledPoisson

/-! Actual finite quotient bounds prove dual summability and allow both
zero contributions to be separated from periodic scaled Poisson. -/

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
/-- The genuine divisor-transform coefficients are bounded by their finite
pullback L1 mass, so the dual weighted sum is summable at every local base. -/
theorem summable_sIntegerPeriodicScaledDualTensor
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (p : G) :
    Summable (fun a : OS =>
      sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
        (Ideal.Quotient.mk _ a) *
      sIntegerScaledDualTensorTerm K S μv φ h p a.val) := by
  let B := sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
    (fun a : (OS ⧸ Ideal.span ({c} : Set OS)) => f (Ideal.Quotient.mk _ d * a))
  have hs := summable_sIntegerScaledDualTensorTerm K S ν μv μ hS φ h hlc hcs p
  apply (hs.norm.mul_left B).of_norm_bounded
  intro a
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_sIntegerPeriodicDivisorFourier_le_pullback_L1 K
      (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d (Ideal.Quotient.mk _ a))
    (norm_nonneg _)

include ν μ in
/-- The periodic nonzero formula retains the literal values of both zero
terms and the inverse-modulus dual base; no vanishing at zero is assumed. -/
theorem sIntegerPeriodicScaledPoisson_nonzero
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (p : G) :
    let C : ℂ :=
      (sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) p : ℂ)⁻¹ *
        (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹
    let pdual : G := p⁻¹ *
      (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩)⁻¹
    (∑' a : {a : OS // a ≠ 0},
      f (Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) (d * a.val)) *
        sIntegerScaledTensorTerm K S φ h p a.val.val) =
      C * (∑' a : {a : OS // a ≠ 0},
        sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
          (Ideal.Quotient.mk _ a.val) *
        sIntegerScaledDualTensorTerm K S μv φ h pdual a.val.val) +
      C * (sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d 0 *
        sIntegerScaledDualTensorTerm K S μv φ h pdual 0) -
      f 0 * sIntegerScaledTensorTerm K S φ h p 0 := by
  dsimp only
  have he := sIntegerPeriodicScaledPoisson K S hS c hc ν μv μ φ h hlc hcs f d p
  rw [tsum_eq_zero_add_tsum_ne_zero _
      (summable_sIntegerPeriodicScaledTensor K S c hc φ h hlc hcs f d p),
    tsum_eq_zero_add_tsum_ne_zero _
      (summable_sIntegerPeriodicScaledDualTensor K S hS c hc ν μv μ φ h hlc hcs f d
        (p⁻¹ * (sLocalNonzeroIntegerDiagonal K
          (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩)⁻¹))] at he
  simp only [mul_zero, map_zero] at he
  linear_combination he

end HeckeGeneral.Bridge

