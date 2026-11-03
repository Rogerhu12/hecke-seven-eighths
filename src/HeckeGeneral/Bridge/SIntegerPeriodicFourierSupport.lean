import HeckeGeneral.Bridge.SIntegerPeriodicFiniteFourier
import HeckeGeneral.Arithmetic.SIntegerModulusFrequencySupport
import HeckeGeneral.Characters.LocalStandardAnnihilator

/-! Actual Fourier support outside the original S-local coordinates.
The normalized transform vanishes when the literal field product c*xi is
not an S-integer. This is support containment, with no nonvanishing claim
inside the support and no change of the original multiplicative quotient. -/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  NumberField.StandardAddChar NumberField.AdelicFourier MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K

variable (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)


local notation "P" => sIntegerModulusPlaces K (S : Set (HeightOneSpectrum (𝓞 K))) c hc

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

include hS μv in
theorem sIntegerPeriodicCosetMask_fourier_zero_of_not_support
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : (OS ⧸ Ideal.span ({c} : Set OS))) (ξ : K)
    (w : FiniteAdeleRing (𝓞 K) K)
    (hw : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      w v = algebraMap K (v.adicCompletion K) ξ)
    (hξ : (c : K) * ξ ∉ OS) :
    ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
      fourierIntegral (standardFiniteAddCharacter K) ν
        (sIntegerPeriodicCosetMask K S c hc h r) w = 0 := by
  obtain ⟨v, hvS, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧
      ¬ Valued.v (algebraMap K (v.adicCompletion K) ξ) ≤
        WithZero.exp (sIntegerModulusPrimeExponents K
          (S : Set (HeightOneSpectrum (𝓞 K))) c hc v : ℤ) := by
    by_contra! hall
    exact hξ ((sIntegerModulusFrequencySupport_iff K
      (S : Set (HeightOneSpectrum (𝓞 K))) c hc ξ).mp hall)
  have hlocal := sIntegerPeriodicLocalFactor_locallyConstant_compactSupport K S c hc h hlc hcs r
  rw [sIntegerPeriodicCosetMask,
    sIntegerFiniteMask_fourier_factorization K ν μv (S ∪ P) _
      (fun v hv => (hlocal v hv).1) (fun v hv => (hlocal v hv).2)]
  by_cases hvP : v ∈ P
  · have hterm :
        (((μv v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
          fourierIntegral (psiLocal K v) (μv v)
            (sIntegerPeriodicLocalFactor K S c hc h r v) (w v) = 0 := by
      rw [sIntegerPeriodicLocalFactor_at_modulus K S c hc h r ⟨v, hvP⟩,
        normalizedFourier_localIntegerResidueCosetIndicator, hw v hvS,
        hS v hvS, zero_add, if_neg hv, mul_zero]
    have hprod : sIntegerLocalFourierProduct K μv (S ∪ P)
        (sIntegerPeriodicLocalFactor K S c hc h r) w = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_union_right S hvP) hterm
    rw [hprod, zero_mul]
  · have hn : sIntegerModulusPrimeExponents K
        (S : Set (HeightOneSpectrum (𝓞 K))) c hc v = 0 :=
      Finsupp.notMem_support_iff.mp hvP
    have hnot : ¬ outsideSStandardAnnihilator K (S ∪ P) w := by
      intro hann
      have hvU : v ∉ S ∪ P := by simp only [Finset.mem_union, not_or]; exact ⟨hvS, hvP⟩
      have hbound := (standardLocalAnnihilator_iff K v (w v)).mp (hann v hvU)
      rw [hw v hvS, hS v hvS, WithZero.exp_zero] at hbound
      exact hv (by simpa only [hn, Int.natCast_zero, WithZero.exp_zero] using hbound)
    rw [if_neg hnot, mul_zero]

include hS μv in
theorem sIntegerPeriodicFiniteTest_fourier_zero_of_not_support
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (ξ : K)
    (w : FiniteAdeleRing (𝓞 K) K)
    (hw : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      w v = algebraMap K (v.adicCompletion K) ξ)
    (hξ : (c : K) * ξ ∉ OS) :
    ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
      fourierIntegral (standardFiniteAddCharacter K) ν
        (sIntegerPeriodicFiniteTest K S c hc h f d) w = 0 := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
  rw [fourierIntegral_sIntegerPeriodicFiniteTest K S c hc ν h hlc hcs f d,
    Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro r _
  calc
    _ = f (Ideal.Quotient.mk _ d * r) *
        (((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
          fourierIntegral (standardFiniteAddCharacter K) ν
            (sIntegerPeriodicCosetMask K S c hc h r) w) := by ring
    _ = 0 := by
      rw [sIntegerPeriodicCosetMask_fourier_zero_of_not_support K S hS c hc ν μv
        h hlc hcs r ξ w hw hξ, mul_zero]

end HeckeGeneral.Bridge

