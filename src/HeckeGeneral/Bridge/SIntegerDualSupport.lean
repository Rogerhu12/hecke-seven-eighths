import HeckeGeneral.Bridge.SIntegerFourierFactorization
import HeckeGeneral.Characters.LocalStandardAnnihilator

/-! Actual principal dual support after adjoining the different primes to S. -/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

theorem outsideSStandardAnnihilator_iff_valuation
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : FiniteAdeleRing (𝓞 K) K) :
    outsideSStandardAnnihilator K S w ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        Valued.v (w v) ≤ WithZero.exp (localDifferentExponent K v) := by
  unfold outsideSStandardAnnihilator
  simp only [standardLocalAnnihilator_iff]

/-- Once S contains every different prime, actual principal dual frequencies
are exactly the genuine valuation-defined S-integers. -/
theorem outsideSStandardAnnihilator_principal_iff_sInteger
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (a : K) :
    outsideSStandardAnnihilator K S (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) ↔
      a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
  rw [← outsideIntegral_principal_iff_sInteger K S a,
    outsideSStandardAnnihilator_iff_valuation]
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [hS v hv, WithZero.exp_zero,
    HeightOneSpectrum.mem_adicCompletionIntegers]

theorem exists_finiteS_standardDualSupport
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      ∀ a : K,
        outsideSStandardAnnihilator K S
          (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) ↔
          a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
  obtain ⟨S, hsub, hS⟩ := exists_finiteS_localDifferentExponent_eq_zero K S₀
  exact ⟨S, hsub, outsideSStandardAnnihilator_principal_iff_sInteger K S hS⟩

end HeckeGeneral.Bridge
