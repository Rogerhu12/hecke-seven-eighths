import HeckeSkeleton.Descent.LocalIdentity

/-! Artin factorization after deleting the actual finite set of bad primes. -/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Descent.DeletedEuler

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Characters.NormPullbackDraft
open HeckeSkeleton.Descent.Artin HeckeSkeleton.Descent.ArtinPrimeArithmetic
open HeckeSkeleton.Descent.PrimeAssembly HeckeSkeleton.Descent.LocalIdentity
open scoped Classical BigOperators

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K] [IsAbelianGalois F K]

/-- All character-ramified and extension-ramified primes, and primes above 2 or 3. -/
def badPlaces (χ : HeckeCharacter F) : Finset (HeightOneSpectrum (𝓞 F)) :=
  artinBadPrimes F K χ

/-- Precisely all primes above the downstairs deletion set. -/
def badPlacesUp (χ : HeckeCharacter F) : Finset (HeightOneSpectrum (𝓞 K)) :=
  primesAboveDeletion F K (badPlaces F K χ)

@[simp] theorem mem_badPlacesUp (χ : HeckeCharacter F) (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ badPlacesUp F K χ ↔ _root_.finitePlaceBelow (K := F) w ∈ badPlaces F K χ :=
  mem_primesAboveDeletion F K (badPlaces F K χ) w

/-- The full Artin family has the same deleted Euler product as the actual norm pullback. -/
theorem artinDeletedEulerProduct (χ : HeckeCharacter F) :
    ∀ s : ℂ, 1 < s.re →
      heckeDeletedContinuation K (heckeNormPullback F K χ) (badPlacesUp F K χ) s =
        ∏ ψ ∈ artinFactors F K χ, heckeDeletedContinuation F ψ (badPlaces F K χ) s := by
  intro s hs
  apply deleted_artin_identity_of_good_prime_factors F K χ (badPlaces F K χ) hs
  intro v hv
  obtain ⟨hχ, hunram⟩ := good_of_not_mem_artinBadPrimes F K χ v hv
  exact good_prime_artin_euler_identity F K χ v hχ hunram s

end HeckeSkeleton.Descent.DeletedEuler
