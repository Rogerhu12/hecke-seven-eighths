import HeckeGeneral.Arithmetic.SUnitPrimePowers
import HeckeGeneral.Arithmetic.SIntegerLocalization

/-!
# Localization at exactly a prescribed finite set of primes

The product of the class-number prime-power generators has prime support
exactly equal to the original finite set `S`. Consequently the actual
valuation-defined ring of S-integers is a localization away from this one
integer. No enlargement of `S` or principal-ideal-domain assumption is used.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]

/-- A class-number prime-power generator belongs to precisely its own prime. -/
theorem primePowerGenerator_mem_prime_iff
    (v w : HeightOneSpectrum (𝓞 K)) :
    primePowerGenerator K v ∈ w.asIdeal ↔ w = v := by
  constructor
  · intro hmem
    by_contra hne
    have hlt := (w.intValuation_lt_one_iff_mem (primePowerGenerator K v)).mpr hmem
    rw [intValuation_primePowerGenerator_ne K v w hne] at hlt
    exact (lt_irrefl (1 : WithZero (Multiplicative ℤ))) hlt
  · intro hw
    subst w
    apply (v.intValuation_lt_one_iff_mem (primePowerGenerator K v)).mp
    rw [intValuation_primePowerGenerator_self]
    apply WithZero.exp_lt_one_iff.mpr
    exact neg_lt_zero.mpr (by exact_mod_cast classNumber_pos K)

/-- One nonzero integer whose prime support is the prescribed finite set. -/
def finiteSIntegerDenominator (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    𝓞 K :=
  ∏ v ∈ (Set.toFinite S).toFinset, primePowerGenerator K v

theorem finiteSIntegerDenominator_ne_zero
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    finiteSIntegerDenominator K S ≠ 0 := by
  classical
  unfold finiteSIntegerDenominator
  exact Finset.prod_ne_zero_iff.mpr fun v _hv => primePowerGenerator_ne_zero K v

/-- The support is exactly `S`, including when `S` is empty. -/
theorem integerPrimeSupport_finiteSIntegerDenominator
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    integerPrimeSupport (finiteSIntegerDenominator K S) = S := by
  classical
  ext w
  letI : w.asIdeal.IsPrime := w.isPrime
  rw [mem_integerPrimeSupport, finiteSIntegerDenominator, Ideal.IsPrime.prod_mem_iff]
  constructor
  · rintro ⟨v, hv, hmem⟩
    have h := (primePowerGenerator_mem_prime_iff K v w).mp hmem
    subst w
    exact (Set.toFinite S).mem_toFinset.mp hv
  · intro hw
    exact ⟨w, (Set.toFinite S).mem_toFinset.mpr hw,
      (primePowerGenerator_mem_prime_iff K w w).mpr rfl⟩

/-- Every finite-set S-integer ring is the actual localization away from
the explicit product of the class-number prime-power generators. -/
theorem sInteger_isLocalizationAway_finiteDenominator
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    IsLocalization.Away (finiteSIntegerDenominator K S) (S.integer K) := by
  have h := integerPrimeSupport_isLocalizationAway K
    (finiteSIntegerDenominator K S) (finiteSIntegerDenominator_ne_zero K S)
  rw [integerPrimeSupport_finiteSIntegerDenominator K S] at h
  exact h

/-- An existential interface retaining both exact support and the genuine
localization property, rather than a larger auxiliary set of primes. -/
theorem exists_sInteger_localizationAway
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ∃ a : 𝓞 K, a ≠ 0 ∧ integerPrimeSupport a = S ∧
      IsLocalization.Away a (S.integer K) := by
  exact ⟨finiteSIntegerDenominator K S, finiteSIntegerDenominator_ne_zero K S,
    integerPrimeSupport_finiteSIntegerDenominator K S,
    sInteger_isLocalizationAway_finiteDenominator K S⟩

end HeckeGeneral.Arithmetic
