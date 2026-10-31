import HeckeGeneral.Arithmetic.SIntegerFiniteLocalization
import HeckeGeneral.Arithmetic.SIntegerOrbits
import HeckeGeneral.Characters.SIntegerSexticCharacter

/-! SOURCE ONLY, UNRUN. One supported denominator is chosen for the actual
S-integer before any exterior prime or second Hilbert argument. Its prime
support is contained in the original S, without enlargement or PID input. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical
variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- A power of the actual finite-set denominator avoids every exterior
prime, including exponent zero. -/
theorem finiteSIntegerDenominator_pow_not_mem_exterior
    (t : ℕ) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    finiteSIntegerDenominator K S ^ t ∉ p.asIdeal := by
  intro ht
  have hD : finiteSIntegerDenominator K S ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem t ht
  apply hp
  rw [← integerPrimeSupport_finiteSIntegerDenominator K S]
  exact (mem_integerPrimeSupport _ p).mpr hD

/-- Actual supported denominator witness with simultaneous local avoidance.
The equality has integral numerator on the left and D^t*a on the right. -/
theorem exists_sIntegerSextic_supported_denominator
    (a : NonzeroRingElements (S.integer K)) :
    ∃ t : ℕ, ∃ A : 𝓞 K,
      A ≠ 0 ∧ finiteSIntegerDenominator K S ^ t ≠ 0 ∧
      algebraMap (𝓞 K) (S.integer K) A =
        algebraMap (𝓞 K) (S.integer K) (finiteSIntegerDenominator K S ^ t) * a.val ∧
      ∀ p : HeightOneSpectrum (𝓞 K), ∀ hp : p ∉ S,
        finiteSIntegerDenominator K S ^ t ∉ p.asIdeal ∧
        (sIntegerSexticResidueMap K S p hp a.val ≠ 0 → A ∉ p.asIdeal) := by
  letI supportedDenominator_localization :
      IsLocalization.Away (finiteSIntegerDenominator K S) (S.integer K) :=
    sInteger_isLocalizationAway_finiteDenominator K S
  obtain ⟨⟨A, d⟩, hsurj⟩ :=
    IsLocalization.surj (Submonoid.powers (finiteSIntegerDenominator K S)) a.val
  obtain ⟨t, ht⟩ :=
    (Submonoid.mem_powers_iff d.val (finiteSIntegerDenominator K S)).mp d.property
  have hden : algebraMap (𝓞 K) (S.integer K) d.val ≠ 0 :=
    (IsLocalization.map_units (S.integer K) d).ne_zero
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hsurj
    exact (mul_ne_zero a.property hden) hsurj
  have heq : algebraMap (𝓞 K) (S.integer K) A =
      algebraMap (𝓞 K) (S.integer K) (finiteSIntegerDenominator K S ^ t) * a.val := by
    rw [ht]
    exact hsurj.symm.trans (mul_comm _ _)
  refine ⟨t, A, hA, pow_ne_zero _ (finiteSIntegerDenominator_ne_zero K S), heq, ?_⟩
  intro p hp
  letI supportedDenominator_residuePrime : p.asIdeal.IsPrime := p.isPrime
  have hd := finiteSIntegerDenominator_pow_not_mem_exterior K S t p hp
  refine ⟨hd, ?_⟩
  intro ha hAp
  have hdres : sIntegerSexticResidueMap K S p hp
      (algebraMap (𝓞 K) (S.integer K) (finiteSIntegerDenominator K S ^ t)) ≠ 0 := by
    rw [sIntegerSexticResidueMap_algebraMap]
    exact fun hz => hd (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hres := congrArg (sIntegerSexticResidueMap K S p hp) heq
  rw [map_mul] at hres
  rw [sIntegerSexticResidueMap_algebraMap,
    Ideal.Quotient.eq_zero_iff_mem.mpr hAp] at hres
  exact (mul_ne_zero hdres ha) hres.symm
end HeckeGeneral.Arithmetic
