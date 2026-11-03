import HeckeGeneral.Analysis.GlobalThetaData
import HeckeGeneral.Characters.SIntegerSexticPowerMask
import HeckeGeneral.Arithmetic.IdealFactorization
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
Whole-ideal assembly from good-prime coefficient calibration. This uses
finite ideal factorization and the existing power-residue-symbol API.

A finite arithmetic consumer: good-prime coefficient calibration implies the
literal whole-ideal calibration with the original coprimality mask. No character
is constructed here, and no ramification at bad numerator primes is assumed.
The argument even allows a = 0; the requested nonzero case is a special case.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.PrimeCalibrationDraft

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The two existing multiplicity definitions agree on actual nonzero ideals. -/
theorem idealPrimeMultiplicity_eq_primeExponents
    (I : NonzeroIdeal K) (p : HeightOneSpectrum (𝓞 K)) :
    idealPrimeMultiplicity K p I.val = primeExponents I p := by
  rw [primeExponents_apply]
  exact Ideal.count_associates_factors_eq
    (nonZeroDivisors.coe_ne_zero I) p.isPrime p.ne_bot

/-- Reindexing the existing normalized-factor coefficient by the named finite
prime-divisor subtype. This includes the empty product at I = top. -/
theorem idealCoefficient_eq_prod_idealPrimeDivisors
    (f : HeightOneSpectrum (𝓞 K) → ℂ) (I : NonzeroIdeal K) :
    idealCoefficient f I.val =
      letI : Fintype (idealPrimeDivisors K I.val) :=
        (idealPrimeDivisors_finite K I.val (nonZeroDivisors.coe_ne_zero I)).fintype
      ∏ p : idealPrimeDivisors K I.val, f p.val ^ idealPrimeMultiplicity K p.val I.val := by
  letI : Fintype (idealPrimeDivisors K I.val) :=
    (idealPrimeDivisors_finite K I.val (nonZeroDivisors.coe_ne_zero I)).fintype
  have hsupport : ∀ p : HeightOneSpectrum (𝓞 K),
      p ∈ (primeExponents I).support ↔ p.asIdeal ∣ I.val := by
    intro p
    rw [Finsupp.mem_support_iff, ← idealPrimeMultiplicity_eq_primeExponents]
    exact Associates.count_ne_zero_iff_dvd (nonZeroDivisors.coe_ne_zero I) p.irreducible
  have hrec : (primeExponents I).prod (fun p n => p.asIdeal ^ n) = I.val := by
    exact congrArg Subtype.val (idealOfPrimeExponents_primeExponents I)
  calc
    idealCoefficient f I.val =
        (idealCoefficientHom f) ((primeExponents I).prod (fun p n => p.asIdeal ^ n)) :=
      congrArg (idealCoefficientHom f) hrec.symm
    _ = (primeExponents I).prod (fun p n => idealCoefficient f (p.asIdeal ^ n)) :=
      map_finsuppProd (idealCoefficientHom f) _ _
    _ = (primeExponents I).prod (fun p n => f p ^ n) := by
      unfold Finsupp.prod
      apply Finset.prod_congr rfl
      intro p _
      exact idealCoefficient_prime_pow f p (primeExponents I p)
    _ = ∏ p : idealPrimeDivisors K I.val,
        f p.val ^ idealPrimeMultiplicity K p.val I.val := by
      unfold Finsupp.prod
      rw [Finset.prod_subtype (primeExponents I).support hsupport]
      apply Finset.prod_congr rfl
      intro p _
      rw [idealPrimeMultiplicity_eq_primeExponents]

/-- Literal good-prime calibration is enough for the original masked
whole-ideal coefficient. In the bad branch the symbol vanishes by its actual
zero set, regardless of the character's behavior at the bad prime. -/
theorem masked_heckeIdealCoefficient_eq_idealSymbol_of_primeCalibration
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (D : ThetaArithmeticData K S) (a : S.integer K) (χ : HeckeCharacter K)
    (hprime : ∀ (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S),
      ¬ p.asIdeal ∣ sIntegerModulusContraction K S a →
      primeCoefficient K χ p =
        sIntegerSexticEvaluation K S p hpS D.root6 D.primitive6 D.embedding
          (D.away_six p hpS) a)
    (I : ExteriorIdeal K S) :
    (if IsCoprime I.val.val (sIntegerModulusContraction K S a)
      then heckeIdealCoefficient K χ I.val else 0) = idealSymbol K S D I a := by
  have hI : I.val.val ≠ 0 := nonZeroDivisors.coe_ne_zero I.val
  have hno := sIntegerSextic_no_badPrime_iff_coprime_contraction
    K S I.val.val hI I.property a
  by_cases hcop : IsCoprime I.val.val (sIntegerModulusContraction K S a)
  · rw [if_pos hcop]
    letI : Fintype (idealPrimeDivisors K I.val.val) :=
      (idealPrimeDivisors_finite K I.val.val hI).fintype
    change idealCoefficient (primeCoefficient K χ) I.val.val =
      sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding I.val.val
        hI I.property (fun p hp => D.away_six p (I.property p hp)) a
    rw [idealCoefficient_eq_prod_idealPrimeDivisors K (primeCoefficient K χ) I.val]
    unfold sIntegerSexticIdealEvaluation
    apply Finset.prod_congr rfl
    intro p _
    apply congrArg (fun z : ℂ => z ^ idealPrimeMultiplicity K p.val I.val.val)
    apply hprime p.val (I.property p.val p.property)
    intro hdiv
    exact (hno.mpr hcop) p.val p.property
      ((sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction
        K S p.val (I.property p.val p.property) a).mpr hdiv)
  · rw [if_neg hcop]
    have hbad : ∃ (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I.val.val),
        sIntegerSexticResidueMap K S p (I.property p hp) a = 0 := by
      by_contra h
      apply hcop
      apply hno.mp
      intro p hp hz
      exact h ⟨p, hp, hz⟩
    obtain ⟨p, hp, hz⟩ := hbad
    symm
    exact sIntegerSexticIdealEvaluation_eq_zero_of_badPrime
      K S D.root6 D.primitive6 D.embedding I.val.val hI I.property
        (fun q hq => D.away_six q (I.property q hq)) a p hp hz

end HeckeGeneral.Analysis.PrimeCalibrationDraft
