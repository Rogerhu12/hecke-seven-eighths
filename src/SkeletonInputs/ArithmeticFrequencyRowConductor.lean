import ArithmeticFrequencyRowRamification
import ArithmeticSexticKummerUnramified
import HeckeGeneral.Characters.SexticTameConductor
import Lean.Elab.Tactic.Omega

/-!
UNCOMPILED cache candidate, 2026-10-11. No Lean/Lake invocation was made.

Exact OUTSIDE-S conductor exponents for the actual arithmetic row character.
The character's sixth power is proved from the actual Kummer root values;
the tame upper bound is the formally integrated SexticTameConductor theorem.
The nonzero-exponent lower bound is the preceding actual row ramification
candidate. At exponent zero the existing good-prime Kummer unramified theorem
is used with the SAME chosen integral sixth-power S-unit representative.

No ramification, conductor bound, principal-unit kernel, or coefficient
calibration conclusion is assumed. The original S, row, unit sector and
representative are retained. Unit-ideal rows have zero conductor exponent
outside S, irrespective of their sector. NOTHING is claimed at primes in S.

The CFT chain, ArithmeticRowCharacterInput, the good-prime adapter and the
ramification candidates still await native compatibility checking. The first
two imports are bare cache modules, not formal modules; their checked cache
artifacts must precede checking this candidate. Earlier drafts are unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Characters.ArithmeticKummerDraft
open HeckeGeneral.Analysis HeckeGeneral.Analysis.PrimeCalibrationDraft
open HeckeGeneral.ThetaSkeleton.Global
open GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S)

/-- Equality of actual continuous Hecke characters, obtained from the
pointwise sixth-power identity of the actual arithmetic Kummer construction. -/
theorem arithmeticRowCharacter_pow_six_eq_one (v : FrequencyRow K S) :
    arithmeticRowCharacter K S P v ^ 6 = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  change arithmeticRowCharacter K S P v x ^ 6 = 1
  dsimp only [arithmeticRowCharacter]
  exact arithmeticSexticKummerCharacter_pow K _ _ _ x

/-- A row exponent zero is exactly the required good-prime case. The
proof uses the original representative relation, rather than deleting a mask. -/
theorem arithmeticRowCharacter_unramified_of_exponent_zero
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hz : primeExponents v.ideal.val p = 0) :
    UnramifiedAt K (arithmeticRowCharacter K S P v) p := by
  have hpv : ¬ p.asIdeal ∣ v.ideal.val.val := by
    intro hdvd
    have hm : idealPrimeMultiplicity K p v.ideal.val.val ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd
        (nonZeroDivisors.coe_ne_zero v.ideal.val) p.irreducible).mpr hdvd
    rw [idealPrimeMultiplicity_eq_primeExponents K v.ideal.val p, hz] at hm
    exact hm rfl
  let b := arithmeticRowIntegralRepresentative K S P v
  obtain ⟨γ, hrep⟩ := b.property.2
  change UnramifiedAt K
    (arithmeticSexticKummerCharacter K P.arithmetic.embedding
      ⟨P.arithmetic.root6,
        (mem_primitiveRoots (by norm_num)).mpr P.arithmetic.primitive6⟩
      (nonzeroIntegralFieldUnit K b.val b.property.1)) p
  exact frequencyRow_integer_representative_unramifiedAt K S P
    ⟨P.arithmetic.root6,
      (mem_primitiveRoots (by norm_num)).mpr P.arithmetic.primitive6⟩
    v b.val b.property.1 γ hrep p hp hpv

/-- Exact local conductor exponent outside the original fixed S: one on
the support of the original sixth-free row ideal, zero off that support. -/
theorem arithmeticRowCharacter_localConductorExponent_outside_S
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    localConductorExponent K (arithmeticRowCharacter K S P v) p =
      if primeExponents v.ideal.val p = 0 then 0 else 1 := by
  have hupper : localConductorExponent K (arithmeticRowCharacter K S P v) p ≤ 1 :=
    localConductorExponent_le_one_of_pow_six_eq_one K
      (arithmeticRowCharacter K S P v)
      (arithmeticRowCharacter_pow_six_eq_one K S P v) p
      (P.arithmetic.away_six p hp)
  by_cases hz : primeExponents v.ideal.val p = 0
  · rw [if_pos hz]
    exact (localConductorExponent_eq_zero_iff K _ p).mpr
      (arithmeticRowCharacter_unramified_of_exponent_zero K S P v p hp hz)
  · rw [if_neg hz]
    have hram := arithmeticRowCharacter_not_unramified_of_pos_exponent
      K S P v p hp (Nat.pos_of_ne_zero hz)
    have hnonzero : localConductorExponent K (arithmeticRowCharacter K S P v) p ≠ 0 :=
      fun hzero => hram ((localConductorExponent_eq_zero_iff K _ p).mp hzero)
    omega

/-- The same exact exponent on the actual candidate R projection. Its
coefficient-calibration field is neither changed nor used in this theorem. -/
theorem arithmeticRowCharacterInput_localConductorExponent_outside_S
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    localConductorExponent K ((arithmeticRowCharacterInput K S P).character v) p =
      if primeExponents v.ideal.val p = 0 then 0 else 1 := by
  change localConductorExponent K ((arithmeticRowCharacterInput K S P).character v) p = _
  exact arithmeticRowCharacter_localConductorExponent_outside_S K S P v p hp

/-- The genuine integral conductor ideal has the radical's local exponent
outside S. This is the local entry point for a later conductor-norm comparison;
no control of its additional S-prime factors is asserted here. -/
theorem arithmeticRowCharacter_finiteConductor_primeExponents_outside_S
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    primeExponents (finiteConductor K (arithmeticRowCharacter K S P v)) p =
      if primeExponents v.ideal.val p = 0 then 0 else 1 := by
  rw [primeExponents_finiteConductor, conductorExponents_apply]
  exact arithmeticRowCharacter_localConductorExponent_outside_S K S P v p hp

/-- All unit-ideal sectors are unramified outside S. This does not discard
the sector, identify its character with one, or assert unramifiedness inside S. -/
theorem arithmeticRowCharacter_unitIdeal_localConductorExponent_outside_S
    (v : FrequencyRow K S) (hv : v.ideal.val = 1)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    localConductorExponent K (arithmeticRowCharacter K S P v) p = 0 := by
  rw [arithmeticRowCharacter_localConductorExponent_outside_S K S P v p hp]
  have hz : primeExponents v.ideal.val p = 0 := by
    rw [hv, primeExponents_one]
    rfl
  rw [if_pos hz]

end HeckeGeneral.ThetaSkeleton.Physical
