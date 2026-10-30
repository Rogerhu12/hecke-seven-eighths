import ArithmeticSexticKummerLocalComponent
import HeckeGeneral.Characters.Unramified
import HeckeGeneral.Arithmetic.SIntegerModulusValuation
import HeckeGeneral.Analysis.FrequencyRowOrbit
import ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior

/-!
UNCOMPILED cache candidate, 2026-10-11. No compiler was launched.

This proves only the good-prime unramified adapter for the concrete arithmetic
Artin/Kummer character. The multiplicative valuation equals 1 (additive order
0); no coefficient orientation or converse ramification statement is asserted.
The integral representative and sixth-power S-unit precede the varying prime.
The original row ideal is retained; no norm bound on its representative is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem sInteger_valuation_eq_one_of_not_dvd_contraction
    (a : S.integer K) (ha : a ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpa : ¬ p.asIdeal ∣ sIntegerModulusContraction K S a) :
    p.valuation K (a : K) = 1 := by
  have hexp : sIntegerModulusPrimeExponents K S a ha p = 0 := by
    change (normalizedFactors (sIntegerModulusContraction K S a)).count p.asIdeal = 0
    apply Multiset.count_eq_zero_of_notMem
    intro hmem
    exact hpa (dvd_of_mem_normalizedFactors hmem)
  rw [sIntegerModulus_valuation K S a ha p hp, hexp]
  simp

theorem integer_sixthPower_sUnit_representative_valuation_eq_one
    (a : S.integer K) (ha : a ≠ 0) (b : 𝓞 K) (u : S.unit K)
    (hrep : algebraMap (𝓞 K) (S.integer K) b =
      (S.unitEquivUnitsInteger K u).val ^ 6 * a)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpa : ¬ p.asIdeal ∣ sIntegerModulusContraction K S a) :
    p.valuation K (b : K) = 1 := by
  have hfield : (b : K) = ((u : Kˣ) : K) ^ 6 * (a : K) :=
    congrArg (fun z : S.integer K => (z : K)) hrep
  rw [hfield, map_mul, map_pow, Set.unit_valuation_eq_one S K u hp,
    sInteger_valuation_eq_one_of_not_dvd_contraction K S a ha p hp hpa,
    one_pow, mul_one]

end HeckeGeneral.Arithmetic

namespace HeckeGeneral.Characters.ArithmeticKummerDraft

open NumberField IsDedekindDomain KummerTheory
open HeckeGeneral.Arithmetic
open GlobalClassFieldTheory.Reciprocity

variable (K : Type) [Field K] [NumberField K]

private theorem six_nonzero : (6 : K) ≠ 0 := by norm_num

set_option maxHeartbeats 1000000 in
/-- The standard unit-radicand theorem gives actual local-unit triviality.
The hypotheses are elementary valuations, not desired unramifiedness. -/
theorem arithmeticSexticKummerCharacter_unramifiedAt_of_valuation_eq_one
    (embedding : K →+* ℂ) (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ)
    (p : HeightOneSpectrum (𝓞 K))
    (ha : p.valuation K (a : K) = 1) (h6 : p.valuation K (6 : K) = 1) :
    UnramifiedAt K (arithmeticSexticKummerCharacter K embedding hmu a) p := by
  let E := sexticExtension K a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K (6 : ℕ+) (six_nonzero K) a
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K (6 : ℕ+) (six_nonzero K) hmu a
  have hunram : ChosenFinitePlaceIsUnramified (K := K) (L := E) p :=
    chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
      (K := K) (6 : ℕ+) (six_nonzero K) hmu a p ha h6
  apply (unramifiedAt_iff_integral_units K _ p).mpr
  intro x hx
  have hnorm : x ∈ chosenFinitePlaceLocalNormSubgroup (K := K) (L := E) p :=
    adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := E) p hunram hx
  have hgeom : chosenFinitePlaceArtinMonoidHom (K := K) (L := E) p x = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [chosenFinitePlaceArtinMonoidHom_ker]
    exact hnorm
  have harith : arithmeticChosenFinitePlaceArtinMonoidHom K E p x = 1 :=
    (arithmeticChosenFinitePlaceArtinMonoidHom_apply K E p x).trans (by
      rw [hgeom, inv_one])
  exact (arithmeticSexticKummerCharacter_localComponent_apply
    K embedding hmu a p x).trans <| by
      change simpleSexticCircleHom K embedding hmu a
        (arithmeticChosenFinitePlaceArtinMonoidHom K E p x) = 1
      exact (congrArg (simpleSexticCircleHom K embedding hmu a) harith).trans
        (map_one (simpleSexticCircleHom K embedding hmu a))

/-- Fixing b and u once gives all good primes of the original actual row.
Bad primes remain outside this theorem; their original mask is not removed. -/
theorem arithmeticSexticKummerCharacter_integer_representative_unramifiedAt
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (embedding : K →+* ℂ) (hmu : (primitiveRoots 6 K).Nonempty)
    (a : S.integer K) (ha : a ≠ 0) (b : 𝓞 K) (hb : b ≠ 0) (u : S.unit K)
    (hrep : algebraMap (𝓞 K) (S.integer K) b =
      (S.unitEquivUnitsInteger K u).val ^ 6 * a)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpa : ¬ p.asIdeal ∣ sIntegerModulusContraction K S a)
    (h6 : (6 : 𝓞 K) ∉ p.asIdeal) :
    UnramifiedAt K
      (arithmeticSexticKummerCharacter K embedding hmu
        (Units.mk0 (b : K) (fun h => hb (Subtype.ext h)))) p := by
  apply arithmeticSexticKummerCharacter_unramifiedAt_of_valuation_eq_one
  · exact integer_sixthPower_sUnit_representative_valuation_eq_one
      K S a ha b u hrep p hp hpa
  · exact p.valuation_eq_one_iff_notMem.mpr h6

end HeckeGeneral.Characters.ArithmeticKummerDraft

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Characters.ArithmeticKummerDraft

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem frequencyRow_integer_representative_unramifiedAt
    (P : ProbeData K S) (hmu : (primitiveRoots 6 K).Nonempty)
    (v : FrequencyRow K S) (b : 𝓞 K) (hb : b ≠ 0) (u : S.unit K)
    (hrep : algebraMap (𝓞 K) (S.integer K) b =
      (S.unitEquivUnitsInteger K u).val ^ 6 * frequencyRowElement K S P v)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpv : ¬ p.asIdeal ∣ v.ideal.val.val) :
    UnramifiedAt K
      (arithmeticSexticKummerCharacter K P.arithmetic.embedding hmu
        (Units.mk0 (b : K) (fun h => hb (Subtype.ext h)))) p := by
  apply arithmeticSexticKummerCharacter_integer_representative_unramifiedAt
    K S P.arithmetic.embedding hmu (frequencyRowElement K S P v)
    (frequencyRowElement_ne_zero K S P v) b hb u hrep p hp
  · simpa only [frequencyRowElement_contraction] using hpv
  · exact P.arithmetic.away_six p hp

end HeckeGeneral.ThetaSkeleton.Physical
