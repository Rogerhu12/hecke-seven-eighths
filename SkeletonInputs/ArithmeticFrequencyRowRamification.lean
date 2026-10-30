import ArithmeticRowCharacterInput
import ArithmeticSexticKummerRamification
import HeckeGeneral.Analysis.SIntegerSixthPowerDenominatorMask
import HeckeGeneral.Arithmetic.SIntegerIdealSaturation

/-!
UNCOMPILED cache candidate, 2026-10-11. No Lean/Lake invocation was made.

The first import is the existing independent candidate in
.cache/sixth-denominator-mask-20261011/ArithmeticRowCharacterInput.lean;
its bare module artifact and its CFT dependencies must be checked first.
No coefficient-calibration result is used in the ramification proof below.

For ANY integral sixth-power S-unit representative b of the original row,
ordinary multiplicity at p outside S equals primeExponents of that row's
exterior ideal exactly. This follows by equality of principal ideals in
O_S, contraction, and deletion of exactly S-prime factors of ordinary (b).
We never identify the full ordinary ideal (b) with the exterior ideal.
The original unit sector and the sixth-power S-unit are both retained.

The CFT signed valuation is minus this multiplicity. The preceding actual
Kummer ramification candidate therefore proves that the actual constructed
row character is ramified whenever the displayed exponent is nonzero mod 6.
Its distinction from a fixed character unramified there is then immediate.
Nonunit sixth-free exterior ideals supply such a prime automatically.
Unit-ideal rows, even nontrivial sixth-unit sectors, are NOT asserted to be
ramified anywhere: they remain the separate finite exceptional alternative.

This file uses the current actual row API `primeExponents v.ideal.val p`;
there is no additional assumed exteriorPrimeExponents/valuation interface.
All assertions remain candidates until the cache/CFT chain is natively checked.
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

/-- Any integral representative in the ORIGINAL sixth-power S-unit class
has the original exterior multiplicity at every prime outside the same S. -/
theorem frequencyRow_integerSixthRepresentative_multiplicity
    (v : FrequencyRow K S) (b : 𝓞 K) (hb : b ≠ 0) (γ : S.unit K)
    (hrep : algebraMap (𝓞 K) (S.integer K) b =
      (S.unitEquivUnitsInteger K γ).val ^ 6 * frequencyRowElement K S P v)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    idealPrimeMultiplicity K p (Ideal.span {b}) = primeExponents v.ideal.val p := by
  let J := nonzeroIntegralPrincipalIdeal K b hb
  have hmap : J.val.map (algebraMap (𝓞 K) (S.integer K)) =
      Ideal.span ({algebraMap (𝓞 K) (S.integer K) b} : Set (S.integer K)) := by
    change (Ideal.span ({b} : Set (𝓞 K))).map
      (algebraMap (𝓞 K) (S.integer K)) = _
    rw [Ideal.map_span, Set.image_singleton]
  have hcontraction : sIntegerModulusContraction K S
      (algebraMap (𝓞 K) (S.integer K) b) = (outsideSIdeal K S J).val := by
    unfold sIntegerModulusContraction
    rw [← hmap]
    exact under_map_ideal_eq_outsideSIdeal K S J
  have hsame : outsideSIdeal K S J = v.ideal.val := by
    apply Subtype.ext
    exact hcontraction.symm.trans
      ((sIntegerModulusContraction_eq_of_sixthPower_sUnit_representative
        K S (frequencyRowElement K S P v) b γ hrep).trans
          (frequencyRowElement_contraction K S P v))
  have hexp := congrArg (fun I : NonzeroIdeal K => primeExponents I p) hsame
  rw [outsideSIdeal, primeExponents_idealOfPrimeExponents,
    outsideSPrimeExponents, Finsupp.filter_apply_pos (fun p => p ∉ S) _ hp] at hexp
  calc
    _ = primeExponents J p := idealPrimeMultiplicity_eq_primeExponents K J p
    _ = _ := hexp

/-- The particular chosen representative of the actual row character
retains this equality, without forgetting its chosen sixth-power S-unit. -/
theorem arithmeticRowIntegralRepresentative_multiplicity
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    idealPrimeMultiplicity K p
      (Ideal.span {(arithmeticRowIntegralRepresentative K S P v).val}) =
        primeExponents v.ideal.val p := by
  let b := arithmeticRowIntegralRepresentative K S P v
  obtain ⟨γ, hrep⟩ := b.property.2
  exact frequencyRow_integerSixthRepresentative_multiplicity
    K S P v b.val b.property.1 γ hrep p hp

/-- The signed local CFT valuation is the NEGATIVE original row exponent. -/
theorem arithmeticRowIntegralRepresentative_signedValuation
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    finitePlaceNormalizedValuation K p
      (nonzeroIntegralFieldUnit K (arithmeticRowIntegralRepresentative K S P v).val
        (arithmeticRowIntegralRepresentative K S P v).property.1) =
      -(primeExponents v.ideal.val p : ℤ) := by
  rw [finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit,
    arithmeticRowIntegralRepresentative_multiplicity K S P v p hp]

/-- Actual ramification of the constructed row character, not a condition
added to RowCharacterInput. The coefficient-calibration field is not used. -/
theorem arithmeticRowCharacter_not_unramified_of_exponent_mod_six
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hmod : primeExponents v.ideal.val p % 6 ≠ 0) :
    ¬ UnramifiedAt K (arithmeticRowCharacter K S P v) p := by
  let b := arithmeticRowIntegralRepresentative K S P v
  have hmodb : idealPrimeMultiplicity K p (Ideal.span {b.val}) % 6 ≠ 0 := by
    dsimp only [b]
    rw [arithmeticRowIntegralRepresentative_multiplicity K S P v p hp]
    exact hmod
  change ¬ UnramifiedAt K
    (arithmeticSexticKummerCharacter K P.arithmetic.embedding
      ⟨P.arithmetic.root6,
        (mem_primitiveRoots (by norm_num)).mpr P.arithmetic.primitive6⟩
      (nonzeroIntegralFieldUnit K b.val b.property.1)) p
  exact arithmeticSexticKummerCharacter_not_unramified_of_integral_multiplicity
    K P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
      p (P.arithmetic.away_six p hp) b.val b.property.1 hmodb

/-- Sixth-power freeness makes every positive row exponent lie in 1,...,5. -/
theorem arithmeticRowCharacter_not_unramified_of_pos_exponent
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpos : 0 < primeExponents v.ideal.val p) :
    ¬ UnramifiedAt K (arithmeticRowCharacter K S P v) p := by
  apply arithmeticRowCharacter_not_unramified_of_exponent_mod_six K S P v p hp
  rw [Nat.mod_eq_of_lt (v.sixthPowerFree p)]
  exact Nat.ne_of_gt hpos

/-- The actual character differs from every fixed character unramified
at the displayed ramified prime. No full-Theta exclusion is assumed. -/
theorem arithmeticRowCharacter_ne_of_unramified_at_exponent_prime
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpos : 0 < primeExponents v.ideal.val p)
    (θ : HeckeCharacter K) (hθ : UnramifiedAt K θ p) :
    arithmeticRowCharacter K S P v ≠ θ := by
  intro heq
  apply arithmeticRowCharacter_not_unramified_of_pos_exponent K S P v p hp hpos
  rw [heq]
  exact hθ

/-- Distinction from an entire fixed exceptional family follows if each
member is unramified at that prime, as ensured after its conductors enter S. -/
theorem arithmeticRowCharacter_not_mem_unramified_family_at_exponent_prime
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpos : 0 < primeExponents v.ideal.val p)
    (T : Finset (HeckeCharacter K)) (hT : ∀ θ ∈ T, UnramifiedAt K θ p) :
    arithmeticRowCharacter K S P v ∉ T := by
  intro hmem
  exact arithmeticRowCharacter_ne_of_unramified_at_exponent_prime
    K S P v p hp hpos (arithmeticRowCharacter K S P v) (hT _ hmem) rfl

/-- Exactly the nonunit IDEAL condition supplies a nonzero exterior prime
exponent. No assertion is made for nontrivial sectors with unit ideal. -/
theorem frequencyRow_exists_pos_exponent_of_ideal_ne_one
    (v : FrequencyRow K S) (hv : v.ideal.val ≠ 1) :
    ∃ p : HeightOneSpectrum (𝓞 K), p ∉ S ∧ 0 < primeExponents v.ideal.val p := by
  have hex : ∃ p : HeightOneSpectrum (𝓞 K), 0 < primeExponents v.ideal.val p := by
    by_contra hnone
    have he : primeExponents v.ideal.val = 0 := by
      ext p
      exact Nat.eq_zero_of_not_pos (fun h => hnone ⟨p, h⟩)
    apply hv
    calc
      _ = idealOfPrimeExponents (primeExponents v.ideal.val) :=
        (idealOfPrimeExponents_primeExponents v.ideal.val).symm
      _ = idealOfPrimeExponents (0 : HeightOneSpectrum (𝓞 K) →₀ ℕ) :=
        congrArg idealOfPrimeExponents he
      _ = 1 := idealOfPrimeExponents_zero
  obtain ⟨p, hpos⟩ := hex
  have hm : idealPrimeMultiplicity K p v.ideal.val.val ≠ 0 := by
    rw [idealPrimeMultiplicity_eq_primeExponents K v.ideal.val p]
    exact Nat.ne_of_gt hpos
  have hdvd : p.asIdeal ∣ v.ideal.val.val :=
    (Associates.count_ne_zero_iff_dvd
      (nonZeroDivisors.coe_ne_zero v.ideal.val) p.irreducible).mp hm
  exact ⟨p, v.ideal.property p hdvd, hpos⟩

/-- Every nonunit-ideal actual row is distinguished from a fixed family
whose members are unramified outside S. Unit sectors remain uncollapsed. -/
theorem arithmeticRowCharacter_not_mem_unramified_family_of_ideal_ne_one
    (v : FrequencyRow K S) (hv : v.ideal.val ≠ 1)
    (T : Finset (HeckeCharacter K))
    (hT : ∀ θ ∈ T, ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p) :
    arithmeticRowCharacter K S P v ∉ T := by
  obtain ⟨p, hp, hpos⟩ := frequencyRow_exists_pos_exponent_of_ideal_ne_one K S v hv
  exact arithmeticRowCharacter_not_mem_unramified_family_at_exponent_prime
    K S P v p hp hpos T (fun θ hθ => hT θ hθ p hp)

/-- In particular the original nonprincipal filter follows for nonunit
ideal rows, without imposing any condition on their actual unit sector. -/
theorem arithmeticRowCharacter_ne_one_of_ideal_ne_one
    (v : FrequencyRow K S) (hv : v.ideal.val ≠ 1) :
    arithmeticRowCharacter K S P v ≠ 1 := by
  obtain ⟨p, hp, hpos⟩ := frequencyRow_exists_pos_exponent_of_ideal_ne_one K S v hv
  exact arithmeticRowCharacter_ne_of_unramified_at_exponent_prime
    K S P v p hp hpos 1 (unramifiedAt_one K p)

/-- The same exclusion on the actual candidate R, with no replacement of
its character or coefficient-calibration fields. -/
theorem arithmeticRowCharacterInput_not_mem_unramified_family_of_ideal_ne_one
    (v : FrequencyRow K S) (hv : v.ideal.val ≠ 1)
    (T : Finset (HeckeCharacter K))
    (hT : ∀ θ ∈ T, ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p) :
    (arithmeticRowCharacterInput K S P).character v ∉ T :=
  arithmeticRowCharacter_not_mem_unramified_family_of_ideal_ne_one K S P v hv T hT

end HeckeGeneral.ThetaSkeleton.Physical
