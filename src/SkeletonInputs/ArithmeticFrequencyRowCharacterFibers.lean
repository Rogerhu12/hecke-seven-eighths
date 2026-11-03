import ArithmeticFrequencyRowRamification
import Mathlib.Data.Int.ModEq
import Mathlib.SetTheory.Cardinal.Finite

/-!
UNCOMPILED cache candidate, 2026-10-11. No Lean/Lake invocation.

Actual arithmetic Kummer row-character fibers. A residue-unit lift whose
specified sextic residue value has EXACT order six detects the entire row
exponent modulo six, not merely the ramification support. Sixth-power-free
rows then have identical ideal exponents. Every original unit sector remains.

No character injectivity, fiber bound, Kummer multiplicativity, allowed
generator compatibility, or desired ramification conclusion is assumed.
The twist theorem explicitly requires the displayed theta to be unramified
outside the ORIGINAL S. The same-character fiber theorem has no such input.
This does NOT establish that the complete exceptional Theta family is
unramified outside S. AllowedGeneratorInput has no such field, and finite
order alone does not imply it. The final finite-family bound counts genuine
exceptional rows; it does not assert their exclusion or change S.

The bare import and its arithmetic/CFT dependency chain remain candidates.
All older drafts are frozen. Native checking is pending.
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

local instance fiberResidueField (p : HeightOneSpectrum (𝓞 K)) :
    Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _

local instance fiberResidueFintype (p : HeightOneSpectrum (𝓞 K)) :
    Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _

/-- The preceding true local-component formula, now calibrated to the
NEGATIVE exponent of the original row ideal. Unit sectors and the chosen
integral sixth-power S-unit representative are both retained. -/
theorem arithmeticRowCharacter_localComponent_primeUnit_zpow
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (x : 𝓞 K) (hx : x ∉ p.asIdeal) :
    (localComponent K p (arithmeticRowCharacter K S P v)
      (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom
        (primeAvoidingIntegralFieldUnit K p x hx)) : ℂ) =
      sexticResidueEvaluation K P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding p (P.arithmetic.away_six p hp) x ^
          (-(primeExponents v.ideal.val p : ℤ)) := by
  have h := arithmeticSexticKummerCharacter_localComponent_primeUnit_zpow
    K P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
    (nonzeroIntegralFieldUnit K (arithmeticRowIntegralRepresentative K S P v).val
      (arithmeticRowIntegralRepresentative K S P v).property.1)
    p (P.arithmetic.away_six p hp) x hx
  change (localComponent K p (arithmeticRowCharacter K S P v)
    (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom
      (primeAvoidingIntegralFieldUnit K p x hx)) : ℂ) = _ at h
  rw [arithmeticRowIntegralRepresentative_signedValuation K S P v p hp] at h
  exact h

/-- An actual integral prime-unit test detecting every exponent modulo six.
The exact-order value and its integral lift are constructed, not supplied. -/
private theorem exists_primeUnit_residue_value_order_six
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    ∃ x : 𝓞 K, x ∉ p.asIdeal ∧ ∃ c : ℂˣ, orderOf c = 6 ∧
      sexticResidueEvaluation K P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding p (P.arithmetic.away_six p hp) x = (c : ℂ) := by
  let F := 𝓞 K ⧸ p.asIdeal
  let h6 := six_dvd_card_residue_sub_one K P.arithmetic.root6
    P.arithmetic.primitive6 p (P.arithmetic.away_six p hp)
  let ζF := sexticResidueRootUnit K P.arithmetic.root6 P.arithmetic.primitive6 p
  let ζC := sexticComplexRootUnit K P.arithmetic.root6 P.arithmetic.primitive6
    P.arithmetic.embedding
  let hF := isPrimitiveRoot_sexticResidueRootUnit K P.arithmetic.root6
    P.arithmetic.primitive6 p (P.arithmetic.away_six p hp)
  let hC := isPrimitiveRoot_sexticComplexRootUnit K P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding
  obtain ⟨u, hu⟩ := Arithmetic.FiniteFieldSexticCharacter.exists_unitCharacter_order_six
    F h6 ζF ζC hF hC
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : F)
  have hxv : x ∉ p.asIdeal := by
    intro hxmem
    have hz : Ideal.Quotient.mk p.asIdeal x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hxmem
    exact u.ne_zero (hx.symm.trans hz)
  let c : ℂˣ := Arithmetic.FiniteFieldSexticCharacter.unitCharacter
    F h6 ζF ζC hF hC u
  refine ⟨x, hxv, c, hu, ?_⟩
  change Arithmetic.FiniteFieldSexticCharacter.character F h6 ζF ζC hF hC
    (Ideal.Quotient.mk p.asIdeal x) = (c : ℂ)
  rw [hx]
  exact Arithmetic.FiniteFieldSexticCharacter.character_unit F h6 ζF ζC hF hC u

/-- A true character relation, tested on the constructed local unit, forces
congruence of the ORIGINAL ideal exponents. The background theta may have
arbitrary behavior elsewhere; only its displayed local unramifiedness is used. -/
theorem arithmeticRowCharacter_primeExponents_modEq_of_eq_mul_unramifiedAt
    (v w : FrequencyRow K S) (θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) (hθ : UnramifiedAt K θ p)
    (hχ : arithmeticRowCharacter K S P v = arithmeticRowCharacter K S P w * θ) :
    (primeExponents v.ideal.val p : ℤ) ≡
      (primeExponents w.ideal.val p : ℤ) [ZMOD 6] := by
  obtain ⟨x, hx, c, hc, heval⟩ := exists_primeUnit_residue_value_order_six K S P p hp
  let y : (p.adicCompletion K)ˣ :=
    Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom
      (primeAvoidingIntegralFieldUnit K p x hx)
  have hy : ‖y.val‖ = 1 := primeAvoidingIntegralFieldUnit_local_norm_one K p x hx
  have hlocal : localComponent K p (arithmeticRowCharacter K S P v) y =
      localComponent K p (arithmeticRowCharacter K S P w) y := by
    calc
      _ = localComponent K p (arithmeticRowCharacter K S P w * θ) y :=
        congrArg (fun η : HeckeCharacter K => localComponent K p η y) hχ
      _ = localComponent K p (arithmeticRowCharacter K S P w) y *
          localComponent K p θ y := rfl
      _ = _ := by rw [hθ y hy, mul_one]
  have hv := arithmeticRowCharacter_localComponent_primeUnit_zpow K S P v p hp x hx
  have hw := arithmeticRowCharacter_localComponent_primeUnit_zpow K S P w p hp x hx
  rw [heval] at hv hw
  have hpow : (c : ℂ) ^ (-(primeExponents v.ideal.val p : ℤ)) =
      (c : ℂ) ^ (-(primeExponents w.ideal.val p : ℤ)) :=
    hv.symm.trans ((congrArg (fun z : Circle => (z : ℂ)) hlocal).trans hw)
  have hpowUnits : c ^ (-(primeExponents v.ideal.val p : ℤ)) =
      c ^ (-(primeExponents w.ideal.val p : ℤ)) := by
    apply Units.ext
    simpa only [Units.val_zpow_eq_zpow_val] using hpow
  have hmod := zpow_eq_zpow_iff_modEq.mp hpowUnits
  simpa only [hc, Nat.cast_ofNat, Int.neg_modEq_neg] using hmod

theorem arithmeticRowCharacter_primeExponents_eq_of_eq_mul_unramifiedAt
    (v w : FrequencyRow K S) (θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) (hθ : UnramifiedAt K θ p)
    (hχ : arithmeticRowCharacter K S P v = arithmeticRowCharacter K S P w * θ) :
    primeExponents v.ideal.val p = primeExponents w.ideal.val p := by
  have hm := arithmeticRowCharacter_primeExponents_modEq_of_eq_mul_unramifiedAt
    K S P v w θ p hp hθ hχ
  have hnat : Nat.ModEq 6 (primeExponents v.ideal.val p) (primeExponents w.ideal.val p) :=
    Int.natCast_modEq_iff.mp hm
  change primeExponents v.ideal.val p % 6 = primeExponents w.ideal.val p % 6 at hnat
  simpa only [Nat.mod_eq_of_lt (v.sixthPowerFree p),
    Nat.mod_eq_of_lt (w.sixthPowerFree p)] using hnat

/-- Exterior row ideals have zero exponents on the unchanged S. -/
private theorem frequencyRow_primeExponents_zero_of_mem
    (v : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) :
    primeExponents v.ideal.val p = 0 := by
  by_contra hz
  have hm : idealPrimeMultiplicity K p v.ideal.val.val ≠ 0 := by
    rw [idealPrimeMultiplicity_eq_primeExponents K v.ideal.val p]
    exact hz
  have hdvd : p.asIdeal ∣ v.ideal.val.val :=
    (Associates.count_ne_zero_iff_dvd
      (nonZeroDivisors.coe_ne_zero v.ideal.val) p.irreducible).mp hm
  exact v.ideal.property p hdvd hp

/-- Characters differing by any displayed S-exterior-unramified twist have
identical sixth-free exterior ideals. This does not identify their sectors. -/
theorem arithmeticRowCharacter_ideal_eq_of_eq_mul_exterior_unramified
    (v w : FrequencyRow K S) (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hχ : arithmeticRowCharacter K S P v = arithmeticRowCharacter K S P w * θ) :
    v.ideal = w.ideal := by
  have he : primeExponents v.ideal.val = primeExponents w.ideal.val := by
    ext p
    by_cases hp : p ∈ S
    · rw [frequencyRow_primeExponents_zero_of_mem K S v p hp,
        frequencyRow_primeExponents_zero_of_mem K S w p hp]
    · exact arithmeticRowCharacter_primeExponents_eq_of_eq_mul_unramifiedAt
        K S P v w θ p hp (hθ p hp) hχ
  apply Subtype.ext
  exact (primeExponentEquiv (R := 𝓞 K)).injective he

/-- No additional arithmetic assumption is needed for equal actual characters. -/
theorem arithmeticRowCharacter_ideal_eq_of_eq (v w : FrequencyRow K S)
    (hχ : arithmeticRowCharacter K S P v = arithmeticRowCharacter K S P w) :
    v.ideal = w.ideal := by
  apply arithmeticRowCharacter_ideal_eq_of_eq_mul_exterior_unramified K S P v w 1
  · exact fun p _ => unramifiedAt_one K p
  · simpa only [mul_one] using hχ

private theorem frequencyRow_eq_of_ideal_eq_sector_eq (v w : FrequencyRow K S)
    (hi : v.ideal = w.ideal) (hs : v.sector = w.sector) : v = w := by
  cases v with
  | mk I hI s =>
    cases w with
    | mk J hJ t =>
      dsimp only at hi hs
      cases hi
      cases hs
      rfl

/-- The true fiber embeds in the ORIGINAL finite unit-sector type. -/
theorem arithmeticRowCharacter_fiber_sector_injective (η : HeckeCharacter K) :
    Function.Injective (fun v : {v : FrequencyRow K S //
      arithmeticRowCharacter K S P v = η} => v.val.sector) := by
  intro v w hs
  apply Subtype.ext
  exact frequencyRow_eq_of_ideal_eq_sector_eq K S v.val w.val
    (arithmeticRowCharacter_ideal_eq_of_eq K S P v.val w.val
      (v.property.trans w.property.symm)) hs

theorem arithmeticRowCharacter_fiber_finite (η : HeckeCharacter K) :
    Finite {v : FrequencyRow K S // arithmeticRowCharacter K S P v = η} :=
  Finite.of_injective (fun v : {v : FrequencyRow K S //
    arithmeticRowCharacter K S P v = η} => v.val.sector)
    (arithmeticRowCharacter_fiber_sector_injective K S P η)

/-- Uniform over EVERY target character, with no bound or injectivity input. -/
theorem arithmeticRowCharacter_fiber_card_le (η : HeckeCharacter K) :
    Nat.card {v : FrequencyRow K S // arithmeticRowCharacter K S P v = η} ≤
      Nat.card (SixthUnitClasses K S) :=
  Nat.card_le_card_of_injective (fun v : {v : FrequencyRow K S //
    arithmeticRowCharacter K S P v = η} => v.val.sector)
    (arithmeticRowCharacter_fiber_sector_injective K S P η)

/-- A finite exceptional character family gives finitely many actual rows,
even without classifying that family as unramified outside S. -/
theorem arithmeticRowCharacter_finiteFamily_sector_injective
    (T : Finset (HeckeCharacter K)) :
    Function.Injective (fun v : {v : FrequencyRow K S //
      arithmeticRowCharacter K S P v ∈ T} =>
      ((⟨arithmeticRowCharacter K S P v.val, v.property⟩,
        v.val.sector) : T × SixthUnitClasses K S)) := by
  intro v w he
  have hχ : arithmeticRowCharacter K S P v.val = arithmeticRowCharacter K S P w.val :=
    congrArg (fun t : T × SixthUnitClasses K S => t.1.val) he
  have hs : v.val.sector = w.val.sector := congrArg Prod.snd he
  apply Subtype.ext
  exact frequencyRow_eq_of_ideal_eq_sector_eq K S v.val w.val
    (arithmeticRowCharacter_ideal_eq_of_eq K S P v.val w.val hχ) hs

theorem arithmeticRowCharacter_finiteFamily_finite (T : Finset (HeckeCharacter K)) :
    Finite {v : FrequencyRow K S // arithmeticRowCharacter K S P v ∈ T} :=
  Finite.of_injective
    (fun v : {v : FrequencyRow K S // arithmeticRowCharacter K S P v ∈ T} =>
      ((⟨arithmeticRowCharacter K S P v.val, v.property⟩,
        v.val.sector) : T × SixthUnitClasses K S))
    (arithmeticRowCharacter_finiteFamily_sector_injective K S P T)

theorem arithmeticRowCharacter_finiteFamily_card_le (T : Finset (HeckeCharacter K)) :
    Nat.card {v : FrequencyRow K S // arithmeticRowCharacter K S P v ∈ T} ≤
      T.card * Nat.card (SixthUnitClasses K S) := by
  have h := Nat.card_le_card_of_injective
    (fun v : {v : FrequencyRow K S // arithmeticRowCharacter K S P v ∈ T} =>
      ((⟨arithmeticRowCharacter K S P v.val, v.property⟩,
        v.val.sector) : T × SixthUnitClasses K S))
    (arithmeticRowCharacter_finiteFamily_sector_injective K S P T)
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe] using h

end HeckeGeneral.ThetaSkeleton.Physical
