import ArithmeticFrequencyRowCharacterFibers
import RowCharacterCanonicalUniqueness
import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The local six-divisibility detected by the original row characters

An integral unit with sextic residue value of exact order six tests a
product of two actual row characters. If that product is unramified,
the sum of the two complete ideal multiplicities is divisible by six.
The two original unit sectors are retained throughout.
-/

noncomputable section
open scoped Classical nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Characters.ArithmeticKummerDraft
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.PrimeCalibrationDraft
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols

variable {K : Type} [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S)

local instance valuationResidueField (p : HeightOneSpectrum (𝓞 K)) :
    Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _

local instance valuationResidueFintype (p : HeightOneSpectrum (𝓞 K)) :
    Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _

private theorem exists_primeUnit_order_six
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
  obtain ⟨u, hu⟩ := HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.exists_unitCharacter_order_six
    F h6 ζF ζC hF hC
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : F)
  have hxv : x ∉ p.asIdeal := by
    intro hxmem
    have hz : Ideal.Quotient.mk p.asIdeal x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hxmem
    exact u.ne_zero (hx.symm.trans hz)
  let c : ℂˣ := HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.unitCharacter
    F h6 ζF ζC hF hC u
  refine ⟨x, hxv, c, hu, ?_⟩
  change HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.character F h6 ζF ζC hF hC
    (Ideal.Quotient.mk p.asIdeal x) = (c : ℂ)
  rw [hx]
  exact HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.character_unit F h6 ζF ζC hF hC u

/-- The literal local component detects the sum of the two row
exponents, even when the individual characters are ramified. -/
theorem arithmeticRowCharacters_sum_exponent_dvd_six
    (v w : FrequencyRow K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hχ : UnramifiedAt K
      (arithmeticRowCharacter K S P v * arithmeticRowCharacter K S P w) p) :
    6 ∣ primeExponents v.ideal.val p + primeExponents w.ideal.val p := by
  obtain ⟨x, hx, c, hc, heval⟩ := exists_primeUnit_order_six S P p hp
  let y : (p.adicCompletion K)ˣ :=
    Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom
      (primeAvoidingIntegralFieldUnit K p x hx)
  have hy : ‖y.val‖ = 1 := primeAvoidingIntegralFieldUnit_local_norm_one K p x hx
  have hlocal : localComponent K p (arithmeticRowCharacter K S P v) y *
      localComponent K p (arithmeticRowCharacter K S P w) y = 1 := hχ y hy
  have hv := arithmeticRowCharacter_localComponent_primeUnit_zpow K S P v p hp x hx
  have hw := arithmeticRowCharacter_localComponent_primeUnit_zpow K S P w p hp x hx
  rw [heval] at hv hw
  have hpow : (c : ℂ) ^ (-(primeExponents v.ideal.val p : ℤ)) *
      (c : ℂ) ^ (-(primeExponents w.ideal.val p : ℤ)) = 1 := by
    have hcomplex := congrArg (fun z : Circle => (z : ℂ)) hlocal
    simp only [Circle.coe_mul, Circle.coe_one] at hcomplex
    rw [hv, hw] at hcomplex
    exact hcomplex
  have hpowUnits : c ^ (-(primeExponents v.ideal.val p : ℤ) +
      -(primeExponents w.ideal.val p : ℤ)) = 1 := by
    rw [zpow_add]
    apply Units.ext
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] using hpow
  have hdvd : (orderOf c : ℤ) ∣ -(primeExponents v.ideal.val p : ℤ) +
      -(primeExponents w.ideal.val p : ℤ) :=
    orderOf_dvd_iff_zpow_eq_one.mpr hpowUnits
  have hneg : (6 : ℤ) ∣ -((primeExponents v.ideal.val p +
      primeExponents w.ideal.val p : ℕ) : ℤ) := by
    simpa only [hc, Nat.cast_ofNat, Nat.cast_add, neg_add] using hdvd
  exact Int.natCast_dvd_natCast.mp (dvd_neg.mp hneg)

/-- Complete ideal rows have the same local exponent modulo six as
their sixth-free bases. This recovers the original complete exponents. -/
theorem completeRowCharacters_sum_exponent_dvd_six
    (R : RowCharacterInput K S P) (I J : ExteriorIdeal K S)
    (u v : SixthUnitClasses K S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hχ : UnramifiedAt K
      (completeIdealRowCharacter K S P R u I.val *
        completeIdealRowCharacter K S P R v J.val) p) :
    6 ∣ primeExponents I.val p + primeExponents J.val p := by
  simp only [completeIdealRowCharacter_exterior,
    rowCharacterInput_character_eq_arithmetic] at hχ
  have hbase := arithmeticRowCharacters_sum_exponent_dvd_six S P
    (decomposedFrequencyRow K S I u) (decomposedFrequencyRow K S J v) p hp hχ
  change 6 ∣ primeExponents (sixthPowerFreePart I.val) p +
    primeExponents (sixthPowerFreePart J.val) p at hbase
  rw [primeExponents_sixthPowerFreePart, primeExponents_sixthPowerFreePart] at hbase
  apply Nat.dvd_of_mod_eq_zero
  simpa only [Nat.add_mod, Nat.mod_mod] using Nat.mod_eq_zero_of_dvd hbase

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.arithmeticRowCharacters_sum_exponent_dvd_six
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.completeRowCharacters_sum_exponent_dvd_six
