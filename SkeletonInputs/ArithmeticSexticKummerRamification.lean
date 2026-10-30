import ArithmeticSexticKummerResidue
import HeckeGeneral.Characters.Unramified
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
UNCOMPILED cache candidate, 2026-10-11. No Lean/Lake invocation was made.

Actual ramification of the arithmetic Artin/Kummer Hecke character when
the radicand's local multiplicity is not divisible by six. This uses no
supplied ramification, nontriviality or kernel-containment conclusion.
The CFT chain and the preceding three cache modules still await native
compatibility checks; this file is a proof candidate, not audited evidence.

Fixed upstream: 2eb22d6485af45f29c5219de6c49f196a61c4f49.
PowerResidueReciprocity source SHA256:
4bbafe6fc14edd0fd10c357cfd64364c7fcbf9a0c237860df34be428c2fd86be.
The relevant source is GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity:
* finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor_zpow takes an
  integral PRIME-UNIT first entry x and an ARBITRARY field-unit second
  entry a. In particular the radicand a need not be a local integral unit.
* finitePlaceHilbertSymbol_skew interchanges the two entries and inverts.
* finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit identifies the
  upstream normalized valuation with NEGATIVE ordinary prime multiplicity.

Arithmetic normalization gives the actual local value H(a,x). Applying
skew before the tame formula gives residue(x)^(normalized valuation a).
Thus for integral radicand b the exponent is -multiplicity(b). This is not
an application of the earlier good-prime unit-radicand formula to b.

The finite-field exact-order-six witness is constructed by the existing
FiniteFieldSexticCharacter.exists_unitCharacter_order_six theorem. A lift
of this residue unit is a genuine integral local unit. Unramifiedness would
force its value to one, contradicting the proved exact order. The final
integral corollary allows arbitrary positive multiplicity not 0 modulo 6,
not merely multiplicities one or five and not merely squarefree radicands.

For physical frequency rows a later literal calibration must identify this
signed valuation with minus the exterior ideal's primeExponents; no such
row-identification fact is asserted or assumed in this character theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Characters.ArithmeticKummerDraft

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

local instance ramificationResidueField (v : HeightOneSpectrum (𝓞 K)) :
    Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _

local instance ramificationResidueFintype (v : HeightOneSpectrum (𝓞 K)) :
    Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _

private theorem ramificationSixNeZero : (6 : K) ≠ 0 := by norm_num

/-- On an integral local unit, the actual arithmetic character of ANY
radicand is the specified residue character raised to the upstream signed
valuation. No local-unit hypothesis is imposed on the radicand a. -/
theorem arithmeticSexticKummerCharacter_localComponent_primeUnit_zpow
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (embedding : K →+* ℂ)
    (a : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hv : (6 : 𝓞 K) ∉ v.asIdeal)
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    (localComponent K v
        (arithmeticSexticKummerCharacter K embedding
          ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩ a)
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
          (primeAvoidingIntegralFieldUnit K v x hx)) : ℂ) =
      sexticResidueEvaluation K ζ hζ embedding v hv x ^
        finitePlaceNormalizedValuation K v a := by
  let hmu : (primitiveRoots 6 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩
  have hv' : v ∉ powerResidueExponentFinitePlaces K (6 : ℕ+) := by
    simpa only [mem_powerResidueExponentFinitePlaces_iff,
      powerResidueExponentIdeal, Ideal.dvd_span_singleton,
      PNat.val_ofNat, Nat.cast_ofNat] using hv
  have h := congrArg (fun z : Circle => (z : ℂ))
    (arithmeticSexticKummerCharacter_localComponent_globalUnit K embedding hmu
      a v (primeAvoidingIntegralFieldUnit K v x hx))
  rw [finitePlaceHilbertSymbol_skew K (6 : ℕ+) (ramificationSixNeZero K)
      hmu v a (primeAvoidingIntegralFieldUnit K v x hx),
    finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor_zpow K (6 : ℕ+)
      (ramificationSixNeZero K) hmu v hv'
      (specifiedSexticNormCoprime K ζ hζ v hv) x hx a] at h
  calc
    _ = embedding (algebraMap (𝓞 K) K
          ((primeIdealPowerResidueSymbol K v (6 : ℕ+) hmu
            (specifiedSexticNormCoprime K ζ hζ v hv) x hx).val : 𝓞 K)) ^
        finitePlaceNormalizedValuation K v a := by
      rw [← zpow_neg, neg_neg] at h
      erw [_root_.map_zpow (sixthRootsToCircle K embedding)
        (integralRootsOfUnityToNthRoots K 6
          (primeIdealPowerResidueSymbol K v (6 : ℕ+) hmu
            (specifiedSexticNormCoprime K ζ hζ v hv) x hx))
        (finitePlaceNormalizedValuation K v a), Circle.coe_zpow,
        coe_sixthRootsToCircle_integralRoots] at h
      exact h
    _ = _ := by
      rw [sexticResidueEvaluation_eq_powerResidueSymbol K ζ hζ embedding v hv x hx]

/-- A residue-unit lift is an actual unit of local norm one, even when it
is not a global integer-ring unit. This is the unit tested by UnramifiedAt. -/
theorem primeAvoidingIntegralFieldUnit_local_norm_one
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    ‖(Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
      (primeAvoidingIntegralFieldUnit K v x hx)).val‖ = 1 := by
  change ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 K) K x)‖ = 1
  exact (NumberField.FinitePlace.norm_eq_one_iff_notMem K v x).2 hx

/-- Non-divisibility of the actual signed local valuation forces genuine
ramification. No nonprincipal-character or local-value hypothesis occurs. -/
theorem arithmeticSexticKummerCharacter_not_unramified_of_valuation
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (embedding : K →+* ℂ)
    (a : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hv : (6 : 𝓞 K) ∉ v.asIdeal)
    (hval : ¬ (6 : ℤ) ∣ finitePlaceNormalizedValuation K v a) :
    ¬ UnramifiedAt K
      (arithmeticSexticKummerCharacter K embedding
        ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩ a) v := by
  intro hunram
  let F := 𝓞 K ⧸ v.asIdeal
  let h6 := six_dvd_card_residue_sub_one K ζ hζ v hv
  let ζF := sexticResidueRootUnit K ζ hζ v
  let ζC := sexticComplexRootUnit K ζ hζ embedding
  let hF := isPrimitiveRoot_sexticResidueRootUnit K ζ hζ v hv
  let hC := isPrimitiveRoot_sexticComplexRootUnit K ζ hζ embedding
  obtain ⟨u, hu⟩ :=
    Arithmetic.FiniteFieldSexticCharacter.exists_unitCharacter_order_six
      F h6 ζF ζC hF hC
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : F)
  have hxv : x ∉ v.asIdeal := by
    intro hxmem
    have hz : Ideal.Quotient.mk v.asIdeal x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hxmem
    exact u.ne_zero (hx.symm.trans hz)
  let c : ℂˣ := Arithmetic.FiniteFieldSexticCharacter.unitCharacter
    F h6 ζF ζC hF hC u
  have hc : orderOf c = 6 := hu
  have heval : sexticResidueEvaluation K ζ hζ embedding v hv x = (c : ℂ) := by
    change Arithmetic.FiniteFieldSexticCharacter.character F h6 ζF ζC hF hC
      (Ideal.Quotient.mk v.asIdeal x) = (c : ℂ)
    rw [hx]
    exact Arithmetic.FiniteFieldSexticCharacter.character_unit F h6 ζF ζC hF hC u
  have hlocal := arithmeticSexticKummerCharacter_localComponent_primeUnit_zpow
    K ζ hζ embedding a v hv x hxv
  rw [heval] at hlocal
  have hone := congrArg (fun z : Circle => (z : ℂ))
    (hunram _ (primeAvoidingIntegralFieldUnit_local_norm_one K v x hxv))
  have hpow : (c : ℂ) ^ finitePlaceNormalizedValuation K v a = 1 :=
    hlocal.symm.trans hone
  have hpowUnits : c ^ finitePlaceNormalizedValuation K v a = 1 := by
    apply Units.ext
    simpa only [Units.val_zpow_eq_zpow_val, Units.val_one] using hpow
  have hdvd : (orderOf c : ℤ) ∣ finitePlaceNormalizedValuation K v a :=
    orderOf_dvd_iff_zpow_eq_one.mpr hpowUnits
  apply hval
  simpa only [hc, Nat.cast_ofNat] using hdvd

/-- Integral radicands with multiplicity nonzero modulo six are ramified
at every prime not containing six. The normalized valuation is -multiplicity;
divisibility is unchanged by this sign, which is kept explicit in the proof. -/
theorem arithmeticSexticKummerCharacter_not_unramified_of_integral_multiplicity
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (embedding : K →+* ℂ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (6 : 𝓞 K) ∉ v.asIdeal)
    (b : 𝓞 K) (hb : b ≠ 0)
    (hmod : idealPrimeMultiplicity K v (Ideal.span {b}) % 6 ≠ 0) :
    ¬ UnramifiedAt K
      (arithmeticSexticKummerCharacter K embedding
        ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩
          (nonzeroIntegralFieldUnit K b hb)) v := by
  apply arithmeticSexticKummerCharacter_not_unramified_of_valuation K ζ hζ embedding
    (nonzeroIntegralFieldUnit K b hb) v hv
  intro hdiv
  rw [finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit] at hdiv
  have hdiv' : (6 : ℤ) ∣ (idealPrimeMultiplicity K v (Ideal.span {b}) : ℤ) :=
    dvd_neg.mp hdiv
  have hnat : 6 ∣ idealPrimeMultiplicity K v (Ideal.span {b}) :=
    Int.natCast_dvd_natCast.mp hdiv'
  exact hmod (Nat.mod_eq_zero_of_dvd hnat)

end HeckeGeneral.Characters.ArithmeticKummerDraft
