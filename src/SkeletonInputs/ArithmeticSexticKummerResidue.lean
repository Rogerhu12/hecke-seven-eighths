import ArithmeticSexticKummerLocalComponent
import HeckeGeneral.Characters.SexticPowerResidueComparison
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity

/-!
UNCOMPILED cache candidate, 2026-10-11.

Arithmetic normalization is essential: the geometric root character at x
has Hilbert value H(x,a). Arithmetic inversion and skew symmetry give H(a,x).
For a prime-unit integral radicand b and nonzero integral input x, this is
the positive power-residue value raised to the prime multiplicity of (x).

No local-component, reciprocity, coefficient-calibration or unramifiedness
conclusion is supplied as a hypothesis. The two preceding actual-character
cache drafts and the upstream CFT imports still require native checking.
This file does not yet identify primeCoefficient: that also needs the
unramifiedness theorem and a global integral uniformizer specialization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ArithmeticKummerDraft

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols

variable (K : Type) [Field K] [NumberField K]

private theorem residueSixNeZero : (6 : K) ≠ 0 := by norm_num

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- The local component at a global unit, with the radicand first in the
Hilbert symbol. Both inversions are explicit in the proof. -/
theorem arithmeticSexticKummerCharacter_localComponent_globalUnit
    (embedding : K →+* ℂ) (hmu : (primitiveRoots 6 K).Nonempty)
    (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    localComponent K v (arithmeticSexticKummerCharacter K embedding hmu a)
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) =
      sixthRootsToCircle K embedding
        (finitePlaceHilbertSymbol K (6 : ℕ+) (residueSixNeZero K) hmu v a x) := by
  let E := sexticExtension K a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K (6 : ℕ+) (residueSixNeZero K) a
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K (6 : ℕ+) (residueSixNeZero K) hmu a
  rw [arithmeticSexticKummerCharacter_localComponent_apply]
  change simpleSexticCircleHom K embedding hmu a
      (arithmeticChosenFinitePlaceArtinMonoidHom K E v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x)) = _
  rw [arithmeticChosenFinitePlaceArtinMonoidHom_apply, map_inv]
  have hgeometric :
      simpleSexticCircleHom K embedding hmu a
          (chosenFinitePlaceArtinMonoidHom (K := K) (L := E) v
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x)) =
        sixthRootsToCircle K embedding
          (finitePlaceKummerRootCharacter K (6 : ℕ+) (residueSixNeZero K) hmu v x a) := by
    rfl
  erw [hgeometric, finitePlaceKummerRootCharacter_localGlobal, ← map_inv]
  exact congrArg (sixthRootsToCircle K embedding)
    (finitePlaceHilbertSymbol_skew K (6 : ℕ+) (residueSixNeZero K) hmu v a x).symm

/-- Integral roots use the same actual complex embedding as the sextic
residue evaluator; no arbitrary root identification is introduced. -/
theorem coe_sixthRootsToCircle_integralRoots (embedding : K →+* ℂ)
    (r : rootsOfUnity 6 (𝓞 K)) :
    (sixthRootsToCircle K embedding (integralRootsOfUnityToNthRoots K 6 r) : ℂ) =
      embedding (algebraMap (𝓞 K) K (r.val : 𝓞 K)) := by
  rfl

/-- Exact positive power-residue formula for an integral local input.
The exponent is the ordinary prime multiplicity of that input, not a
supposed equality between ordinary and S-integer principal ideals. -/
theorem arithmeticSexticKummerCharacter_localComponent_integral
    (embedding : K →+* ℂ) (hmu : (primitiveRoots 6 K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueExponentFinitePlaces K (6 : ℕ+))
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime 6)
    (b x : 𝓞 K) (hb : b ≠ 0) (hx : x ≠ 0) (hbv : b ∉ v.asIdeal) :
    (localComponent K v
        (arithmeticSexticKummerCharacter K embedding hmu (nonzeroIntegralFieldUnit K b hb))
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
          (nonzeroIntegralFieldUnit K x hx)) : ℂ) =
      embedding (algebraMap (𝓞 K) K
        ((primeIdealPowerResidueSymbol K v (6 : ℕ+) hmu hcoprime b hbv).val : 𝓞 K)) ^
          idealPrimeMultiplicity K v (Ideal.span {x}) := by
  have h := congrArg (fun z : Circle => (z : ℂ))
    (arithmeticSexticKummerCharacter_localComponent_globalUnit K embedding hmu
      (nonzeroIntegralFieldUnit K b hb) v (nonzeroIntegralFieldUnit K x hx))
  rw [finitePlaceHilbertSymbol_integral_eq_primeIdealPowerResidueFactor
    K (6 : ℕ+) (residueSixNeZero K) hmu v hv hcoprime b x hb hx hbv] at h
  erw [_root_.map_pow (sixthRootsToCircle K embedding)
    (integralRootsOfUnityToNthRoots K 6
      (primeIdealPowerResidueSymbol K v (6 : ℕ+) hmu hcoprime b hbv))
    (idealPrimeMultiplicity K v (Ideal.span {x})), Circle.coe_pow,
    coe_sixthRootsToCircle_integralRoots] at h
  exact h

/-- The same formula expressed in the project's specified-root sextic
evaluation, with the original exponent-prime exclusion. -/
theorem arithmeticSexticKummerCharacter_localComponent_sexticEvaluation
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (embedding : K →+* ℂ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (6 : 𝓞 K) ∉ v.asIdeal)
    (b x : 𝓞 K) (hb : b ≠ 0) (hx : x ≠ 0) (hbv : b ∉ v.asIdeal) :
    (localComponent K v
        (arithmeticSexticKummerCharacter K embedding
          ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩ (nonzeroIntegralFieldUnit K b hb))
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
          (nonzeroIntegralFieldUnit K x hx)) : ℂ) =
      sexticResidueEvaluation K ζ hζ embedding v hv b ^
        idealPrimeMultiplicity K v (Ideal.span {x}) := by
  have hv' : v ∉ powerResidueExponentFinitePlaces K (6 : ℕ+) := by
    simpa only [mem_powerResidueExponentFinitePlaces_iff,
      powerResidueExponentIdeal, Ideal.dvd_span_singleton,
      PNat.val_ofNat, Nat.cast_ofNat] using hv
  rw [arithmeticSexticKummerCharacter_localComponent_integral K embedding
    ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩ v hv'
    (specifiedSexticNormCoprime K ζ hζ v hv) b x hb hx hbv]
  rw [sexticResidueEvaluation_eq_powerResidueSymbol K ζ hζ embedding v hv b hbv]

end HeckeGeneral.Characters.ArithmeticKummerDraft
