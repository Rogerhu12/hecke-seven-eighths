import ArithmeticSexticKummerUnramified
import ArithmeticSexticKummerResidue
import HeckeGeneral.Characters.PrimeCoefficients
import Lean.Elab.Tactic.Omega

/-!
UNCOMPILED cache candidate, 2026-10-11. No Lean/Lake invocation was made.

The actual good-prime Euler coefficient of the arithmetic Kummer character
is the specified-root sextic residue evaluation. The integral uniformizer is
obtained from the existing Dedekind valuation theorem, not supplied as data.
Its multiplicity is proved to be one, and the existing norm-invariance API
avoids identifying it with the project's separately chosen localUniformizer.

All arithmetic Kummer predecessor candidates and the upstream closure
still require native checking. No bad-prime coefficient, S-integer coefficient
calibration, or RowCharacterInput is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ArithmeticKummerDraft

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols

variable (K : Type) [Field K] [NumberField K]

/-- A global integral uniformizer has ordinary prime multiplicity one.
This is a consequence of its actual valuation, not an additional hypothesis
on the uniformizer supplied to the coefficient theorem below. -/
theorem idealPrimeMultiplicity_eq_one_of_valuation_exp_neg_one
    (p : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0)
    (hval : p.valuation K (x : K) = WithZero.exp (-1 : ℤ)) :
    idealPrimeMultiplicity K p (Ideal.span {x}) = 1 := by
  rw [valuation_of_algebraMap,
    intValuation_eq_exp_neg_idealPrimeMultiplicity K p x hx] at hval
  have hexp := WithZero.exp_inj.mp hval
  omega

/-- The actual zero-extended prime coefficient at a good prime, with the
same embedding and specified sixth root as the residue evaluation. -/
theorem arithmeticSexticKummerCharacter_primeCoefficient
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (embedding : K →+* ℂ)
    (b : 𝓞 K) (hb : b ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (hbp : b ∉ p.asIdeal) :
    primeCoefficient K
        (arithmeticSexticKummerCharacter K embedding
          ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩
          (nonzeroIntegralFieldUnit K b hb)) p =
      sexticResidueEvaluation K ζ hζ embedding p h6 b := by
  have hχ : UnramifiedAt K
      (arithmeticSexticKummerCharacter K embedding
        ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩
        (nonzeroIntegralFieldUnit K b hb)) p := by
    apply arithmeticSexticKummerCharacter_unramifiedAt_of_valuation_eq_one
    · exact p.valuation_eq_one_iff_notMem.mpr hbp
    · exact p.valuation_eq_one_iff_notMem.mpr h6
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer' K
  have hπ0 : π ≠ 0 := by
    intro hzero
    have hbad := hπ
    simp only [hzero, map_zero] at hbad
    exact WithZero.exp_ne_zero hbad.symm
  have hmult : idealPrimeMultiplicity K p (Ideal.span {π}) = 1 :=
    idealPrimeMultiplicity_eq_one_of_valuation_exp_neg_one K p π hπ0 hπ
  let πlocal : (p.adicCompletion K)ˣ :=
    Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom
      (nonzeroIntegralFieldUnit K π hπ0)
  have hπnorm : ‖πlocal.val‖ = (residueCard K p : ℝ)⁻¹ := by
    apply localNorm_eq_inv_residueCard_of_valuation K p
    change Valued.v ((π : K) : p.adicCompletion K) = WithZero.exp (-1 : ℤ)
    rw [valuedAdicCompletion_eq_valuation']
    exact hπ
  rw [primeCoefficient_eq_of_norm K _ p hχ πlocal hπnorm]
  simpa only [πlocal, hmult, pow_one] using
    arithmeticSexticKummerCharacter_localComponent_sexticEvaluation
      K ζ hζ embedding p h6 b π hb hπ0 hbp

end HeckeGeneral.Characters.ArithmeticKummerDraft
