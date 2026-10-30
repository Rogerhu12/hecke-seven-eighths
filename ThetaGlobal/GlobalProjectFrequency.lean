module

public import ThetaGlobal.GlobalFrequency
public import ThetaGlobal.GlobalCharacterSums
public import HeckeGeneral.Analysis.MarkedThetaReflection
public import HeckeGeneral.Analysis.ThetaPrimeGaussNorm

@[expose] public section

/-!
# Actual local zero underlying support-level frequency uniqueness

The generic frequency theorem needs optional active ordinary primes to
have numerator exponent zero on nonzero support.  This file proves that
statement directly from the project's finite Weyl sum.  No local KP
table realization and no global reflection statement is assumed.

This is a project-facing module; see the separate compilation-status report.
-/

noncomputable section
open scoped BigOperators Classical

namespace ThetaGlobal.GlobalProjectFrequency

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
  (D : ThetaArithmeticData K S)

theorem thetaPrimeCharacter_order_six (p : ExteriorPrime K S) :
    orderOf (thetaPrimeCharacter K S D p) = 6 :=
  sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property)

/-- Every positive-valuation zeroth ordinary digit vanishes, including
the enlarged duplicate branch at exponent three. -/
theorem localWeylScalar_zero_digit_positive (p : ExteriorPrime K S)
    (e : ℕ) (he : e ≠ 0) :
    localWeylScalar K S D p (0 : Fin 6) e = 0 := by
  letI : Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _
  unfold localWeylScalar
  simp only [digitMask, Fin.val_zero, if_pos rfl, Units.ne_zero, if_false, he, mul_one]
  exact GlobalCharacterSums.ordinary_zero_digit_positive_sum
    (thetaPrimeCharacter K S D p) (thetaPrimeCharacter_order_six K S D p)
    (p.val.asIdeal.absNorm : ℂ)⁻¹ (sphericalDigit K S D p e)

theorem localWeylScalar_zero_digit_nonzero_implies_exponent_zero
    (p : ExteriorPrime K S) (e : ℕ)
    (h : localWeylScalar K S D p (0 : Fin 6) e ≠ 0) : e = 0 := by
  by_contra he
  exact h (localWeylScalar_zero_digit_positive K S D p e he)

theorem duplicate_branch_local_scalar_zero (p : ExteriorPrime K S) :
    localWeylScalar K S D p (0 : Fin 6) 3 = 0 :=
  localWeylScalar_zero_digit_positive K S D p 3 (by decide)

end ThetaGlobal.GlobalProjectFrequency
