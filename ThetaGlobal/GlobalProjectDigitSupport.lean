import ThetaGlobal.GlobalDigitSupport
import ThetaGlobal.GlobalProjectFrequency

/-! Exact scalar support rules for the project's literal Weyl digit sum.
The representation-theoretic equality with a local Whittaker digit remains
a permitted local input; no global reflection is used here. -/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectDigitSupport

open NumberField IsDedekindDomain HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
  (D : ThetaArithmeticData K S)

theorem localWeylScalar_positive_zero (p : ExteriorPrime K S)
    (j : Fin 6) (hj : j.val ≠ 4) (e : ℕ) (he : e ≠ 0) :
    localWeylScalar K S D p j e = 0 := by
  by_cases hz : j.val = 0
  · have hj0 : j = 0 := Fin.ext hz
    subst j
    exact GlobalProjectFrequency.localWeylScalar_zero_digit_positive K S D p e he
  · letI : Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _
    letI : Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _
    unfold localWeylScalar
    simp only [digitMask, if_neg hz, if_neg he, mul_one]
    exact GlobalDigitSupport.ordinary_positive_digit_sum_zero
      (thetaPrimeCharacter K S D p)
      (GlobalProjectFrequency.thetaPrimeCharacter_order_six K S D p) j hj
      (localTau K S D p j)⁻¹ (sphericalDigit K S D p e)

theorem moving_row_nonzero_implies_zero_exponent (p : ExteriorPrime K S)
    (e : ℕ) (h : localWeylScalar K S D p ⟨1, by decide⟩ e ≠ 0) : e = 0 := by
  by_contra he
  exact h (localWeylScalar_positive_zero K S D p ⟨1, by decide⟩ (by decide) e he)

theorem sphericalDigit_nonzero_mod_three (p : ExteriorPrime K S) (e : ℕ)
    (h : sphericalDigit K S D p e ≠ 0) : e % 3 ≠ 2 := by
  intro he
  apply h
  simp [sphericalDigit, he]

theorem localWeylScalar_nonzero_mod_three (p : ExteriorPrime K S)
    (j : Fin 6) (e : ℕ) (h : localWeylScalar K S D p j e ≠ 0) : e % 3 ≠ 2 := by
  apply sphericalDigit_nonzero_mod_three K S D p e
  intro hz
  apply h
  simp [localWeylScalar, hz]

end ThetaGlobal.GlobalProjectDigitSupport
