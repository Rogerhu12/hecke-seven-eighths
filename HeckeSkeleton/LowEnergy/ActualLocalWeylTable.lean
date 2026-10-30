import HeckeSkeleton.LowEnergy.ActualFrozenCube
import HeckeSkeleton.LowEnergy.LocalWeylTableCore

/-! The finite-field table instantiated with the project's actual local definitions. -/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualLocalWeylTable

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowFrozenCube
open HeckeSkeleton.LowEnergy.ActualFrozenCube
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local instance residueField (p : ExteriorPrime K S) : Field (𝓞 K ⧸ p.val.asIdeal) :=
  Ideal.Quotient.field _

local instance residueFintype (p : ExteriorPrime K S) : Fintype (𝓞 K ⧸ p.val.asIdeal) :=
  Fintype.ofFinite _

def residueAddChar (p : ExteriorPrime K S) : AddChar (𝓞 K ⧸ p.val.asIdeal) ℂ :=
  transportCharacter (thetaPrimeResidueEquiv K S p)
    (thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p))

theorem residueAddChar_primitive (p : ExteriorPrime K S) :
    (residueAddChar K S D p).IsPrimitive :=
  transportCharacter_isPrimitive _ _
    (thetaPrincipalAddCharacter_isPrimitive K S D (exteriorPrimeIdeal K S p))

theorem thetaPrimeCharacter_order (p : ExteriorPrime K S) :
    orderOf (thetaPrimeCharacter K S D p) = 6 :=
  sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property)

/-- No alternate local table is substituted: this is the literal finite sum. -/
theorem localWeylScalar_eq_core (p : ExteriorPrime K S) (j : Fin 6) (e : ℕ) :
    localWeylScalar K S D p j e =
      LocalWeylTableCore.localScalar (thetaPrimeCharacter K S D p)
        (residueAddChar K S D p) (thetaGamma K S D (exteriorPrimeIdeal K S p) 2) j e := by
  have hcard : Fintype.card (𝓞 K ⧸ p.val.asIdeal) = p.val.asIdeal.absNorm :=
    card_primeIdealResidueField K p.val
  have hs : sphericalDigit K S D p e = LocalWeylTableCore.spherical
      (F := 𝓞 K ⧸ p.val.asIdeal) (thetaGamma K S D (exteriorPrimeIdeal K S p) 2) e := by
    simp only [sphericalDigit, LocalWeylTableCore.spherical, hcard]
  have ht : localTau K S D p j = LocalWeylTableCore.tau
      (thetaPrimeCharacter K S D p) (residueAddChar K S D p) j := rfl
  unfold localWeylScalar LocalWeylTableCore.localScalar
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  have hm : digitMask K S D p j u = LocalWeylTableCore.mask
      (thetaPrimeCharacter K S D p) (residueAddChar K S D p) j u := by
    unfold digitMask LocalWeylTableCore.mask
    rw [hcard, ht]
    by_cases hj : j.val = 0 <;> simp only [hj, if_pos, if_neg, Units.ne_zero]
  rw [hm]
  rfl

theorem localWeylScalar_zero_norm (p : ExteriorPrime K S) (j : Fin 6) :
    ‖localWeylScalar K S D p j 0‖ =
      if j.val = 0 ∨ j.val = 4 then (Real.sqrt (p.val.asIdeal.absNorm : ℝ))⁻¹ else 1 := by
  rw [localWeylScalar_eq_core]
  simpa only [card_primeIdealResidueField K p.val] using
    LocalWeylTableCore.localScalar_zero_norm (thetaPrimeCharacter K S D p)
      (residueAddChar K S D p) (thetaPrimeCharacter_order K S D p)
      (residueAddChar_primitive K S D p) _ j

theorem localWeylScalar_positive_eq_zero (p : ExteriorPrime K S)
    (j : Fin 6) (e : ℕ) (he : 0 < e) (hj : j.val ≠ 4) :
    localWeylScalar K S D p j e = 0 := by
  rw [localWeylScalar_eq_core]
  exact LocalWeylTableCore.localScalar_positive_eq_zero (thetaPrimeCharacter K S D p)
    (residueAddChar K S D p) (thetaPrimeCharacter_order K S D p) _ j e he hj

theorem localWeylScalar_one_norm_le (p : ExteriorPrime K S) (j : Fin 6) :
    ‖localWeylScalar K S D p j 1‖ ≤ 1 := by
  rw [localWeylScalar_eq_core]
  exact LocalWeylTableCore.localScalar_one_norm_le (thetaPrimeCharacter K S D p)
    (residueAddChar K S D p) (thetaPrimeCharacter_order K S D p)
    (residueAddChar_primitive K S D p) _ (thetaGamma_exteriorPrime_two_norm K S D p) j

theorem localWeylScalar_three_norm_le (p : ExteriorPrime K S) (j : Fin 6) :
    ‖localWeylScalar K S D p j 3‖ ≤ (Real.sqrt (p.val.asIdeal.absNorm : ℝ))⁻¹ := by
  rw [localWeylScalar_eq_core]
  simpa only [card_primeIdealResidueField K p.val] using
    LocalWeylTableCore.localScalar_three_norm_le (thetaPrimeCharacter K S D p)
      (residueAddChar K S D p) (thetaPrimeCharacter_order K S D p)
      (residueAddChar_primitive K S D p) _ j

/-- All local support and inverse-square-root charges are explicit. -/
def minimumMajorant (p : ExteriorPrime K S) (j : Fin 6) (m : ℕ) : ℝ :=
  if m = 0 then
    if j.val = 0 ∨ j.val = 4 then (Real.sqrt (p.val.asIdeal.absNorm : ℝ))⁻¹ else 1
  else if j.val = 4 then
    if m = 1 then 1 else if m = 3 then (Real.sqrt (p.val.asIdeal.absNorm : ℝ))⁻¹ else 0
  else 0

theorem minimumMajorant_nonneg (p : ExteriorPrime K S) (j : Fin 6) (m : ℕ) :
    0 ≤ minimumMajorant K S p j m := by
  unfold minimumMajorant
  split_ifs <;> positivity

theorem localWeylScalar_minimum_norm_le (p : ExteriorPrime K S) (j : Fin 6) (e : ℕ) :
    ‖localWeylScalar K S D p j (frozenMin e)‖ ≤
      minimumMajorant K S p j (frozenMin e) := by
  rcases frozenMin_cases e with hm | hm | hm
  · rw [hm, localWeylScalar_zero_norm]
    simp only [minimumMajorant, if_pos rfl]
  · rw [hm]
    by_cases hj : j.val = 4
    · simpa only [minimumMajorant, if_neg (by decide : ¬(1 : ℕ) = 0), if_pos hj,
        if_pos rfl] using localWeylScalar_one_norm_le K S D p j
    · rw [localWeylScalar_positive_eq_zero K S D p j 1 (by decide) hj]
      simp [minimumMajorant, hj]
  · rw [hm]
    by_cases hj : j.val = 4
    · simpa only [minimumMajorant, if_neg (by decide : ¬(3 : ℕ) = 0), if_pos hj,
        if_neg (by decide : ¬(3 : ℕ) = 1), if_pos rfl] using
        localWeylScalar_three_norm_le K S D p j
    · rw [localWeylScalar_positive_eq_zero K S D p j 3 (by decide) hj]
      simp [minimumMajorant, hj]

/-- Literal local table decay, including its exact vanishing branches. -/
theorem localWeylScalar_norm_frozen (p : ExteriorPrime K S) (j : Fin 6)
    (e : ℕ) (he : AdmissibleExponent e) :
    ‖localWeylScalar K S D p j e‖ ≤
      (p.val.asIdeal.absNorm : ℝ)⁻¹ ^ frozenCubeExp e *
        minimumMajorant K S p j (frozenMin e) := by
  rw [localWeylScalar_frozen K S D p j e he, norm_mul, norm_pow, norm_inv,
    Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (localWeylScalar_minimum_norm_le K S D p j e)
    (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)

end HeckeSkeleton.LowEnergy.ActualLocalWeylTable
