import ThetaGlobal.GlobalProjectForwardCoefficients

/-!
# Local support extracted from the actual digit coefficient

The optional ordinary-zero branch and the marked branch are active only
at order -2.  A moving digit is active only at order -2.  All inactive
places have nonnegative order congruent to zero or one modulo three.
These are proved consequences of the literal finite tables and are the
inputs to actual ideal-coordinate reconstruction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectLocalSupport

open NumberField IsDedekindDomain DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectLocalDigitTables ThetaGlobal.GlobalProjectDigitProduct
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

variable (Adata : ThetaArithmeticData F ((R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))))

def localValue (p : P) (j : Fin 6) (marked : Bool) (x : Fˣ) : ℂ :=
  inactiveCoefficient R Adata p j marked x + activeCoefficient R Adata p j marked x

theorem spherical_nonzero (p : P) (x : Fˣ)
    (hx : sphericalValue R Adata p x ≠ 0) :
    0 ≤ ThetaBranch.order p.val x ∧ (ThetaBranch.order p.val x).toNat % 3 ≠ 2 := by
  have hn : ¬ ThetaBranch.order p.val x < 0 := by
    intro h
    exact hx (by simp [sphericalValue, h])
  refine ⟨le_of_not_gt hn, ?_⟩
  apply GlobalProjectDigitSupport.sphericalDigit_nonzero_mod_three F Sf Adata
    (skeletonPrime R p) _
  intro hz
  exact hx (by rw [sphericalValue, if_neg hn, hz, zero_mul])

theorem active_nonzero (p : P) (j : Fin 6) (x : Fˣ)
    (hx : activeValue R Adata p j x ≠ 0) :
    -2 ≤ ThetaBranch.order p.val x ∧
      (ThetaBranch.order p.val x + 2).toNat % 3 ≠ 2 ∧
      (j.val ≠ 4 → ThetaBranch.order p.val x = -2) := by
  have hn : ¬ ThetaBranch.order p.val x + 2 < 0 := by
    intro h
    exact hx (by simp [activeValue, h])
  have hw : localWeylScalar F Sf Adata (skeletonPrime R p) j
      (ThetaBranch.order p.val x + 2).toNat ≠ 0 := by
    intro hz
    exact hx (by rw [activeValue, if_neg hn, hz, zero_mul])
  refine ⟨by omega,
    GlobalProjectDigitSupport.localWeylScalar_nonzero_mod_three F Sf Adata _ _ _ hw, ?_⟩
  intro hj
  have he : (ThetaBranch.order p.val x + 2).toNat = 0 := by
    by_contra he
    exact hw (GlobalProjectDigitSupport.localWeylScalar_positive_zero F Sf Adata _ j hj _ he)
  omega

theorem active_zero_digit (p : P) (x : Fˣ) (hx : ThetaBranch.order p.val x ≠ -2) :
    activeValue R Adata p 0 x = 0 := by
  by_cases he : ThetaBranch.order p.val x + 2 < 0
  · simp [activeValue, he]
  · have hn : (ThetaBranch.order p.val x + 2).toNat ≠ 0 := by omega
    simp only [activeValue, if_neg he,
      GlobalProjectFrequency.localWeylScalar_zero_digit_positive F Sf Adata _ _ hn, zero_mul]

theorem localValue_nonzero_lower (p : P) (j : Fin 6) (marked : Bool) (x : Fˣ)
    (hx : localValue R Adata p j marked x ≠ 0) : -2 ≤ ThetaBranch.order p.val x := by
  by_contra hn
  have hs : ThetaBranch.order p.val x < 0 := by omega
  have he : ThetaBranch.order p.val x + 2 < 0 := by omega
  have hm : ThetaBranch.order p.val x ≠ -2 := by omega
  apply hx
  cases marked <;>
    simp [localValue, inactiveCoefficient, activeCoefficient, sphericalValue, activeValue,
      markedActive, hs, he, hm]

theorem localValue_nonzero_mandatory (p : P) (j : Fin 6) (hj : j.val ≠ 0)
    (x : Fˣ) (hx : localValue R Adata p j false x ≠ 0) :
    activeValue R Adata p j x ≠ 0 := by
  simpa only [localValue, inactiveCoefficient, activeCoefficient,
    Bool.false_eq_true, if_false, if_neg hj, zero_mul, zero_add] using hx

theorem localValue_nonzero_mandatory_digits (p : P) (j : Fin 6) (hj : j.val ≠ 0)
    (x : Fˣ) (hx : localValue R Adata p j false x ≠ 0) :
    (ThetaBranch.order p.val x + 2).toNat % 3 ≠ 2 :=
  (active_nonzero R Adata p j x (localValue_nonzero_mandatory R Adata p j hj x hx)).2.1

theorem localValue_moving (p : P) (x : Fˣ)
    (hx : localValue R Adata p ⟨1, by decide⟩ false x ≠ 0) :
    ThetaBranch.order p.val x = -2 :=
  (active_nonzero R Adata p ⟨1, by decide⟩ x
    (localValue_nonzero_mandatory R Adata p _ (by decide) x hx)).2.2 (by decide)

theorem localValue_optional_negative (p : P) (marked : Bool) (x : Fˣ)
    (hx : localValue R Adata p 0 marked x ≠ 0)
    (hn : ThetaBranch.order p.val x < 0) : ThetaBranch.order p.val x = -2 := by
  by_contra hm
  apply hx
  cases marked with
  | false => simp [localValue, inactiveCoefficient, activeCoefficient, sphericalValue, hn,
      active_zero_digit R Adata p x hm]
  | true => simp [localValue, inactiveCoefficient, activeCoefficient, sphericalValue,
      markedActive, hn, hm]

theorem localValue_optional_nonnegative (p : P) (marked : Bool) (x : Fˣ)
    (hx : localValue R Adata p 0 marked x ≠ 0)
    (hn : 0 ≤ ThetaBranch.order p.val x) :
    (ThetaBranch.order p.val x).toNat % 3 ≠ 2 := by
  apply (spherical_nonzero R Adata p x ?_).2
  intro hz
  have hm : ThetaBranch.order p.val x ≠ -2 := by omega
  apply hx
  cases marked with
  | false => simp [localValue, inactiveCoefficient, activeCoefficient, hz,
      active_zero_digit R Adata p x hm]
  | true => simp [localValue, inactiveCoefficient, activeCoefficient, markedActive, hz, hm]

variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)
  (H : Input R D Adata)

include H in
theorem row_nonzero (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool) (x : Fˣ)
    (hx : GlobalProjectSignedExtraction.reverseCoefficient R D m
      (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked) x ≠ 0)
    (p : RowPrime R m) :
    localValue R Adata (exteriorRowPrime R m p) (j p) (marked p) x ≠ 0 := by
  rw [reverseCoefficient_literal_product R D Adata H] at hx
  exact Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).1 p (Finset.mem_univ p)

include H in
theorem off_row_nonzero (E : ExteriorCoefficients R Q T D)
    (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool) (x : Fˣ)
    (hx : GlobalProjectSignedExtraction.reverseCoefficient R D m
      (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked) x ≠ 0)
    (p : P) (hp : p ∉ exteriorRows R m) : sphericalValue R Adata p x ≠ 0 := by
  rw [reverseCoefficient_literal_product R D Adata H] at hx
  have ho := (mul_ne_zero_iff.mp hx).2
  intro hz
  apply ho
  have hf : Function.HasFiniteMulSupport (fun q : P =>
      if q ∈ exteriorRows R m then 1 else D.exteriorValue R q x) := by
    apply (GlobalProjectForwardCoefficients.exteriorProduct_finite R D E x).subset
    intro q hq
    by_cases hmem : q ∈ exteriorRows R m
    · exact False.elim (hq (if_pos hmem))
    · simpa only [Function.mem_mulSupport, if_neg hmem] using hq
  exact finprod_eq_zero _ p (by rw [if_neg hp, H.diagonal p x, hz]) hf

end ThetaGlobal.GlobalProjectLocalSupport
