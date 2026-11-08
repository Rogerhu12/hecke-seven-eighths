module

public import ThetaGlobal.GlobalProjectWeightedSheet
public import ThetaGlobal.GlobalProjectFrequency

@[expose] public section

/-!
# Literal project masks in the actual finite digit average

This adapter uses the project's `digitMask`, including its special j=0
unit cutoff, and the literal marked constant `absNorm(p)⁻¹`.  Its
invariance proof only uses the genuine exact-order-six residue character.
No identification of a Gauss normalization is required for this descent
step; the local evaluation theorem subsequently sees these exact weights.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectLiteralDigitWeights

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical BigOperators

/-- The literal marked average is the complement of the zeroth ordinary
digit.  This is the local identity behind finite inclusion--exclusion. -/
theorem marked_eq_delta_sub_zero_digit
    (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (D : ThetaArithmeticData K S) (p : ExteriorPrime K S)
    (x : 𝓞 K ⧸ p.val.asIdeal) :
    (p.val.asIdeal.absNorm : ℂ)⁻¹ =
      (if x = 0 then 1 else 0) - digitMask K S D p 0 x := by
  by_cases hx : x = 0 <;> simp [digitMask, hx]

theorem digitMask_mul_sixth
    (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (D : ThetaArithmeticData K S) (p : ExteriorPrime K S)
    (z : (𝓞 K ⧸ p.val.asIdeal)ˣ) (j : Fin 6) (x : 𝓞 K ⧸ p.val.asIdeal) :
    digitMask K S D p j ((z : 𝓞 K ⧸ p.val.asIdeal) ^ 6 * x) =
      digitMask K S D p j x := by
  letI : Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _
  have hz : thetaPrimeCharacter K S D p ((z : 𝓞 K ⧸ p.val.asIdeal) ^ 6) = 1 :=
    ThetaDigitDescent.chi_sixth_pow_eq_one _
      (GlobalProjectFrequency.thetaPrimeCharacter_order_six K S D p) z.ne_zero
  have hzero : (z : 𝓞 K ⧸ p.val.asIdeal) ^ 6 * x = 0 ↔ x = 0 :=
    mul_eq_zero.trans (or_iff_right (pow_ne_zero _ z.ne_zero))
  unfold digitMask
  simp only [hzero, map_mul, hz, one_mul]

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

def exteriorPlace (m : ThetaReflectionData.Row R.A)
    (p : GlobalProjectWeightedDigits.Places R m) :
    ExteriorPrime F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) :=
  ⟨p.val, ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩

def tensorWeight
    (D : ThetaArithmeticData F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool)
    (d : GlobalProjectWeightedDigits.Digits R m) : ℂ :=
  ∏ p : GlobalProjectWeightedDigits.Places R m,
    if marked p then (p.val.asIdeal.absNorm : ℂ)⁻¹ else
      digitMask F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) D
        (exteriorPlace R m p) (j p) (d p)

/-- Literal ordinary masks, punctures with j=0, and marked constants
all satisfy the exact reindexing condition of the actual sheet theorem. -/
theorem tensorWeight_reindexInvariant
    (D : ThetaArithmeticData F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool) :
    GlobalProjectWeightedDigits.ReindexInvariant R m (tensorWeight R D m j marked) := by
  intro u d
  unfold tensorWeight
  apply Finset.prod_congr rfl
  intro p _
  split_ifs
  · rfl
  · let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
    obtain ⟨z, hz⟩ := DigitMasks.residueSixthUnit_is_sixth R ⟨p.val, hp⟩ u
    change digitMask F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) D
      (exteriorPlace R m p) (j p)
      ((ThetaDigitDescent.residueSixthUnit R.A p.val hp u : ThetaDigitAverage.Residue p.val) * d p) = _
    rw [hz, Units.val_pow_eq_pow_val]
    exact digitMask_mul_sixth F _ D (exteriorPlace R m p) z (j p) (d p)

end ThetaGlobal.GlobalProjectLiteralDigitWeights
