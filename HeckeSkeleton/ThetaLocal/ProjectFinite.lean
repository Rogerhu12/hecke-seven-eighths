import HeckeSkeleton.ThetaLocal.ProjectResidue
import HeckeSkeleton.ThetaLocal.ExteriorPhaseSeparation
import HeckeSkeleton.ThetaLocal.ExteriorFourierMasks

/-!
# Exterior digit tables for the project's arithmetic objects

Every statement below uses the definitions in `MarkedThetaReflection`.
`ProjectResidue` supplies the residue cardinality, the exact sextic order,
the principal additive phase, and the normalized Gauss comparison.  The
finite-field calculations can therefore be applied without extra character
or normalization assumptions.
-/

set_option autoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Global

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeSkeleton.ThetaLocal
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local instance (p : ExteriorPrime K S) : Field (𝓞 K ⧸ p.val.asIdeal) :=
  Ideal.Quotient.field _

local instance (p : ExteriorPrime K S) : Fintype (𝓞 K ⧸ p.val.asIdeal) :=
  Fintype.ofFinite _


theorem localTau_eq_residueField (p : ExteriorPrime K S) (j : Fin 6) :
    localTau K S D p j =
      ResidueField.localTau (thetaPrimeCharacter K S D p) (projectPrimePhase K S D p) j := by
  unfold localTau ResidueField.localTau
  apply Finset.sum_congr rfl
  intro x _
  rw [projectPrimePhase_apply]

theorem digitMask_eq_residueField (p : ExteriorPrime K S) (j : Fin 6)
    (x : 𝓞 K ⧸ p.val.asIdeal) :
    digitMask K S D p j x =
      ResidueField.digitMask (thetaPrimeCharacter K S D p) (projectPrimePhase K S D p) j x := by
  simp only [digitMask, ResidueField.digitMask, residue_card_eq_absNorm K S p,
    ← localTau_eq_residueField K S D p j]

theorem sphericalDigit_eq_residueField (p : ExteriorPrime K S) (e : ℕ) :
    sphericalDigit K S D p e =
      ResidueField.sphericalDigit (thetaPrimeCharacter K S D p) (projectPrimePhase K S D p) e := by
  simp only [sphericalDigit, ResidueField.sphericalDigit, residue_card_eq_absNorm K S p,
    ← thetaGamma_two_eq_gammaTwo K S D p]

theorem localWeylScalar_eq_residueField (p : ExteriorPrime K S) (j : Fin 6) (e : ℕ) :
    localWeylScalar K S D p j e =
      ResidueField.localWeylScalar (thetaPrimeCharacter K S D p) (projectPrimePhase K S D p) j e := by
  unfold localWeylScalar ResidueField.localWeylScalar
  rw [sphericalDigit_eq_residueField]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [digitMask_eq_residueField, projectPrimePhase_apply]

theorem localWeylExponent_eq_residueField (j : Fin 6) (e : ℕ) :
    localWeylExponent j e = ResidueField.localWeylExponent j e := rfl

/-- The project's denominator is the Gauss sum of the inverse character power. -/
theorem localTau_eq_gaussSum (p : ExteriorPrime K S) (j : Fin 6) :
    localTau K S D p j =
      gaussSum ((thetaPrimeCharacter K S D p)⁻¹ ^ j.val) (projectPrimePhase K S D p) := by
  rw [localTau_eq_residueField, ResidueField.localTau_eq_digitTau]
  rfl

/-- The zeroth denominator is the primitive additive sum over nonzero residues. -/
theorem localTau_zero (p : ExteriorPrime K S) : localTau K S D p 0 = -1 := by
  rw [localTau_eq_gaussSum]
  have hψ : projectPrimePhase K S D p ≠ 1 := by
    simpa using projectPrimePhase_isPrimitive K S D p
      (one_ne_zero : (1 : 𝓞 K ⧸ p.val.asIdeal) ≠ 0)
  simpa using gaussSum_one_left hψ

theorem localTau_ne_zero (p : ExteriorPrime K S) (j : Fin 6) (hj : j.val ≠ 0) :
    localTau K S D p j ≠ 0 := by
  rw [localTau_eq_residueField]
  exact ResidueField.localTau_ne_zero _ (thetaPrimeCharacter_orderOf K S D p) _
    (projectPrimePhase_isPrimitive K S D p) j hj

theorem localTau_norm (p : ExteriorPrime K S) (j : Fin 6) (hj : j.val ≠ 0) :
    ‖localTau K S D p j‖ = Real.sqrt (p.val.asIdeal.absNorm : ℝ) := by
  rw [localTau_eq_residueField, ResidueField.localTau_norm _ (thetaPrimeCharacter_orderOf K S D p)
    _ (projectPrimePhase_isPrimitive K S D p) j hj, residue_card_eq_absNorm K S p]

/-- Fourier inversion, including the unit indicator for the zeroth digit. -/
theorem digitMask_fourier (p : ExteriorPrime K S) (j : Fin 6)
    (t : 𝓞 K ⧸ p.val.asIdeal) :
    (∑ x : 𝓞 K ⧸ p.val.asIdeal, digitMask K S D p j x * primePhase K S D p (t * x)) =
      (thetaPrimeCharacter K S D p ^ j.val) t := by
  simp_rw [digitMask_eq_residueField, ← projectPrimePhase_apply]
  exact ResidueField.digitMask_fourier _ (thetaPrimeCharacter_orderOf K S D p) _
    (projectPrimePhase_isPrimitive K S D p) j t

theorem thetaGamma_two_norm (p : ExteriorPrime K S) :
    ‖thetaGamma K S D (exteriorPrimeIdeal K S p) 2‖ = 1 := by
  rw [thetaGamma_two_eq_gammaTwo]
  exact ResidueField.gammaTwo_norm _ (thetaPrimeCharacter_orderOf K S D p) _
    (projectPrimePhase_isPrimitive K S D p)

theorem sphericalDigit_zero (p : ExteriorPrime K S) : sphericalDigit K S D p 0 = 1 := by
  simp [sphericalDigit]

theorem sphericalDigit_three_mul (p : ExteriorPrime K S) (k : ℕ) :
    sphericalDigit K S D p (3 * k) = (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ k := by
  rw [sphericalDigit_eq_residueField, ResidueField.sphericalDigit_three_mul,
    residue_card_eq_absNorm K S p]

theorem sphericalDigit_three_mul_add_one (p : ExteriorPrime K S) (k : ℕ) :
    sphericalDigit K S D p (3 * k + 1) =
      (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ k *
        (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
        thetaGamma K S D (exteriorPrimeIdeal K S p) 2 := by
  rw [sphericalDigit_eq_residueField, ResidueField.sphericalDigit_three_mul_add_one,
    residue_card_eq_absNorm K S p, ← thetaGamma_two_eq_gammaTwo]

theorem sphericalDigit_vanishes (p : ExteriorPrime K S) (e : ℕ) (he : e % 3 = 2) :
    sphericalDigit K S D p e = 0 := by
  simp [sphericalDigit, he]

/-- The inactive ordinary digit has precisely the coefficient used in `frozenOmega`. -/
theorem digitMask_zero_zero (p : ExteriorPrime K S) :
    digitMask K S D p 0 0 = 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹ := by
  simp [digitMask]

/-- The depth-zero ordinary scalar with row digit zero carries a minus sign. -/
theorem localWeylScalar_zero_zero (p : ExteriorPrime K S) :
    localWeylScalar K S D p 0 0 =
      -(Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
        thetaGamma K S D (exteriorPrimeIdeal K S p) 2 := by
  have hχ6 : thetaPrimeCharacter K S D p ^ 6 = 1 := by
    simpa [thetaPrimeCharacter_orderOf K S D p] using
      pow_orderOf_eq_one (thetaPrimeCharacter K S D p)
  rw [localWeylScalar_eq_residueField, ResidueField.localWeylScalar_zero_zero _ hχ6,
    residue_card_eq_absNorm K S p, ← thetaGamma_two_eq_gammaTwo]

/-- The six depth-zero scalar entries, with the trivial numerator retained at `j=4`. -/
theorem localWeylScalar_zero_nonzero (p : ExteriorPrime K S) (j : Fin 6)
    (hj : j.val ≠ 0) :
    localWeylScalar K S D p j 0 =
      gaussSum (thetaPrimeCharacter K S D p ^ ((j.val + 2) % 6))
        (projectPrimePhase K S D p) / localTau K S D p j := by
  have hχ6 : thetaPrimeCharacter K S D p ^ 6 = 1 := by
    simpa [thetaPrimeCharacter_orderOf K S D p] using
      pow_orderOf_eq_one (thetaPrimeCharacter K S D p)
  rw [localWeylScalar_eq_residueField, ResidueField.localWeylScalar_zero_nonzero _ hχ6 _ j hj,
    ← localTau_eq_residueField]

/-- At every positive valuation only ordinary row digit four survives. -/
theorem localWeylScalar_positive (p : ExteriorPrime K S) (j : Fin 6)
    (e : ℕ) (he : e ≠ 0) :
    localWeylScalar K S D p j e =
      if j.val = 4 then
        ((p.val.asIdeal.absNorm : ℂ) - 1) / localTau K S D p j * sphericalDigit K S D p e
      else 0 := by
  rw [localWeylScalar_eq_residueField,
    ResidueField.localWeylScalar_positive _ (thetaPrimeCharacter_orderOf K S D p) _ j e he,
    residue_card_eq_absNorm K S p, ← localTau_eq_residueField,
    ← sphericalDigit_eq_residueField]

theorem localWeylScalar_support (p : ExteriorPrime K S) (j : Fin 6)
    (e : ℕ) (he : e % 3 = 2) : localWeylScalar K S D p j e = 0 := by
  rw [localWeylScalar_eq_residueField]
  exact ResidueField.localWeylScalar_support _ _ j e he

/-- The actual finite sum at an arbitrary residue-field unit factors with the
project's scalar and its literal `localWeylExponent`. -/
theorem localWeyl_phase_separation (p : ExteriorPrime K S) (j : Fin 6)
    (e : ℕ) (t : (𝓞 K ⧸ p.val.asIdeal)ˣ) :
    (sphericalDigit K S D p e * thetaPrimeCharacter K S D p t ^ (4 + 2 * e) *
      ∑ v : (𝓞 K ⧸ p.val.asIdeal)ˣ,
        digitMask K S D p j v * thetaPrimeCharacter K S D p v ^ 4 *
          (if e = 0 then primePhase K S D p ((t : 𝓞 K ⧸ p.val.asIdeal) / v) else 1)) =
      localWeylScalar K S D p j e * thetaPrimeCharacter K S D p t ^ localWeylExponent j e := by
  simp_rw [sphericalDigit_eq_residueField, digitMask_eq_residueField,
    ← projectPrimePhase_apply, localWeylScalar_eq_residueField,
    localWeylExponent_eq_residueField]
  exact ResidueField.unitWeylSum_phase_separation _ (thetaPrimeCharacter_orderOf K S D p) _ j e t

/-- The uniform active mark is exactly the coefficient used in `reflectedMarkFactor`. -/
theorem marked_localWeyl_table (p : ExteriorPrime K S) (e : ℕ)
    (t : (𝓞 K ⧸ p.val.asIdeal)ˣ) :
    (sphericalDigit K S D p e * thetaPrimeCharacter K S D p t ^ (4 + 2 * e) *
      ∑ v : (𝓞 K ⧸ p.val.asIdeal)ˣ,
        (p.val.asIdeal.absNorm : ℂ)⁻¹ * thetaPrimeCharacter K S D p v ^ 4 *
          (if e = 0 then primePhase K S D p ((t : 𝓞 K ⧸ p.val.asIdeal) / v) else 1)) =
      if e = 0 then
        (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
          thetaGamma K S D (exteriorPrimeIdeal K S p) 2 * thetaPrimeCharacter K S D p t ^ 2
      else 0 := by
  have hχ6 : thetaPrimeCharacter K S D p ^ 6 = 1 := by
    simpa [thetaPrimeCharacter_orderOf K S D p] using
      pow_orderOf_eq_one (thetaPrimeCharacter K S D p)
  have hχ4 : thetaPrimeCharacter K S D p ^ 4 ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by decide : (4 : ℕ) ≠ 0)
    rw [thetaPrimeCharacter_orderOf K S D p]
    decide
  have h := ResidueField.markedWeylValue_table (thetaPrimeCharacter K S D p) hχ6 hχ4
    (projectPrimePhase K S D p) e t
  simpa only [ResidueField.markedWeylValue, ResidueField.unitWeylSum,
    HeckeSkeleton.ThetaLocal.uniformDigit, residue_card_eq_absNorm K S p,
    ← sphericalDigit_eq_residueField, ← thetaGamma_two_eq_gammaTwo,
    projectPrimePhase_apply] using h

theorem localWeylScalar_zero_norm_le (p : ExteriorPrime K S) (j : Fin 6) :
    ‖localWeylScalar K S D p j 0‖ ≤ 1 := by
  rw [localWeylScalar_eq_residueField]
  exact ResidueField.localWeylScalar_zero_norm_le _ (thetaPrimeCharacter_orderOf K S D p) _
    (projectPrimePhase_isPrimitive K S D p) j

theorem row_prime_scalar_norm (p : ExteriorPrime K S) :
    ‖localWeylScalar K S D p 1 0‖ = 1 := by
  rw [localWeylScalar_eq_residueField]
  exact ResidueField.row_prime_scalar_norm _ (thetaPrimeCharacter_orderOf K S D p) _
    (projectPrimePhase_isPrimitive K S D p)

theorem localWeylScalar_three_mul_add_one_norm_le (p : ExteriorPrime K S)
    (j : Fin 6) (k : ℕ) :
    ‖localWeylScalar K S D p j (3 * k + 1)‖ ≤ (p.val.asIdeal.absNorm : ℝ)⁻¹ ^ k := by
  rw [localWeylScalar_eq_residueField, ← residue_card_eq_absNorm K S p]
  exact ResidueField.localWeylScalar_three_mul_add_one_norm_le _
    (thetaPrimeCharacter_orderOf K S D p) _ (projectPrimePhase_isPrimitive K S D p) j k

theorem localWeylScalar_three_mul_succ_norm_le (p : ExteriorPrime K S)
    (j : Fin 6) (k : ℕ) :
    ‖localWeylScalar K S D p j (3 * (k + 1))‖ ≤
      Real.sqrt (p.val.asIdeal.absNorm : ℝ) * (p.val.asIdeal.absNorm : ℝ)⁻¹ ^ (k + 1) := by
  rw [localWeylScalar_eq_residueField, ← residue_card_eq_absNorm K S p]
  exact ResidueField.localWeylScalar_three_mul_succ_norm_le _
    (thetaPrimeCharacter_orderOf K S D p) _ (projectPrimePhase_isPrimitive K S D p) j k

end HeckeGeneral.ThetaSkeleton.Global

end
