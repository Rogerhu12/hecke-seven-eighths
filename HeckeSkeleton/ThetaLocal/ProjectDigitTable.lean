import HeckeSkeleton.ThetaLocal.ProjectFinite

/-!
# The project's spherical digit interface

The existing `LocalThetaInput` is an interface for an explicit valuation
table.  This file supplies that table using the project's residue character,
absolute norm, and Gauss coefficient, and proves every field of the interface.
The table's representation-theoretic realization is a separate construction.
-/

set_option autoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Global

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The unit phase and the existing spherical digit, with zero negative support. -/
def projectSphericalDigitTable : ThetaDigitTable K S := fun p e u =>
  if e < 0 then 0
  else thetaPrimeCharacter K S D p u ^ (2 * e.toNat) * sphericalDigit K S D p e.toNat

/-- All local digit obligations follow from the actual arithmetic data. -/
theorem projectSphericalDigitTable_input :
    LocalThetaInput K S D (projectSphericalDigitTable K S D) where
  gauss_norm := thetaGamma_two_norm K S D
  negative := by
    intro p e u he
    simp [projectSphericalDigitTable, he]
  triple := by
    intro p k u
    have he : (3 * (k : ℤ)).toNat = 3 * k := by omega
    have hn : ¬3 * (k : ℤ) < 0 := by omega
    have hp : 2 * (3 * k) = 6 * k := by omega
    simp only [projectSphericalDigitTable, if_neg hn, he, hp,
      sphericalDigit_three_mul]
  triple_one := by
    intro p k u
    have he : (3 * (k : ℤ) + 1).toNat = 3 * k + 1 := by omega
    have hn : ¬3 * (k : ℤ) + 1 < 0 := by omega
    have hp : 2 * (3 * k + 1) = 6 * k + 2 := by omega
    simp only [projectSphericalDigitTable, if_neg hn, he, hp,
      sphericalDigit_three_mul_add_one]
    ring
  triple_two := by
    intro p k u
    have he : (3 * (k : ℤ) + 2).toNat = 3 * k + 2 := by omega
    have hn : ¬3 * (k : ℤ) + 2 < 0 := by omega
    have hm : (3 * k + 2) % 3 = 2 := by omega
    simp only [projectSphericalDigitTable, if_neg hn, he,
      sphericalDigit_vanishes K S D p _ hm, mul_zero]

theorem projectSphericalDigitTable_normalized (p : ExteriorPrime K S) :
    projectSphericalDigitTable K S D p 0 1 = 1 :=
  LocalThetaInput.normalized K S D _ (projectSphericalDigitTable_input K S D) p

end HeckeGeneral.ThetaSkeleton.Global

end
