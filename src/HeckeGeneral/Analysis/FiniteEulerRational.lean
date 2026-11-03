import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Finite Laurent data for local Euler factors

These are the original finite-table definitions from `PhysicalProbeRows`.
Keeping the arithmetic-independent data in this module lets local table
identities be checked directly against the same types used by the physical
row continuation.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical
open scoped BigOperators

/-- Finite Laurent data for exceptional local factors. Coefficients are
calibrated to the initial row series in the arithmetic application. -/
structure FiniteEulerPolynomial where
  powers : Finset (ℤ × ℤ × ℤ)
  coefficient : ℤ × ℤ × ℤ → ℂ

def finiteEulerPolynomialValue (A : FiniteEulerPolynomial) (q : ℝ) (s w z : ℂ) : ℂ :=
  ∑ e ∈ A.powers, A.coefficient e * (q : ℂ) ^
    (-((e.1 : ℂ) * s + (e.2.1 : ℂ) * w + (e.2.2 : ℂ) * z))

structure FiniteEulerRational where
  numerator : FiniteEulerPolynomial
  denominator : FiniteEulerPolynomial

def finiteEulerRationalValue (A : FiniteEulerRational) (q : ℝ) (s w z : ℂ) : ℂ :=
  finiteEulerPolynomialValue A.numerator q s w z /
    finiteEulerPolynomialValue A.denominator q s w z

end HeckeGeneral.ThetaSkeleton.Physical
