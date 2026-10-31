import Expansion.ActualPrincipalVerticalRemainders

/-!
# Exact regular factors of the two principal residues

These definitions only expose one actual deleted zeta factor at a time.
The identities are pointwise algebra, including at zeros and poles under
the original total-division conventions.  Residue limits and contour
shifts are proved in the analytic modules that import this file.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]
local notation "muS" => (fun p : Sset => mu p.val)

theorem actualPrincipalKernelCore_linear (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s w z Wvalue : ℂ) :
    actualPrincipalKernelCore K S mu P psi g Z s w z Wvalue =
      actualPrincipalKernelCore K S mu P psi g Z s w z 1 * Wvalue := by
  simp only [actualPrincipalKernelCore, div_eq_mul_inv]
  ring

/-- The actual w-residue kernel with just its zeta(6z) factor exposed.
It retains the original residue, denominator test, full finite correction,
Poisson scalar, scale powers, and both independent normalizers. -/
def actualPrincipalZRegularPart (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s z : ℂ) : ℂ :=
  (physicalPoissonScalar K : ℂ) *
    Complex.exp ((s + z - 1) ^ 2) * additiveMellin K Sset muS P.additive z *
    mellin P.denominator.toFun 1 *
    ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z) *
    (Z : ℂ) ^ (s + z - 1) *
    (deletedZetaResidue K Sset / heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s) *
    compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z s 1 z /
    (physicalResidueNormalizer K Sset muS P * primeNormalizer K Sset g ∅ Z)

theorem actualPrincipalWResidueKernel_factorization
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s z : ℂ) :
    actualPrincipalWResidueKernel K S mu P psi g Z s z =
      actualPrincipalZRegularPart K S mu P psi g Z s z *
        heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z) := by
  simp only [actualPrincipalWResidueKernel, actualPrincipalKernelCore,
    actualPrincipalZRegularPart, sub_self, Complex.cpow_zero, mul_one, div_eq_mul_inv]
  ring

end Expansion.Project

#print axioms Expansion.Project.actualPrincipalKernelCore_linear
#print axioms Expansion.Project.actualPrincipalWResidueKernel_factorization
