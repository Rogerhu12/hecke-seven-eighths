import HeckeSkeleton.ThetaLocal.ComplexWeylPowers
import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.CompactWeyl
import DedekindZetaZeroFree.Theta.Whittaker.Complex.TraceCharacterLines

/-!
# The actual high K-type root vectors in the global complex core

This module lifts the existing `ThetaLocal.archRootVector` into the
actual `KPGlobalResidualConstruction.complexCore`.  The highest harmonic
lies in one of the defining harmonic summands; the lowest harmonic is its
actual compact Weyl translate.  The scalar coefficients are the existing
root-string coefficients, so inclusion returns the original local vector.

The canonical continuous functional is the existing theta Jacquet
functional.  Its value on each lifted root vector at the identity is the
positive order-one-third Bessel value.  At the global trace frequency the
parameters are literally `c = 4 * Real.pi` and `beta = traceFrequency`.

The statements provide the vector, Whittaker-functional membership and
functional-nonzero components used by `LocalArchInput`. The stored-source
nonvanishing follows from the source certificate, and the Haar/Mellin
fields are supplied by the separate local analytic modules.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace ThetaGlobal.LocalArchRootCore

open DedekindZetaZeroFree
open KPGlobalResidualConstruction KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPCplxActualImage KPCplxIntertwinerEigenvalues KPCplxRootDerivativeVectors
open KPCplxHarmonicPropagation.RaisingCalculation KPCplxJacquetFunctional KPCplxBessel
open FourierContinuation.ComplexLines
open HeckeSkeleton.ThetaLocal HeckeSkeleton.ThetaLocal.HarmonicCalculation
open scoped Classical

/-- The existing compact Weyl representative is `I` times the swap matrix. -/
theorem compactWeyl_projective :
    Matrix.ProjGenLinGroup.mk (complexSU2Embedding SheetRescaling.compactWeyl) =
      Matrix.ProjGenLinGroup.mk weyl := by
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [complexSU2Embedding, SheetRescaling.compactWeyl, weyl, Matrix.mul_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar]

/-- The highest harmonic belongs to the literal intersection defining the core. -/
def highestCore (n : ℕ) : complexCore := by
  refine ⟨harmonicSection negativeParameter n, ?_⟩
  constructor
  · exact harmonicKType_le_imageSubmodule (1 : ℂˣ) n
      (harmonicSection_harmonic negativeParameter n)
  · exact Submodule.mem_iSup_of_mem n (harmonicSection_harmonic negativeParameter n)

/-- The lowest harmonic is the actual compact translate of the highest one. -/
def lowestCore (n : ℕ) : complexCore :=
  complexCoreCompactAction SheetRescaling.compactWeyl (highestCore n)

theorem coreInImage_highestCore (β : ℂˣ) (n : ℕ) :
    KPWildComplexWhittakerDictionary.coreInImage β (highestCore n) =
      highestImage β n := by
  apply Subtype.ext
  rfl

theorem coreInImage_lowestCore (β : ℂˣ) (n : ℕ) :
    KPWildComplexWhittakerDictionary.coreInImage β (lowestCore n) =
      lowestImage β n := by
  apply Subtype.ext
  change pi negativeParameter
      (Matrix.ProjGenLinGroup.mk (complexSU2Embedding SheetRescaling.compactWeyl))
      (harmonicSection negativeParameter n) =
    pi negativeParameter (Matrix.ProjGenLinGroup.mk weyl)
      (harmonicSection negativeParameter n)
  rw [compactWeyl_projective]

/-- A core vector with the existing root-string coefficients, for every integer weight. -/
def archRootCore (c : ℝ) (β : ℂˣ) : ℤ → complexCore
  | .ofNat n => rootStringCoefficient c β n • highestCore n
  | .negSucc n => rootStringCoefficient c β (n + 1) • lowestCore (n + 1)

/-- Inclusion returns the actual local root vector, without rescaling it. -/
theorem coreInImage_archRootCore (c : ℝ) (β : ℂˣ) (m : ℤ) :
    KPWildComplexWhittakerDictionary.coreInImage β (archRootCore c β m) =
      archRootVector c β m := by
  cases m with
  | ofNat n =>
    change KPWildComplexWhittakerDictionary.coreInImage β
        (rootStringCoefficient c β n • highestCore n) = higherPlus c β n
    rw [map_smul, coreInImage_highestCore, higherPlus_eq_highestImage]
  | negSucc n =>
    change KPWildComplexWhittakerDictionary.coreInImage β
        (rootStringCoefficient c β (n + 1) • lowestCore (n + 1)) =
      higherMinus c β (n + 1)
    rw [map_smul, coreInImage_lowestCore, higherMinus_eq_lowestImage]

theorem harmonicInclusion_archRootCore (c : ℝ) (m : ℤ) :
    harmonicInclusion (archRootCore c traceFrequency m) =
      archRootVector c traceFrequency m :=
  coreInImage_archRootCore c traceFrequency m

/-- The concrete Jacquet functional already has the required Whittaker covariance. -/
theorem thetaJacquetFunctional_whittaker (β : ℂˣ) :
    thetaJacquetFunctional β ∈
      KPCplxWhittakerUnique.whittakerSpace β (character (β : ℂ)) := by
  intro t h
  exact thetaJacquetFunctional_covariance β t h

private theorem whittakerValue_one (β : ℂˣ) (h : Theta β) :
    whittakerValue β h 1 = thetaJacquetFunctional β h := by
  have hd : diagonal (1 : ℂˣ) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.one_apply]
  unfold whittakerValue
  rw [hd, map_one]
  have he : imageAction β 1 h = h := by
    apply Subtype.ext
    exact pi_one negativeParameter h.val
  rw [he]

/-- At the identity every normalized root vector has the same positive Bessel value. -/
theorem thetaJacquetFunctional_archRootVector (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (m : ℤ) :
    thetaJacquetFunctional β (archRootVector c β m) = (besselKThird c : ℂ) := by
  rw [← whittakerValue_one]
  simpa [radius, omegaPlus] using whittaker_archRootVector c hc β hβ m (1 : ℂˣ)

theorem thetaJacquetFunctional_archRootCore_ne_zero (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (m : ℤ) :
    thetaJacquetFunctional β
      (KPWildComplexWhittakerDictionary.coreInImage β (archRootCore c β m)) ≠ 0 := by
  rw [coreInImage_archRootCore, thetaJacquetFunctional_archRootVector c hc β hβ]
  exact Complex.ofReal_ne_zero.mpr (besselKThird_pos c hc).ne'

/-- The exact trace-frequency vector available for each angular weight in the global input. -/
def traceRootCore (m : ℤ) : complexCore :=
  archRootCore (4 * Real.pi) traceFrequency m

theorem harmonicInclusion_traceRootCore (m : ℤ) :
    harmonicInclusion (traceRootCore m) =
      archRootVector (4 * Real.pi) traceFrequency m :=
  harmonicInclusion_archRootCore (4 * Real.pi) m

theorem traceJacquet_whittaker :
    thetaJacquetFunctional traceFrequency ∈
      KPCplxWhittakerUnique.whittakerSpace traceFrequency traceCharacter :=
  thetaJacquetFunctional_whittaker traceFrequency

theorem traceRootCore_value (m : ℤ) :
    thetaJacquetFunctional traceFrequency (harmonicInclusion (traceRootCore m)) =
      (besselKThird (4 * Real.pi) : ℂ) := by
  rw [harmonicInclusion_traceRootCore]
  exact thetaJacquetFunctional_archRootVector (4 * Real.pi) (by positivity)
    traceFrequency rfl m

/-- This is precisely the canonical-functional nonzero field, for any selected local weight. -/
theorem traceRootCore_functional_nonzero (m : ℤ) :
    thetaJacquetFunctional traceFrequency (harmonicInclusion (traceRootCore m)) ≠ 0 := by
  rw [traceRootCore_value]
  exact Complex.ofReal_ne_zero.mpr (besselKThird_pos (4 * Real.pi) (by positivity)).ne'

end ThetaGlobal.LocalArchRootCore

#print axioms ThetaGlobal.LocalArchRootCore.coreInImage_archRootCore
#print axioms ThetaGlobal.LocalArchRootCore.harmonicInclusion_traceRootCore
#print axioms ThetaGlobal.LocalArchRootCore.traceJacquet_whittaker
#print axioms ThetaGlobal.LocalArchRootCore.traceRootCore_value
#print axioms ThetaGlobal.LocalArchRootCore.traceRootCore_functional_nonzero
