import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The canonical annular test data

These five declarations are moved verbatim from `GlobalThetaData`.
Their fully qualified names, types, and defining expressions are unchanged.
Separating them lets Mellin estimates compile without arithmetic or theta data.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Global

open MeasureTheory Set
open scoped ContDiff

/-- The Euler derivative on the positive multiplicative line. -/
def eulerDerivative (f : ℝ → ℂ) : ℝ → ℂ := fun y => (y : ℂ) * deriv f y

def eulerDerivativeOrder (h : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (eulerDerivative^[h]) f

def testIntegral (V : ℝ → ℂ) (j : ℕ) (A : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ‖eulerDerivativeOrder j V y‖ *
    (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y

/-- A finite maximum (with 0 adjoined) of the source's actual integrals. -/
def testSeminorm (V : ℝ → ℂ) (J : ℕ) (A : ℝ) : ℝ :=
  (Finset.range (J + 1)).sup' (by simp) (fun j => max 0 (testIntegral V j A))

/-- Annular tests have support bounded away from zero. The bounds are data,
not an assumption on the final Mellin kernel. -/
structure SmoothAnnularTest where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_ge : lower ≤ upper
  support : Function.support toFun ⊆ Icc lower upper

end HeckeGeneral.ThetaSkeleton.Global
