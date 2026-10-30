import HeckeGeneral.Characters.PrimeCoefficients
import HeckeGeneral.Arithmetic.IdealCoefficients
import HeckeGeneral.Analysis.IdealDirichlet
import HeckeGeneral.Analysis.EulerFactors

/-!
# The convergent L-series of an actual unitary Hecke character

The coefficients come from the actual continuous idèle class character via
its unramified local components and unique factorization of integral ideals.
Absolute convergence and holomorphy are proved on Re(s) > 1. This is not an
analytic continuation to the intended seven-eighths half-plane.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Arithmetic
open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- Actual ideal coefficients obtained from the local components of χ. -/
def heckeIdealCoefficient (χ : HeckeCharacter K) (I : NonzeroIdeal K) : ℂ :=
  nonzeroIdealCoefficient (primeCoefficient K χ) I

theorem norm_heckeIdealCoefficient_le_one (χ : HeckeCharacter K) (I : NonzeroIdeal K) :
    ‖heckeIdealCoefficient K χ I‖ ≤ 1 :=
  norm_nonzeroIdealCoefficient_le_one (primeCoefficient K χ) (norm_primeCoefficient_le_one K χ) I

theorem heckeIdealCoefficient_mul (χ : HeckeCharacter K) (I J : NonzeroIdeal K) :
    heckeIdealCoefficient K χ (I * J) =
      heckeIdealCoefficient K χ I * heckeIdealCoefficient K χ J :=
  idealCoefficient_mul (primeCoefficient K χ) I.val J.val

/-- The Hecke ideal series. Its genuine sum and holomorphy are established below for Re(s) > 1. -/
def heckeLSeries (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  idealDirichletSeries K (heckeIdealCoefficient K χ) s

theorem absolutelySummable_heckeLSeries (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I => ‖dirichletTerm (idealNorm K) (heckeIdealCoefficient K χ) s I‖) :=
  absolutelySummable_idealDirichlet K _ (norm_heckeIdealCoefficient_le_one K χ) hs

theorem hasSum_heckeLSeries (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    HasSum (dirichletTerm (idealNorm K) (heckeIdealCoefficient K χ) s) (heckeLSeries K χ s) :=
  hasSum_idealDirichlet K _ (norm_heckeIdealCoefficient_le_one K χ) hs

theorem analyticAt_heckeLSeries (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (heckeLSeries K χ) s :=
  analyticAt_idealDirichlet K _ (norm_heckeIdealCoefficient_le_one K χ) hs

theorem heckeIdealCoefficient_normTwist (χ : HeckeCharacter K) (t : ℝ) (I : NonzeroIdeal K) :
    heckeIdealCoefficient K (χ * heckeNormTwist K t) I =
      normTwistedCoefficients (idealNorm K) (heckeIdealCoefficient K χ) t I := by
  have hp : primeCoefficient K (χ * heckeNormTwist K t) =
      primeNormTwistedCoefficients K (primeCoefficient K χ) t := by
    funext v
    exact primeCoefficient_normTwist K χ t v
  unfold heckeIdealCoefficient
  rw [hp, nonzeroIdealCoefficient_primeNormTwist]
  simp only [normTwistedCoefficients, idealNorm, Complex.ofReal_natCast]

/-- The actual Hecke character norm twist has the manuscript's s - it sign.
For Re(s) > 1 both sides are convergent sums by the preceding theorem. -/
theorem heckeLSeries_normTwist (χ : HeckeCharacter K) (t : ℝ) (s : ℂ) :
    heckeLSeries K (χ * heckeNormTwist K t) s =
      heckeLSeries K χ (s - (t : ℂ) * Complex.I) := by
  unfold heckeLSeries
  rw [show heckeIdealCoefficient K (χ * heckeNormTwist K t) =
      normTwistedCoefficients (idealNorm K) (heckeIdealCoefficient K χ) t
    from funext (heckeIdealCoefficient_normTwist K χ t)]
  exact idealDirichletSeries_normTwist K _ t s

/-- The genuine unramified local Euler factor; the ramified value is automatically one. -/
def heckeLocalEulerFactor (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  (eulerPolynomial (residueCard K v) (primeCoefficient K χ v) s)⁻¹

theorem heckeLocalEulerFactor_of_ramified (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (hχ : ¬UnramifiedAt K χ v) (s : ℂ) :
    heckeLocalEulerFactor K χ v s = 1 := by
  simp [heckeLocalEulerFactor, primeCoefficient_of_ramified K χ v hχ, eulerPolynomial]

theorem heckeLocalEulerFactor_ne_zero (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    heckeLocalEulerFactor K χ v s ≠ 0 :=
  inv_ne_zero (eulerPolynomial_ne_zero (by exact_mod_cast one_lt_residueCard K v)
    (norm_primeCoefficient_le_one K χ v) hs)

end HeckeGeneral.Analysis
