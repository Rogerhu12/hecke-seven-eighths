import HeckeGeneral.Analysis.IdealDerivative
import HeckeGeneral.Analysis.HeckeEulerProduct

/-!
# Derivative series of an actual unitary Hecke character

The logarithmic moments here use the already constructed coefficients of
the actual local character and the actual integral ideal norm. All analytic
assertions are proved in the open half-plane of absolute convergence.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Characters
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- The genuine signed log-norm moment of the Hecke ideal series. -/
def heckeDerivativeSeries (χ : HeckeCharacter K) (k : ℕ) (s : ℂ) : ℂ :=
  idealLogSeries K (heckeIdealCoefficient K χ) k s

@[simp] theorem heckeDerivativeSeries_zero (χ : HeckeCharacter K) (s : ℂ) :
    heckeDerivativeSeries K χ 0 s = heckeLSeries K χ s :=
  idealLogSeries_zero K (heckeIdealCoefficient K χ) s

theorem absolutelySummable_heckeDerivativeSeries (χ : HeckeCharacter K)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I => ‖idealLogTerm K (heckeIdealCoefficient K χ) k s I‖) :=
  absolutelySummable_idealLogTerm K _ (norm_heckeIdealCoefficient_le_one K χ) k hs

theorem hasSum_heckeDerivativeSeries (χ : HeckeCharacter K) (k : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (idealLogTerm K (heckeIdealCoefficient K χ) k s)
      (heckeDerivativeSeries K χ k s) :=
  hasSum_idealLogTerm K _ (norm_heckeIdealCoefficient_le_one K χ) k hs

/-- Each logarithmic moment differentiates to the next one. -/
theorem hasDerivAt_heckeDerivativeSeries (χ : HeckeCharacter K) (k : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (heckeDerivativeSeries K χ k) (heckeDerivativeSeries K χ (k + 1) s) s :=
  hasDerivAt_idealLogSeries K _ (norm_heckeIdealCoefficient_le_one K χ) k hs

theorem hasDerivAt_heckeLSeries (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (heckeLSeries K χ) (heckeDerivativeSeries K χ 1 s) s :=
  hasDerivAt_idealDirichletSeries K _ (norm_heckeIdealCoefficient_le_one K χ) hs

/-- The k-th complex derivative is the absolutely convergent (-log norm)^k series. -/
theorem iteratedDeriv_heckeLSeries (χ : HeckeCharacter K) (k : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (heckeLSeries K χ) s = heckeDerivativeSeries K χ k s :=
  iteratedDeriv_idealDirichletSeries K _ (norm_heckeIdealCoefficient_le_one K χ) k hs

theorem analyticAt_heckeDerivativeSeries (χ : HeckeCharacter K) (k : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (heckeDerivativeSeries K χ k) s :=
  analyticAt_idealLogSeries K _ (norm_heckeIdealCoefficient_le_one K χ) k hs

theorem heckeDerivativeSeries_normTwist (χ : HeckeCharacter K) (k : ℕ)
    (t : ℝ) (s : ℂ) :
    heckeDerivativeSeries K (χ * heckeNormTwist K t) k s =
      heckeDerivativeSeries K χ k (s - (t : ℂ) * Complex.I) := by
  unfold heckeDerivativeSeries
  rw [show heckeIdealCoefficient K (χ * heckeNormTwist K t) =
      normTwistedCoefficients (idealNorm K) (heckeIdealCoefficient K χ) t
    from funext (heckeIdealCoefficient_normTwist K χ t)]
  exact idealLogSeries_normTwist K _ k t s

/-- The norm twist commutes with every derivative, with the actual s - it convention. -/
theorem iteratedDeriv_heckeLSeries_normTwist (χ : HeckeCharacter K) (k : ℕ)
    (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (heckeLSeries K (χ * heckeNormTwist K t)) s =
      iteratedDeriv k (heckeLSeries K χ) (s - (t : ℂ) * Complex.I) := by
  rw [iteratedDeriv_heckeLSeries K _ k hs,
    iteratedDeriv_heckeLSeries K χ k (by simpa using hs), heckeDerivativeSeries_normTwist]

/-- The logarithmic derivative is defined from the genuine L-function. -/
def heckeLogDerivative (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  deriv (heckeLSeries K χ) s / heckeLSeries K χ s

theorem heckeLogDerivative_eq_series_quotient (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLogDerivative K χ s = heckeDerivativeSeries K χ 1 s / heckeLSeries K χ s := by
  rw [heckeLogDerivative, (hasDerivAt_heckeLSeries K χ hs).deriv]

theorem analyticAt_heckeLogDerivative (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (heckeLogDerivative K χ) s := by
  have heq : heckeLogDerivative K χ =ᶠ[𝓝 s]
      (fun z => heckeDerivativeSeries K χ 1 z / heckeLSeries K χ z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact heckeLogDerivative_eq_series_quotient K χ hz
  exact ((analyticAt_heckeDerivativeSeries K χ 1 hs).div
    (analyticAt_heckeLSeries K χ hs) (heckeLSeries_ne_zero K χ hs)).congr heq.symm

theorem heckeLogDerivative_normTwist (χ : HeckeCharacter K) (t : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLogDerivative K (χ * heckeNormTwist K t) s =
      heckeLogDerivative K χ (s - (t : ℂ) * Complex.I) := by
  rw [heckeLogDerivative_eq_series_quotient K _ hs,
    heckeLogDerivative_eq_series_quotient K χ (by simpa using hs),
    heckeDerivativeSeries_normTwist, heckeLSeries_normTwist]

theorem hasDerivAt_heckeReciprocal (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun z => (heckeLSeries K χ z)⁻¹)
      (-heckeDerivativeSeries K χ 1 s / heckeLSeries K χ s ^ 2) s :=
  (hasDerivAt_heckeLSeries K χ hs).inv (heckeLSeries_ne_zero K χ hs)

end HeckeGeneral.Analysis
