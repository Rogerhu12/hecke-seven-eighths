import HeckeSkeleton.HighBinSupport.ActualDenominatorMellin
import HeckeSkeleton.HighBinSupport.ActualNormFormHigherPrimePowers
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FunProp

/-!
Actual Mellin inversion for the annular prime detector.

The inverse identity is derived from the real `SmoothAnnularTest` and its
proved Mellin integration-by-parts estimates. The logarithm-removal test
is constructed pointwise from the original profile. Its apparent pole is
outside the closed support when P>1, so the test is smooth everywhere.
No inverse-transform identity is supplied as data.
-/

noncomputable section
namespace HighBinVerified.NormFormMellin

open MeasureTheory Complex Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HighBinBoundary.ActualDenominator
open scoped Topology ContDiff

/-- The actual Mellin transform is integrable on every vertical line. -/
theorem verticalIntegrable_mellin (V : SmoothAnnularTest) (sigma : ℝ) :
    Complex.VerticalIntegrable (mellin V.toFun) sigma := by
  obtain ⟨D, hD, hbound⟩ := exists_mellin_uniform_strip_bound V sigma sigma 2
  have hmodel : Integrable (fun t : ℝ => D / (1 + |t|) ^ 2) := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
      (by norm_num)).const_mul D
    convert h using 1
    ext t
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|), Real.rpow_two]
    rfl
  have hc : Continuous (fun t : ℝ => mellin V.toFun ((sigma : ℂ) + t * I)) :=
    (differentiable_mellin V).continuous.comp (by fun_prop)
  apply hmodel.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 2)).mpr
    simpa only [mul_comm] using hbound sigma t le_rfl le_rfl)

/-- Mellin inversion for the repository's genuine smooth annular test. -/
theorem mellin_inversion_annular (V : SmoothAnnularTest) (sigma : ℝ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv sigma (mellin V.toFun) x = V.toFun x :=
  mellinInv_mellin_eq sigma V.toFun hx
    ((good_toFun V).integrableOn_mellin (sigma : ℂ))
    (verticalIntegrable_mellin V sigma) V.smooth.continuous.continuousAt

def divideLogProfile (V : SmoothAnnularTest) (P y : ℝ) : ℂ :=
  V.toFun y / (Real.log (P * y) : ℂ)

theorem divideLogProfile_support (V : SmoothAnnularTest) (P : ℝ) :
    Function.support (divideLogProfile V P) ⊆ Function.support V.toFun := by
  intro y hy
  by_contra hz
  exact hy (by simp only [divideLogProfile, Function.notMem_support.mp hz, zero_div])

/-- A log denominator has no zero on the closed annular support. Outside
that support the quotient agrees locally with zero, including y=1/P. -/
theorem contDiff_divideLogProfile (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2)
    {P : ℝ} (hP : 1 < P) : ContDiff ℝ ∞ (divideLogProfile V P) := by
  have hs : tsupport V.toFun ⊆ Icc (1 : ℝ) 2 :=
    closure_minimal (fun y hy => ⟨(hann hy).1.le, (hann hy).2.le⟩) isClosed_Icc
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ tsupport V.toFun
  · have hy1 : 1 ≤ y := (hs hy).1
    have hPy : 1 < P * y := hP.trans_le (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hy1 (by linarith : 0 ≤ P))
    have hlog : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log (P * x) : ℂ)) y :=
      (Complex.ofRealCLM.contDiff (𝕜 := ℝ)).contDiffAt.comp y
        ((contDiffAt_const.mul contDiffAt_id).log (by linarith : P * y ≠ 0))
    have hlog0 : (Real.log (P * y) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.log_pos hPy).ne'
    simpa only [divideLogProfile, div_eq_mul_inv] using
      V.smooth.contDiffAt.mul (hlog.inv hlog0)
  · have hz : V.toFun =ᶠ[𝓝 y] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hy
    have hz' : divideLogProfile V P =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [hz] with x hx
      simp only [divideLogProfile, hx, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq hz'

/-- The precise annular test which removes the logarithmic prime weight. -/
def divideLogTest (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2)
    (P : ℝ) (hP : 1 < P) : SmoothAnnularTest where
  toFun := divideLogProfile V P
  smooth := contDiff_divideLogProfile V hann hP
  lower := 1
  upper := 2
  lower_pos := zero_lt_one
  upper_ge := by norm_num
  support := fun y hy =>
    ⟨(hann (divideLogProfile_support V P hy)).1.le,
      (hann (divideLogProfile_support V P hy)).2.le⟩

/-- The genuine inversion identity used in a prime-power detector after
dividing by log(N). All support and regularity conditions are discharged. -/
theorem mellin_inversion_divideLog (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2)
    (P sigma : ℝ) (hP : 1 < P) {x : ℝ} (hx : 0 < x) :
    mellinInv sigma (mellin (divideLogProfile V P)) x =
      V.toFun x / (Real.log (P * x) : ℂ) :=
  mellin_inversion_annular (divideLogTest V hann P hP) sigma hx

open NumberField IsDedekindDomain HeckeGeneral.Analysis HeckeGeneral.Characters

variable (K : Type) [Field K] [NumberField K]

/-- At the actual ideal p^(n+1), Mellin inversion removes precisely the
factor log(Np), leaving the reciprocal exponent 1/(n+1). -/
theorem log_mul_mellinInv_primePower (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2)
    (P sigma : ℝ) (hP : 1 < P) (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    (Real.log (pn.1.asIdeal.absNorm : ℝ) : ℂ) *
      mellinInv sigma (mellin (divideLogProfile V P))
        ((pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1) / P) =
      V.toFun ((pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1) / P) /
        ((pn.2 + 1 : ℕ) : ℂ) := by
  have hP0 : 0 < P := by linarith
  have hq1 : (1 : ℝ) < (pn.1.asIdeal.absNorm : ℝ) := by
    exact_mod_cast one_lt_primeIdeal_absNorm K pn.1
  have hN : 0 < (pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1) :=
    pow_pos (by linarith) _
  have hlog : (Real.log (pn.1.asIdeal.absNorm : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hq1).ne'
  have hm : ((pn.2 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero pn.2
  rw [mellin_inversion_divideLog V hann P sigma hP (div_pos hN hP0)]
  have hcancel : P * ((pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1) / P) =
      (pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1) := by field_simp [hP0.ne']
  rw [hcancel, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hm, hlog] <;> ring

/-- Termwise calibration of the full genuine annular prime-power detector.
The coefficient, phase, logarithm, exponent and Mellin normalizations are
the actual expressions, rather than freely chosen local amplitudes. -/
theorem mellinInv_primePower_detector_term (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2)
    (chi : HeckeCharacter K) (P sigma t : ℝ) (hP : 1 < P)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    (Real.log (pn.1.asIdeal.absNorm : ℝ) : ℂ) *
      mellinInv sigma (mellin (divideLogProfile V P))
        ((pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1) / P) *
      primeCoefficient K chi pn.1 ^ (pn.2 + 1) *
      (((pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1)) : ℂ) ^
        (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      HigherPrimePowers.heckeAnnularPrimePowerTerm K chi V.toFun P t pn := by
  rw [log_mul_mellinInv_primePower K V hann P sigma hP pn]
  unfold HigherPrimePowers.heckeAnnularPrimePowerTerm
  ring

end HighBinVerified.NormFormMellin

#print axioms HighBinVerified.NormFormMellin.mellin_inversion_annular
#print axioms HighBinVerified.NormFormMellin.contDiff_divideLogProfile
#print axioms HighBinVerified.NormFormMellin.mellin_inversion_divideLog
#print axioms HighBinVerified.NormFormMellin.mellinInv_primePower_detector_term
