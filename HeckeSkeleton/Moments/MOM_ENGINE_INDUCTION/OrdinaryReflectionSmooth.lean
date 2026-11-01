import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionDecay
import HeckeGeneral.Analysis.SmoothDyadicPartition
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Actual smooth annular windows of the ordinary reflected profile

All polynomial frequency moments of the genuine reflection kernel are
integrable by Euler decay of the original test.  Fourier regularity then
proves smoothness of the reflected profile on the positive axis.  A fixed
proved smooth dyadic cutoff produces actual `SmoothAnnularTest` windows,
with support in [1/2,2] and an exact norm-scale calibration.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators Topology ContDiff FourierTransform

variable (K : Type) [Field K] [NumberField K]

/-- Frequency moments are genuine L1 functions, for every finite order. -/
theorem ordinaryReflectionKernel_weighted_integrable
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Integrable (fun t : ℝ => ‖t‖ ^ n * ‖ordinaryReflectionKernel K χ V δ t‖) := by
  obtain ⟨G, hG, hGb⟩ := ordinaryGammaRatio_strip_bound K hcomplex χ δ hδ.le
  let k : ℕ := (2 * Nat.ceil δ + 2) * Fintype.card (InfinitePlace K)
  let J : ℕ := k + n + 2
  let B : ℝ := 2 ^ J * (Iint V 0 δ + Iint V J δ)
  have hB : 0 ≤ B := mul_nonneg (by positivity)
    (add_nonneg (Iint_nonneg V _ _) (Iint_nonneg V _ _))
  have hc : Continuous (fun t : ℝ => ‖t‖ ^ n * ‖ordinaryReflectionKernel K χ V δ t‖) :=
    (continuous_norm.pow n).mul (continuous_ordinaryReflectionKernel K χ V hδ).norm
  apply ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul (B * G)).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg t) n) (norm_nonneg _))]
  let T : ℝ := 1 + |t|
  have hT : 0 < T := by dsimp [T]; positivity
  let s := idealVerticalPoint (-δ) (-t)
  have he : 1 - idealVerticalPoint (1 + δ) t = s := by
    dsimp [s, idealVerticalPoint]
    push_cast
    ring
  have hm : ‖mellin V.toFun s‖ ≤ B * T ^ (-(J : ℝ)) := by
    simpa only [s, B, T, neg_neg, abs_neg] using
      smoothAnnular_mellin_vertical_decay V J (-δ) (-t)
  have hg : ‖ordinaryGammaRatio K χ s‖ ≤ G * T ^ k := by
    simpa only [s, idealVerticalPoint_im, abs_neg, T, k] using
      hGb s (by simp [s]) (by simp [s]; linarith)
  have hn : ‖t‖ ^ n ≤ T ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) (by dsimp [T]; linarith) n
  have hp : T ^ n * T ^ (-(J : ℝ)) * T ^ k = T ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast T n, ← Real.rpow_natCast T k,
      ← Real.rpow_add hT, ← Real.rpow_add hT]
    congr 1
    dsimp [J]
    push_cast
    ring
  have hk : ‖ordinaryReflectionKernel K χ V δ t‖ =
      ‖mellin V.toFun s‖ * ‖ordinaryGammaRatio K χ s‖ := by
    simp only [ordinaryReflectionKernel, he, ordinaryGammaRatio, norm_mul]
  rw [hk]
  calc
    _ ≤ T ^ n * ((B * T ^ (-(J : ℝ))) * (G * T ^ k)) :=
      mul_le_mul hn (mul_le_mul hm hg (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = B * G * (1 + |t|) ^ (-(2 : ℝ)) := by
      calc
        _ = B * G * (T ^ n * T ^ (-(J : ℝ)) * T ^ k) := by ring
        _ = _ := by rw [hp]

/-- Exact Fourier representation in the logarithmic norm coordinate. -/
theorem ordinaryReflectedProfile_fourier (χ : HeckeCharacter K)
    (V : SmoothAnnularTest) (δ : ℝ) {y : ℝ} (hy : 0 < y) :
    ordinaryReflectedProfile K χ V δ y =
      (2 * (Real.pi : ℂ))⁻¹ * (Real.exp (-(1 + δ) * Real.log y) : ℂ) *
        𝓕 (ordinaryReflectionKernel K χ V δ) (Real.log y / (2 * Real.pi)) := by
  have he (t : ℝ) : (y : ℂ) ^ (-idealVerticalPoint (1 + δ) t) =
      (Real.exp (-(1 + δ) * Real.log y) : ℂ) *
        Complex.exp (((-2 * Real.pi * t * (Real.log y / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      ← Complex.ofReal_log hy.le, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    unfold idealVerticalPoint
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    <;> ring
  rw [ordinaryReflectedProfile, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  simp_rw [he, mul_assoc]
  rw [integral_const_mul]

/-- Fourier regularity derives smoothness; no reflected smoothness field
or derivative bound is postulated. -/
theorem contDiffOn_ordinaryReflectedProfile
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ : ℝ} (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (ordinaryReflectedProfile K χ V δ) (Ioi 0) := by
  have hF : ContDiff ℝ ∞ (𝓕 (ordinaryReflectionKernel K χ V δ)) :=
    Real.contDiff_fourier (N := ⊤) (fun n _ =>
      ordinaryReflectionKernel_weighted_integrable K hcomplex χ V hδ n)
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    Real.contDiffOn_log.mono (fun y hy => ne_of_gt hy)
  have hexp : ContDiffOn ℝ ∞
      (fun y : ℝ => (Real.exp (-(1 + δ) * Real.log y) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hlog))
  have hcont : ContDiffOn ℝ ∞ (fun y : ℝ =>
      (2 * (Real.pi : ℂ))⁻¹ * (Real.exp (-(1 + δ) * Real.log y) : ℂ) *
        𝓕 (ordinaryReflectionKernel K χ V δ) (Real.log y / (2 * Real.pi))) (Ioi 0) :=
    (contDiffOn_const.mul hexp).mul (hF.comp_contDiffOn (hlog.div_const _))
  apply hcont.congr
  intro y hy
  rw [ordinaryReflectedProfile_fourier K χ V δ hy]

/-- A fixed smooth annular window of the actual reflected norm profile. -/
def ordinaryReflectedWindow (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (δ r y : ℝ) : ℂ :=
  ordinaryReflectedProfile K χ V δ (r * y) * (fixedDyadicWeight y : ℂ)

theorem ordinaryReflectedWindow_smooth
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ r : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) :
    ContDiff ℝ ∞ (ordinaryReflectedWindow K χ V δ r) := by
  have hcutoff : ContDiff ℝ ∞ (fun y : ℝ => (fixedDyadicWeight y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fixedDyadicWeight
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · exact (((contDiffOn_ordinaryReflectedProfile K hcomplex χ V hδ).contDiffAt
      (isOpen_Ioi.mem_nhds (mul_pos hr hy))).comp y
        (contDiff_const.mul contDiff_id).contDiffAt).mul hcutoff.contDiffAt
  · have hz : ordinaryReflectedWindow K χ V δ r =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [gt_mem_nhds (show y < 1 / 2 by linarith)] with x hx
      simp only [ordinaryReflectedWindow, fixedDyadicWeight_zero_of_le hx.le,
        Complex.ofReal_zero, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem ordinaryReflectedWindow_support (χ : HeckeCharacter K)
    (V : SmoothAnnularTest) (δ r : ℝ) :
    Function.support (ordinaryReflectedWindow K χ V δ r) ⊆ Icc (1 / 2) 2 := by
  intro y hy
  have hw : fixedDyadicWeight y ≠ 0 := by
    intro hz
    exact hy (by simp only [ordinaryReflectedWindow, hz, Complex.ofReal_zero, mul_zero])
  exact tsupport_fixedDyadicWeight (subset_tsupport fixedDyadicWeight hw)

/-- The annular test used by an actual reflected dyadic child. -/
def ordinaryReflectedWindowTest
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ r : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) : SmoothAnnularTest where
  toFun := ordinaryReflectedWindow K χ V δ r
  smooth := ordinaryReflectedWindow_smooth K hcomplex χ V hδ hr
  lower := 1 / 2
  upper := 2
  lower_pos := by norm_num
  upper_ge := by norm_num
  support := ordinaryReflectedWindow_support K χ V δ r

/-- The actual ideal norm at scale N uses the original reflected profile
at scale Y; this is the literal column calibration, not a model assertion. -/
theorem ordinaryReflectedWindow_calibration (χ : HeckeCharacter K)
    (V : SmoothAnnularTest) (δ N Y : ℝ) (hN : N ≠ 0) (I : NonzeroIdeal K) :
    ordinaryReflectedWindow K χ V δ (N / Y) (idealNorm K I / N) =
      ordinaryReflectedProfile K χ V δ (idealNorm K I / Y) *
        (fixedDyadicWeight (idealNorm K I / N) : ℂ) := by
  have hscale : N / Y * (idealNorm K I / N) = idealNorm K I / Y := by
    by_cases hY : Y = 0
    · simp only [hY, div_zero, zero_mul]
    · field_simp [hN, hY]
  simp only [ordinaryReflectedWindow, hscale]

end HeckeSkeleton.Moments.EngineInduction
