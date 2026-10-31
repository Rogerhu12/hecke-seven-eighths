import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.AnnularMellin
import HeckeGeneral.Analysis.TInputSeparatedProfiles
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Literal Mellin separation on a fixed larger annulus

The cutoff and every frequency column are selected independently of the
moving arithmetic row.  The original profile appears only in its actual
Mellin coefficient.  In particular that coefficient is independent of
the polynomial scale, so one copy serves both rectangles of a centered
coefficient.  The larger support interval is explicit; this file makes
no recursive-annulus closure or canonical-source assertion.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory Set Filter NumberField
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators Topology ContDiff

/-- An actual smooth plateau on `[a,b]`, supported on `[a/2,2*b]`.
Its construction precedes the moving annular profile. -/
def annularPlateau (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : SmoothAnnularTest where
  toFun y := ((Real.smoothTransition (2 * y / a - 1) *
    Real.smoothTransition (2 - y / b) : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp
    ((Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const a).sub contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub (contDiff_id.div_const b))))
  lower := a / 2
  upper := 2 * b
  lower_pos := by linarith
  upper_ge := by linarith
  support := by
    intro y hy
    have hb : 0 < b := ha.trans_le hab
    constructor
    · by_contra h
      have hz : 2 * y / a - 1 ≤ 0 := by
        have hd : 2 * y / a ≤ 1 :=
          (div_le_one ha).2 (by linarith)
        linarith
      exact hy (by rw [Real.smoothTransition.zero_of_nonpos hz, zero_mul,
        Complex.ofReal_zero])
    · by_contra h
      have hz : 2 - y / b ≤ 0 := by
        have hd : 2 ≤ y / b :=
          (le_div_iff₀ hb).2 (by linarith)
        linarith
      exact hy (by rw [Real.smoothTransition.zero_of_nonpos hz, mul_zero,
        Complex.ofReal_zero])

theorem annularPlateau_eq_one (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    {y : ℝ} (hy : y ∈ Icc a b) : (annularPlateau a b ha hab).toFun y = 1 := by
  have hb : 0 < b := ha.trans_le hab
  have hleft : 1 ≤ 2 * y / a - 1 := by
    have hd : 2 ≤ 2 * y / a := (le_div_iff₀ ha).2 (by linarith [hy.1])
    linarith
  have hright : 1 ≤ 2 - y / b := by
    have hd : y / b ≤ 1 := (div_le_one hb).2 hy.2
    linarith
  change ((Real.smoothTransition (2 * y / a - 1) *
    Real.smoothTransition (2 - y / b) : ℝ) : ℂ) = 1
  rw [Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright, one_mul, Complex.ofReal_one]

/-- A pure imaginary power of one fixed smooth cutoff.  The logarithmic
extension is total and nonzero, including at nonpositive arguments. -/
def annularMellinWindow (B : SmoothAnnularTest) (frequency y : ℝ) : ℂ :=
  B.toFun y * profilePower (-idealVerticalPoint 0 frequency) y

theorem annularMellinWindow_norm (B : SmoothAnnularTest) (frequency y : ℝ) :
    ‖annularMellinWindow B frequency y‖ = ‖B.toFun y‖ := by
  simp only [annularMellinWindow, profilePower, norm_mul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    idealVerticalPoint_re, neg_zero, mul_zero, zero_mul, sub_zero,
    Real.exp_zero, mul_one]

theorem annularMellinWindow_support (B : SmoothAnnularTest) (frequency : ℝ) :
    Function.support (annularMellinWindow B frequency) = Function.support B.toFun := by
  ext y
  simp only [Function.mem_support, annularMellinWindow, mul_ne_zero_iff,
    profilePower_ne_zero, and_true]

theorem annularMellinWindow_smooth (B : SmoothAnnularTest) (frequency : ℝ) :
    ContDiff ℝ ∞ (annularMellinWindow B frequency) := by
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    Real.contDiffOn_log.mono (fun y hy => ne_of_gt hy)
  have hpower : ContDiffOn ℝ ∞ (profilePower (-idealVerticalPoint 0 frequency))
      (Ioi 0) :=
    Complex.contDiff_exp.comp_contDiffOn
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hlog).mul contDiffOn_const)
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · exact B.smooth.contDiffAt.mul (hpower.contDiffAt (isOpen_Ioi.mem_nhds hy))
  · have hzero := (good_toFun B).eventually_zero (y := y) (by
      intro hmem
      exact hy (B.lower_pos.trans_le hmem.1))
    have hz : annularMellinWindow B frequency =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [hzero] with x hx
      simp only [annularMellinWindow, hx, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- A genuine smooth annular test, with exactly the original cutoff's
support and no row parameter. -/
def annularMellinWindowTest (B : SmoothAnnularTest) (frequency : ℝ) :
    SmoothAnnularTest where
  toFun := annularMellinWindow B frequency
  smooth := annularMellinWindow_smooth B frequency
  lower := B.lower
  upper := B.upper
  lower_pos := B.lower_pos
  upper_ge := B.upper_ge
  support := by rw [annularMellinWindow_support]; exact B.support

theorem continuous_annularMellinWindow (B : SmoothAnnularTest) (y : ℝ) :
    Continuous (fun frequency : ℝ => annularMellinWindow B frequency y) := by
  unfold annularMellinWindow profilePower
  exact continuous_const.mul (Complex.continuous_exp.comp
    (continuous_const.mul (continuous_idealVerticalPoint 0).neg))

/-- The true Mellin coefficient, chosen independently of every ideal
norm and of both rectangle scales. -/
def annularMellinCoefficient (V : SmoothAnnularTest) (frequency : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * mellin V.toFun (idealVerticalPoint 0 frequency)

theorem continuous_annularMellinCoefficient (V : SmoothAnnularTest) :
    Continuous (annularMellinCoefficient V) := by
  have hdiff : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  exact continuous_const.mul
    (hdiff.continuous.comp (continuous_idealVerticalPoint 0))

theorem integrable_annularMellinCoefficient (V : SmoothAnnularTest) :
    Integrable (annularMellinCoefficient V) := by
  exact (smoothAnnular_mellin_verticalIntegrable V 0).const_mul _

/-- A common coefficient constant, independent of the moving profile. -/
def mellinSeparationConstant (J : ℕ) : ℝ :=
  (1 + ‖(2 * (Real.pi : ℂ))⁻¹‖) * 2 ^ (J + 1)

theorem mellinSeparationConstant_pos (J : ℕ) : 0 < mellinSeparationConstant J := by
  unfold mellinSeparationConstant
  positivity

/-- Arbitrary polynomial decay is charged to the actual Euler seminorm,
with all constants selected before the profile or frequency. -/
theorem annularMellinCoefficient_norm_le (V : SmoothAnnularTest)
    (J : ℕ) (frequency : ℝ) :
    ‖annularMellinCoefficient V frequency‖ ≤
      mellinSeparationConstant J * testSeminorm V.toFun J 0 *
        (1 + |frequency|) ^ (-(J : ℝ)) := by
  let S : ℝ := testSeminorm V.toFun J 0
  have hS : 0 ≤ S := (Iint_nonneg V 0 0).trans
    (Iint_right_le V 0 J (Nat.zero_le _) 0)
  have hi₀ : Iint V 0 0 ≤ S := Iint_right_le V 0 J (Nat.zero_le _) 0
  have hiJ : Iint V J 0 ≤ S := Iint_right_le V J J le_rfl 0
  have hm : ‖mellin V.toFun (idealVerticalPoint 0 frequency)‖ ≤
      2 ^ (J + 1) * S * (1 + |frequency|) ^ (-(J : ℝ)) := by
    have h := smoothAnnular_mellin_vertical_decay V J 0 frequency
    simp only [neg_zero] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    calc
      2 ^ J * (Iint V 0 0 + Iint V J 0) ≤ 2 ^ J * (S + S) :=
        mul_le_mul_of_nonneg_left (add_le_add hi₀ hiJ) (by positivity)
      _ = 2 ^ (J + 1) * S := by rw [pow_succ]; ring
  calc
    ‖annularMellinCoefficient V frequency‖ =
        ‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖mellin V.toFun (idealVerticalPoint 0 frequency)‖ :=
      norm_mul _ _
    _ ≤ (1 + ‖(2 * (Real.pi : ℂ))⁻¹‖) *
        (2 ^ (J + 1) * S * (1 + |frequency|) ^ (-(J : ℝ))) :=
      mul_le_mul (by linarith) hm (norm_nonneg _) (by positivity)
    _ = _ := by unfold mellinSeparationConstant; ring

theorem integrable_annularMellinCoefficient_window (B V : SmoothAnnularTest) (y : ℝ) :
    Integrable (fun frequency : ℝ =>
      annularMellinCoefficient V frequency * annularMellinWindow B frequency y) := by
  apply ((integrable_annularMellinCoefficient V).norm.const_mul ‖B.toFun y‖).mono'
    ((continuous_annularMellinCoefficient V).mul
      (continuous_annularMellinWindow B y)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun frequency => by
    simpa only [norm_mul, annularMellinWindow_norm, mul_comm] using
      (le_refl (‖B.toFun y‖ * ‖annularMellinCoefficient V frequency‖))

/-- Pointwise inversion for all real arguments.  Only a real cutoff
coverage identity is supplied; the Mellin integral itself is proved. -/
theorem annularMellin_separation (B V : SmoothAnnularTest)
    (hB : ∀ y, V.toFun y ≠ 0 → B.toFun y = 1) (y : ℝ) :
    (∫ frequency : ℝ,
      annularMellinCoefficient V frequency * annularMellinWindow B frequency y) =
        V.toFun y := by
  by_cases hy : 0 < y
  · have heq : (fun frequency : ℝ =>
        annularMellinCoefficient V frequency * annularMellinWindow B frequency y) =
      (fun frequency : ℝ => B.toFun y * ((2 * (Real.pi : ℂ))⁻¹ *
        ((y : ℂ) ^ (-idealVerticalPoint 0 frequency) *
          mellin V.toFun (idealVerticalPoint 0 frequency)))) := by
      funext frequency
      unfold annularMellinCoefficient annularMellinWindow
      rw [profilePower_eq_cpow _ hy]
      ring
    rw [heq, integral_const_mul, integral_const_mul,
      smoothAnnular_mellin_inversion V 0 hy]
    by_cases hz : V.toFun y = 0
    · rw [hz, mul_zero]
    · rw [hB y hz, one_mul]
  · have hVz : V.toFun y = 0 := (good_toFun V).zero y (by
      intro hmem
      exact hy (V.lower_pos.trans_le hmem.1))
    have hBz : B.toFun y = 0 := (good_toFun B).zero y (by
      intro hmem
      exact hy (B.lower_pos.trans_le hmem.1))
    simp only [annularMellinWindow, hBz, zero_mul, mul_zero, integral_zero, hVz]

/-- A finite coefficient sum interchanges with the genuine Mellin
integral.  No estimate on the arithmetic coefficients is needed. -/
theorem finite_sum_annularMellin_separation {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (location : ι → ℝ) (B V : SmoothAnnularTest)
    (hB : ∀ y, V.toFun y ≠ 0 → B.toFun y = 1) :
    (∑ i ∈ s, a i * V.toFun (location i)) =
      ∫ frequency : ℝ, annularMellinCoefficient V frequency *
        ∑ i ∈ s, a i * annularMellinWindow B frequency (location i) := by
  have hpoint (frequency : ℝ) :
      annularMellinCoefficient V frequency *
          ∑ i ∈ s, a i * annularMellinWindow B frequency (location i) =
        ∑ i ∈ s, a i *
          (annularMellinCoefficient V frequency * annularMellinWindow B frequency (location i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hpoint]
  rw [integral_finset_sum s (fun i _ =>
    (integrable_annularMellinCoefficient_window B V (location i)).const_mul (a i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, annularMellin_separation B V hB]

end HeckeSkeleton.Moments.EngineInduction
