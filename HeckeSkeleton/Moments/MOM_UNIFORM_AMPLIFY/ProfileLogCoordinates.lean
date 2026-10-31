import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileFourier
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Literal logarithmic coordinates for the Euler test seminorm

On the positive line the Euler operator is conjugate to ordinary
differentiation under y = exp x.  The integral comparison below uses the
repository's actual Euler iterates and its actual two weights.  It supplies
the missing bridge from the logarithmic detector profiles to the source
moment seminorm, without an extra scale or frequency supremum assumption.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open MeasureTheory Set
open HeckeGeneral.ThetaSkeleton.Global
open _root_.ExpansionRecipe.LogProfile
open scoped Classical BigOperators ContDiff SchwartzMap

def profileLogPullback (f : ℝ → ℂ) (x : ℝ) : ℂ := f (Real.exp x)

theorem eulerDerivative_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (eulerDerivative f) := by
  exact Complex.ofRealCLM.contDiff.mul ((contDiff_infty_iff_deriv.mp hf).2)

theorem eulerDerivativeOrder_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ (eulerDerivativeOrder j f) := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    change ContDiff ℝ ∞ ((eulerDerivative^[j + 1]) f)
    rw [Function.iterate_succ_apply']
    exact eulerDerivative_smooth ih

theorem deriv_profileLogPullback {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    deriv (profileLogPullback f) x = eulerDerivative f (Real.exp x) := by
  have h := ((hf.differentiable (by simp)).differentiableAt.hasDerivAt).comp x
    (Real.hasDerivAt_exp x)
  simpa only [profileLogPullback, eulerDerivative, Function.comp_def,
    Complex.real_smul, mul_comm] using h.deriv

/-- Every order is an identity of the actual functions, before any norm,
integral, support restriction, or estimate is applied. -/
theorem iteratedDeriv_profileLogPullback {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (profileLogPullback f) x = eulerDerivativeOrder j f (Real.exp x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    have hfun : iteratedDeriv j (profileLogPullback f) =
        profileLogPullback (eulerDerivativeOrder j f) := funext ih
    rw [iteratedDeriv_succ, hfun,
      deriv_profileLogPullback (eulerDerivativeOrder_smooth hf j)]
    change eulerDerivative ((eulerDerivative^[j]) f) (Real.exp x) =
      ((eulerDerivative^[j + 1]) f) (Real.exp x)
    rw [Function.iterate_succ_apply']

def logEulerWeight (A x : ℝ) : ℝ := Real.exp (x / 4) + Real.exp (-A * x)

def logEulerMass (L A : ℝ) : ℝ := ∫ x in Icc (-L) L, logEulerWeight A x

theorem logEulerWeight_nonneg (A x : ℝ) : 0 ≤ logEulerWeight A x := by
  unfold logEulerWeight
  positivity

theorem logEulerWeight_continuous (A : ℝ) : Continuous (logEulerWeight A) := by
  unfold logEulerWeight
  fun_prop

theorem logEulerMass_nonneg (L A : ℝ) : 0 ≤ logEulerMass L A :=
  setIntegral_nonneg measurableSet_Icc (fun x _ => logEulerWeight_nonneg A x)

/-- Exact substitution in the Euler integral. -/
theorem testIntegral_log_coordinates {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (A : ℝ) :
    testIntegral f j A =
      ∫ x : ℝ, ‖iteratedDeriv j (profileLogPullback f) x‖ * logEulerWeight A x := by
  unfold testIntegral
  rw [← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [iteratedDeriv_profileLogPullback hf]
  simp only [smul_eq_mul]
  have hpos := Real.exp_pos x
  have hquarter : Real.exp x ^ (1 / 4 : ℝ) = Real.exp (x / 4) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hneg : Real.exp x ^ (-A) = Real.exp (-A * x) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hquarter, hneg]
  unfold logEulerWeight
  field_simp

/-- An ordinary log-coordinate Schwartz seminorm controls the exact
weighted Euler integral of an annular profile. -/
theorem testIntegral_le_log_seminorm {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (W : SchwartzMap ℝ ℂ) (hlog : profileLogPullback f = W)
    (L A : ℝ) (hsupport : tsupport W ⊆ Icc (-L) L) (j : ℕ) :
    testIntegral f j A ≤ logEulerMass L A * SchwartzMap.seminorm ℝ 0 j W := by
  rw [testIntegral_log_coordinates hf, hlog]
  have hzero (x : ℝ) (hx : x ∉ Icc (-L) L) : iteratedDeriv j W x = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    apply norm_eq_zero.mpr
    apply Function.notMem_support.mp
    intro h
    exact hx (hsupport ((support_iteratedFDeriv_subset j) h))
  have hI : (∫ x : ℝ, ‖iteratedDeriv j W x‖ * logEulerWeight A x) =
      ∫ x in Icc (-L) L, ‖iteratedDeriv j W x‖ * logEulerWeight A x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])).symm
  rw [hI, mul_comm (logEulerMass L A)]
  unfold logEulerMass
  rw [← integral_const_mul]
  have hg : IntegrableOn (fun x : ℝ => ‖iteratedDeriv j W x‖ * logEulerWeight A x)
      (Icc (-L) L) :=
    (((W.smooth ⊤).continuous_iteratedDeriv j (by simp)).norm.mul
      (logEulerWeight_continuous A)).continuousOn.integrableOn_Icc
  have hw := (logEulerWeight_continuous A).continuousOn.integrableOn_Icc (a := -L) (b := L)
  apply setIntegral_mono_on hg (hw.const_mul _) measurableSet_Icc
  intro x _
  apply mul_le_mul_of_nonneg_right _ (logEulerWeight_nonneg A x)
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
    SchwartzMap.le_seminorm ℝ 0 j W x

theorem testSeminorm_le_log_derivative_bound {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (W : SchwartzMap ℝ ℂ) (hlog : profileLogPullback f = W)
    (L A : ℝ) (hsupport : tsupport W ⊆ Icc (-L) L) (J : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hderiv : ∀ j ≤ J, SchwartzMap.seminorm ℝ 0 j W ≤ B) :
    testSeminorm f J A ≤ logEulerMass L A * B := by
  apply testSeminorm_le_of_integrals _ _ _ _ (mul_nonneg (logEulerMass_nonneg L A) hB)
  intro j hj
  exact (testIntegral_le_log_seminorm hf W hlog L A hsupport j).trans
    (mul_le_mul_of_nonneg_left (hderiv j hj) (logEulerMass_nonneg L A))

/-- Uniform actual Euler-seminorm control for norm-power twists of a fixed
smooth compact log profile.  The raw profile identity, rather than an
Euler estimate, is the connection to the original `MomentData` slice. -/
theorem compact_log_twist_testSeminorm (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hwindow : tsupport Ω ⊆ Icc (-L) L) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.re| ≤ H →
      ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f →
      (∀ x : ℝ, f (Real.exp x) = Ω x * linearExp z x) →
        testSeminorm f J A ≤ C * (1 + |z.im|) ^ J := by
  obtain ⟨C, hC, hb⟩ := compact_exp_twist_uniform_seminorm Ω hΩc hΩ H L hH hL hwindow J
  have hmass := logEulerMass_nonneg L A
  refine ⟨logEulerMass L A * C + 1, by positivity, ?_⟩
  intro z hz f hf hid
  let W := compactExpTwist Ω hΩc hΩ z
  have hlog : profileLogPullback f = W := funext hid
  have hs : tsupport W ⊆ Icc (-L) L := tsupport_mul_subset_left.trans hwindow
  have hbound := testSeminorm_le_log_derivative_bound hf W hlog L A hs J
    (C * (1 + |z.im|) ^ J) (by positivity)
    (fun j hj => by simpa only [pow_zero, one_mul] using hb z hz 0 j hj)
  exact hbound.trans (by nlinarith [pow_nonneg (by positivity : 0 ≤ 1 + |z.im|) J])

end HeckeSkeleton.Moments.UniformAmplify
