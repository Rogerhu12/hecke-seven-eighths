import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileLogCoordinates
import HeckeSkeleton.ExpansionModels.CutoffLogProfile
import HeckeGeneral.Analysis.TInputSeparatedProfiles

/-!
# Actual annular norm-power profiles, including an independent cutoff ratio

The two-scale cutoff and the norm-power factor are the literal functions
used by `recipeCutoffTwist`, `IdealTest.freezeTwist`, and the physical prime
windows.  The cutoff ratio is arbitrary and nonnegative.  The Fourier
derivative bounds cancel its scaling cost, and the original Euler test
seminorm has only polynomial dependence on the imaginary twist.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open MeasureTheory Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Analysis.ConditionalMoments
open _root_.ExpansionRecipe.LogProfile
open scoped Classical BigOperators ContDiff SchwartzMap Topology

def annularLogRadius (W : SmoothAnnularTest) : ℝ :=
  max |Real.log W.lower| |Real.log W.upper|

theorem annularLogRadius_nonneg (W : SmoothAnnularTest) : 0 ≤ annularLogRadius W :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem annular_log_support (W : SmoothAnnularTest) :
    tsupport (profileLogPullback W.toFun) ⊆ Icc (-annularLogRadius W) (annularLogRadius W) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hs := W.support hx
  have hlo : Real.log W.lower ≤ x := by
    simpa using Real.log_le_log W.lower_pos hs.1
  have hup : x ≤ Real.log W.upper := by
    simpa using Real.log_le_log (Real.exp_pos x) hs.2
  have hl : |Real.log W.lower| ≤ annularLogRadius W := le_max_left _ _
  have hu : |Real.log W.upper| ≤ annularLogRadius W := le_max_right _ _
  exact ⟨by linarith [(abs_le.mp hl).1], by linarith [(abs_le.mp hu).2]⟩

theorem annular_log_compact (W : SmoothAnnularTest) :
    HasCompactSupport (profileLogPullback W.toFun) :=
  IsCompact.of_isClosed_subset isCompact_Icc isClosed_tsupport (annular_log_support W)

theorem annular_log_smooth (W : SmoothAnnularTest) :
    ContDiff ℝ ∞ (profileLogPullback W.toFun) := W.smooth.comp Real.contDiff_exp

def annularNormTwist (W : SmoothAnnularTest) (z : ℂ) (y : ℝ) : ℂ :=
  W.toFun y * profilePower z y

def annularCutoffNormTwist (W : SmoothAnnularTest) (V : ℝ → ℂ) (R : ℝ)
    (z : ℂ) (y : ℝ) : ℂ := W.toFun y * V (R * y) * profilePower z y

theorem supported_norm_twist_smooth (f : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hf : ContDiff ℝ ∞ f) (hs : Function.support f ⊆ Icc a b) (z : ℂ) :
    ContDiff ℝ ∞ (fun y : ℝ => f y * profilePower z y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : (fun y : ℝ => f y * profilePower z y) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      have hzero : f y = 0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [hzero]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · unfold profilePower
    exact hf.contDiffAt.mul
      (((Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx)).mul
        contDiffAt_const).cexp)

theorem annularNormTwist_smooth (W : SmoothAnnularTest) (z : ℂ) :
    ContDiff ℝ ∞ (annularNormTwist W z) :=
  supported_norm_twist_smooth W.toFun W.lower W.upper W.lower_pos W.smooth W.support z

theorem annularCutoffNormTwist_smooth (W : SmoothAnnularTest) (V : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (R : ℝ) (z : ℂ) :
    ContDiff ℝ ∞ (annularCutoffNormTwist W V R z) :=
  supported_norm_twist_smooth (fun y : ℝ => W.toFun y * V (R * y)) W.lower W.upper
    W.lower_pos (W.smooth.mul (hV.comp (by fun_prop)))
    ((Function.support_mul_subset_left).trans W.support) z

theorem annularNormTwist_support (W : SmoothAnnularTest) (z : ℂ) :
    Function.support (annularNormTwist W z) ⊆ Icc W.lower W.upper :=
  Function.support_mul_subset_left.trans W.support

theorem annularCutoffNormTwist_support (W : SmoothAnnularTest) (V : ℝ → ℂ)
    (R : ℝ) (z : ℂ) :
    Function.support (annularCutoffNormTwist W V R z) ⊆ Icc W.lower W.upper :=
  Function.support_mul_subset_left.trans (Function.support_mul_subset_left.trans W.support)

theorem annularNormTwist_log (W : SmoothAnnularTest) (z : ℂ) (x : ℝ) :
    annularNormTwist W z (Real.exp x) = profileLogPullback W.toFun x * linearExp z x := by
  simp only [annularNormTwist, profilePower, Real.log_exp, profileLogPullback, linearExp]
  rw [mul_comm (x : ℂ) z]

theorem annularCutoffNormTwist_log (W : SmoothAnnularTest) (V : ℝ → ℂ)
    (R : ℝ) (z : ℂ) (x : ℝ) :
    annularCutoffNormTwist W V R z (Real.exp x) =
      profileLogPullback W.toFun x * V (R * Real.exp x) * linearExp z x := by
  simp only [annularCutoffNormTwist, profilePower, Real.log_exp, profileLogPullback, linearExp]
  rw [mul_comm (x : ℂ) z]

theorem annular_norm_twist_testSeminorm (W : SmoothAnnularTest)
    (H : ℝ) (hH : 0 ≤ H) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.re| ≤ H →
      testSeminorm (annularNormTwist W z) J A ≤ C * (1 + |z.im|) ^ J := by
  obtain ⟨C, hC, hb⟩ := compact_log_twist_testSeminorm (profileLogPullback W.toFun)
    (annular_log_compact W) (annular_log_smooth W) H (annularLogRadius W) hH
    (annularLogRadius_nonneg W) (annular_log_support W) J A
  exact ⟨C, hC, fun z hz => hb z hz _ (annularNormTwist_smooth W z) (annularNormTwist_log W z)⟩

/-- Uniform control of the literal cutoff profile in the independent U,D
family.  No upper or lower bound for the ratio R is required. -/
theorem annular_cutoff_norm_twist_testSeminorm (W : SmoothAnnularTest)
    (V : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0 ≤ H) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R → ∀ z : ℂ, |z.re| ≤ H →
      testSeminorm (annularCutoffNormTwist W V R z) J A ≤ C * (1 + |z.im|) ^ J := by
  let Ω := profileLogPullback W.toFun
  let L := annularLogRadius W
  obtain ⟨C, hC, hb⟩ := scaled_compact_exp_twist_uniform_seminorm Ω V
    (annular_log_compact W) (annular_log_smooth W) H L hH
    (annularLogRadius_nonneg W) (annular_log_support W) J
  have hmass := logEulerMass_nonneg L A
  refine ⟨logEulerMass L A * C + 1, by positivity, ?_⟩
  intro R hR z hz
  let F := scaledCompactExpTwist Ω V (annular_log_compact W) (annular_log_smooth W) R z
  have hlog : profileLogPullback (annularCutoffNormTwist W V R z) = F :=
    funext (annularCutoffNormTwist_log W V R z)
  have hs : tsupport F ⊆ Icc (-L) L :=
    (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans (annular_log_support W)
  have hbound := testSeminorm_le_log_derivative_bound
    (annularCutoffNormTwist_smooth W V (V.smooth ⊤) R z) F hlog L A hs J
    (C * (1 + |z.im|) ^ J) (by positivity)
    (fun j hj => by simpa only [pow_zero, one_mul] using hb R hR z hz 0 j hj)
  exact hbound.trans (by nlinarith [pow_nonneg (by positivity : 0 ≤ 1 + |z.im|) J])

theorem annularCutoffNormTwist_cutoff_extension (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) :
    annularCutoffNormTwist W V R z =
      annularCutoffNormTwist W (cutoffSchwartz V hV hzero) R z := by
  funext y
  by_cases hy : 0 ≤ y
  · unfold annularCutoffNormTwist
    rw [cutoffSchwartz_apply, cutoffSchwartzFun_eq_nonneg V hone (mul_nonneg hR hy)]
  · have hW : W.toFun y = 0 := by
      by_contra hn
      exact hy (W.lower_pos.le.trans (W.support hn).1)
    simp [annularCutoffNormTwist, hW]

/-- The detector's original one-sided cutoff is used without changing its
values; the compact Schwartz extension only proves its estimate. -/
theorem annular_oneSided_cutoff_norm_twist_testSeminorm (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (H : ℝ) (hH : 0 ≤ H) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R → ∀ z : ℂ, |z.re| ≤ H →
      testSeminorm (annularCutoffNormTwist W V R z) J A ≤ C * (1 + |z.im|) ^ J := by
  obtain ⟨C, hC, hb⟩ := annular_cutoff_norm_twist_testSeminorm W
    (cutoffSchwartz V hV hzero) H hH J A
  refine ⟨C, hC, ?_⟩
  intro R hR z hz
  rw [annularCutoffNormTwist_cutoff_extension W V hV hone hzero R hR z]
  exact hb R hR z hz

theorem polynomial_twist_height {M T v : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hv : |v| ≤ M * (1 + T)) (J : ℕ) :
    (1 + |v|) ^ J ≤ (1 + M) ^ J * (1 + T) ^ (J : ℝ) := by
  rw [Real.rpow_natCast, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

theorem annular_norm_twist_slice_control (W : SmoothAnnularTest)
    (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ z : ℂ,
      |z.re| ≤ H → |z.im| ≤ M * (1 + T) →
      SliceControl J A C (J : ℝ) W.lower W.upper T (annularNormTwist W z) := by
  obtain ⟨C, hC, hb⟩ := annular_norm_twist_testSeminorm W H hH J A
  refine ⟨C * (1 + M) ^ J, mul_pos hC (pow_pos (by positivity) _), ?_⟩
  intro T hT z hz hv
  refine ⟨annularNormTwist_smooth W z, annularNormTwist_support W z, ?_⟩
  exact (hb z hz).trans ((mul_le_mul_of_nonneg_left
    (polynomial_twist_height hM hT hv J) hC.le).trans_eq (by ring))

theorem annular_oneSided_cutoff_norm_twist_slice_control (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ R : ℝ, 0 ≤ R →
      ∀ z : ℂ, |z.re| ≤ H → |z.im| ≤ M * (1 + T) →
      SliceControl J A C (J : ℝ) W.lower W.upper T (annularCutoffNormTwist W V R z) := by
  obtain ⟨C, hC, hb⟩ := annular_oneSided_cutoff_norm_twist_testSeminorm W V hV hone hzero H hH J A
  refine ⟨C * (1 + M) ^ J, mul_pos hC (pow_pos (by positivity) _), ?_⟩
  intro T hT R hR z hz hv
  refine ⟨annularCutoffNormTwist_smooth W V hV R z,
    annularCutoffNormTwist_support W V R z, ?_⟩
  exact (hb R hR z hz).trans ((mul_le_mul_of_nonneg_left
    (polynomial_twist_height hM hT hv J) hC.le).trans_eq (by ring))

def annularMixedWindowFun (W : SmoothAnnularTest) (r s : ℕ) (y : ℝ) : ℂ :=
  (Real.log y : ℂ) ^ r * (Complex.I * (Real.log y : ℂ)) ^ s * W.toFun y

theorem annularMixedWindowFun_smooth (W : SmoothAnnularTest) (r s : ℕ) :
    ContDiff ℝ ∞ (annularMixedWindowFun W r s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : annularMixedWindowFun W r s =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds W.lower_pos] with y hy
      have hzero : W.toFun y = 0 := by
        by_contra hn
        exact (not_le_of_gt hy) (W.support hn).1
      simp [annularMixedWindowFun, hzero]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hlog : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx)
    exact ((hlog.pow r).mul ((contDiffAt_const.mul hlog).pow s)).mul W.smooth.contDiffAt

def annularMixedWindow (W : SmoothAnnularTest) (r s : ℕ) : SmoothAnnularTest where
  toFun := annularMixedWindowFun W r s
  smooth := annularMixedWindowFun_smooth W r s
  lower := W.lower
  upper := W.upper
  lower_pos := W.lower_pos
  upper_ge := W.upper_ge
  support := Function.support_mul_subset_right.trans W.support

/-- Literal mixed derivatives of the original norm-power profile,
including the project's total convention at nonpositive y. -/
theorem annularNormTwist_mixed_derivative (W : SmoothAnnularTest)
    (r s : ℕ) (a ν y : ℝ) :
    iteratedDeriv r (fun a' : ℝ => iteratedDeriv s
      (fun ν' : ℝ => annularNormTwist W ((a' : ℂ) + (ν' : ℂ) * Complex.I) y) ν) a =
      annularNormTwist (annularMixedWindow W r s) ((a : ℂ) + (ν : ℂ) * Complex.I) y := by
  have he (a' ν' : ℝ) :
      annularNormTwist W ((a' : ℂ) + (ν' : ℂ) * Complex.I) y =
      (fun _ : ℝ => W.toFun y) (Real.log y) *
        linearExp ((a' : ℂ) + (ν' : ℂ) * Complex.I) (Real.log y) := by
    unfold annularNormTwist profilePower linearExp
    rw [mul_comm (Real.log y : ℂ)]
  simp_rw [he]
  rw [mixed_parameter_derivative]
  unfold annularNormTwist annularMixedWindow annularMixedWindowFun profilePower linearExp
  rw [mul_comm (Real.log y : ℂ)]

/-- The mixed profile orders can be chosen before the source height.
Their constants depend on r,s, but the polynomial height degree remains J. -/
theorem annular_mixed_norm_twist_slice_control (W : SmoothAnnularTest)
    (r s : ℕ) (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ z : ℂ,
      |z.re| ≤ H → |z.im| ≤ M * (1 + T) →
      SliceControl J A C (J : ℝ) W.lower W.upper T
        (annularNormTwist (annularMixedWindow W r s) z) :=
  annular_norm_twist_slice_control (annularMixedWindow W r s) H M hH hM J A

theorem annular_mixed_oneSided_cutoff_norm_twist_slice_control (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (r s : ℕ) (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ R : ℝ, 0 ≤ R →
      ∀ z : ℂ, |z.re| ≤ H → |z.im| ≤ M * (1 + T) →
      SliceControl J A C (J : ℝ) W.lower W.upper T
        (annularCutoffNormTwist (annularMixedWindow W r s) V R z) :=
  annular_oneSided_cutoff_norm_twist_slice_control (annularMixedWindow W r s) V hV hone hzero
    H M hH hM J A

end HeckeSkeleton.Moments.UniformAmplify
