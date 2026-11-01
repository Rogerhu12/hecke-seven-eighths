import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileNormTwists
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileEuler

/-!
# Literal mixed derivatives in the inverse cutoff scale

The original inverse profile has ratio D / U^(2ξ₃).  Its ξ₃ derivatives
are the actual Euler derivatives of the cutoff and cost one factor
-2 log U per derivative.  The finite mixed real/imaginary derivatives
remain the logarithmically weighted annular windows already constructed.
All constants below are chosen before U, D, ξ₃ and the moving height.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open MeasureTheory Set
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Analysis.ConditionalMoments
open _root_.ExpansionRecipe.LogProfile
open scoped Classical BigOperators ContDiff SchwartzMap

theorem profileEulerOrder_succ (j : ℕ) (f : ℝ → ℂ) :
    eulerDerivativeOrder (j + 1) f = eulerDerivative (eulerDerivativeOrder j f) := by
  simp only [eulerDerivativeOrder, Function.iterate_succ_apply']

theorem eulerDerivative_const_mul (c : ℂ) (f : ℝ → ℂ) :
    eulerDerivative (fun y => c * f y) = fun y => c * eulerDerivative f y := by
  funext y
  simp only [eulerDerivative, deriv_const_mul_field]
  ring

theorem eulerDerivativeOrder_const_mul (c : ℂ) (j : ℕ) (f : ℝ → ℂ) :
    eulerDerivativeOrder j (fun y => c * f y) =
      fun y => c * eulerDerivativeOrder j f y := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [profileEulerOrder_succ, ih, eulerDerivative_const_mul, profileEulerOrder_succ]

theorem testIntegral_const_mul (c : ℂ) (f : ℝ → ℂ) (j : ℕ) (A : ℝ) :
    testIntegral (fun y => c * f y) j A = ‖c‖ * testIntegral f j A := by
  unfold testIntegral
  simp_rw [eulerDerivativeOrder_const_mul, norm_mul]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  ring

theorem testSeminorm_const_mul_le (c : ℂ) (f : ℝ → ℂ) (J : ℕ) (A : ℝ) :
    testSeminorm (fun y => c * f y) J A ≤ ‖c‖ * testSeminorm f J A := by
  apply testSeminorm_le_of_integrals _ J A _
    (mul_nonneg (norm_nonneg c) (testSeminorm_nonneg f J A))
  intro j hj
  rw [testIntegral_const_mul]
  exact mul_le_mul_of_nonneg_left (testIntegral_le_testSeminorm f A hj) (norm_nonneg c)

theorem SliceControl.const_mul {J : ℕ} {A C H a b T : ℝ} {f : ℝ → ℂ}
    (h : SliceControl J A C H a b T f) (c : ℂ) :
    SliceControl J A (‖c‖ * C) H a b T (fun y => c * f y) := by
  refine ⟨contDiff_const.mul h.1, fun y hy => h.2.1 y (right_ne_zero_of_mul hy), ?_⟩
  exact (testSeminorm_const_mul_le c f J A).trans
    ((mul_le_mul_of_nonneg_left h.2.2 (norm_nonneg c)).trans_eq (by ring))

theorem hasDerivAt_profileExpScale (C b x : ℝ) :
    HasDerivAt (fun t : ℝ => C * Real.exp (b * t))
      (b * (C * Real.exp (b * x))) x := by
  convert (((hasDerivAt_id x).const_mul b).exp.const_mul C) using 1 <;>
    simp only [id_eq] <;> ring

theorem deriv_profileExpScale_comp {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (C b x : ℝ) :
    deriv (fun t : ℝ => f (C * Real.exp (b * t))) x =
      (b : ℂ) * eulerDerivative f (C * Real.exp (b * x)) := by
  have h := ((hf.differentiable (by simp)).differentiableAt.hasDerivAt).scomp x
    (hasDerivAt_profileExpScale C b x)
  simpa only [eulerDerivative, Function.comp_def, Complex.real_smul,
    Complex.ofReal_mul, mul_assoc] using h.deriv

theorem iteratedDeriv_profileExpScale_comp {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (C b x : ℝ) :
    iteratedDeriv n (fun t : ℝ => f (C * Real.exp (b * t))) x =
      (b : ℂ) ^ n * eulerDerivativeOrder n f (C * Real.exp (b * x)) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]; rfl
  | succ n ih =>
    have he : iteratedDeriv n (fun t : ℝ => f (C * Real.exp (b * t))) =
        fun t => (b : ℂ) ^ n * eulerDerivativeOrder n f (C * Real.exp (b * t)) :=
      funext ih
    rw [iteratedDeriv_succ, he, deriv_const_mul_field,
      deriv_profileExpScale_comp (eulerDerivativeOrder_smooth hf n), profileEulerOrder_succ,
      pow_succ]
    ring

theorem inverseCutoffRatio_expScale (U D ξ : ℝ) (hU : 0 < U) :
    D / U ^ (2 * ξ) = D * Real.exp ((-2 * Real.log U) * ξ) := by
  rw [Real.rpow_def_of_pos hU, div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

theorem annularCutoffNormTwist_mixed_derivative (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (R : ℝ) (r s : ℕ) (a ν y : ℝ) :
    iteratedDeriv r (fun a' : ℝ => iteratedDeriv s
      (fun ν' : ℝ => annularCutoffNormTwist W V R
        ((a' : ℂ) + (ν' : ℂ) * Complex.I) y) ν) a =
      annularCutoffNormTwist (annularMixedWindow W r s) V R
        ((a : ℂ) + (ν : ℂ) * Complex.I) y := by
  have he (a' ν' : ℝ) :
      annularCutoffNormTwist W V R ((a' : ℂ) + (ν' : ℂ) * Complex.I) y =
        (fun _ : ℝ => W.toFun y * V (R * y)) (Real.log y) *
          linearExp ((a' : ℂ) + (ν' : ℂ) * Complex.I) (Real.log y) := by
    unfold annularCutoffNormTwist profilePower linearExp
    rw [mul_comm (Real.log y : ℂ)]
  simp_rw [he]
  rw [mixed_parameter_derivative (fun _ : ℝ => W.toFun y * V (R * y)) r s a ν (Real.log y)]
  simp only [annularCutoffNormTwist, annularMixedWindow, annularMixedWindowFun,
    profilePower, linearExp]
  rw [mul_comm (Real.log y : ℂ) ((a : ℂ) + (ν : ℂ) * Complex.I)]
  ring

/-- The scale derivative is an identity of the original total profile,
before any support restriction or norm is taken. -/
theorem annularCutoffNormTwist_scale_derivative (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (U D : ℝ) (hU : 0 < U) (z : ℂ) (n : ℕ) (ξ y : ℝ) :
    iteratedDeriv n
      (fun q : ℝ => annularCutoffNormTwist W V (D / U ^ (2 * q)) z y) ξ =
      ((-2 * Real.log U : ℝ) : ℂ) ^ n *
        annularCutoffNormTwist W (eulerDerivativeOrder n V) (D / U ^ (2 * ξ)) z y := by
  have he : (fun q : ℝ => annularCutoffNormTwist W V (D / U ^ (2 * q)) z y) =
      fun q => (W.toFun y * profilePower z y) *
        V ((D * y) * Real.exp ((-2 * Real.log U) * q)) := by
    funext q
    rw [annularCutoffNormTwist, inverseCutoffRatio_expScale U D q hU]
    have harg : D * Real.exp ((-2 * Real.log U) * q) * y =
        (D * y) * Real.exp ((-2 * Real.log U) * q) := by ring
    rw [harg]
    ring
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_profileExpScale_comp hV]
  unfold annularCutoffNormTwist
  rw [inverseCutoffRatio_expScale U D ξ hU]
  have harg : D * Real.exp ((-2 * Real.log U) * ξ) * y =
      (D * y) * Real.exp ((-2 * Real.log U) * ξ) := by ring
  rw [harg]
  ring

/-- The actual mixed parameter derivative.  In particular, the scale
parameter is differentiated as a real variable; it is not an extra index
with a derivative estimate supplied as a hypothesis. -/
def annularMixedScaleJet (W : SmoothAnnularTest) (V : ℝ → ℂ) (U D : ℝ)
    (r s n : ℕ) (a ν ξ y : ℝ) : ℂ :=
  iteratedDeriv n (fun q : ℝ => iteratedDeriv r (fun a' : ℝ => iteratedDeriv s
    (fun ν' : ℝ => annularCutoffNormTwist W V (D / U ^ (2 * q))
      ((a' : ℂ) + (ν' : ℂ) * Complex.I) y) ν) a) ξ

theorem annularMixedScaleJet_formula (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (U D : ℝ) (hU : 0 < U)
    (r s n : ℕ) (a ν ξ y : ℝ) :
    annularMixedScaleJet W V U D r s n a ν ξ y =
      ((-2 * Real.log U : ℝ) : ℂ) ^ n *
        annularCutoffNormTwist (annularMixedWindow W r s) (eulerDerivativeOrder n V)
          (D / U ^ (2 * ξ)) ((a : ℂ) + (ν : ℂ) * Complex.I) y := by
  unfold annularMixedScaleJet
  simp_rw [annularCutoffNormTwist_mixed_derivative]
  exact annularCutoffNormTwist_scale_derivative _ V hV U D hU _ n ξ y

theorem annularMixedScaleJet_smooth (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (U D : ℝ) (hU : 0 < U)
    (r s n : ℕ) (a ν ξ : ℝ) :
    ContDiff ℝ ∞ (annularMixedScaleJet W V U D r s n a ν ξ) := by
  have he := funext (annularMixedScaleJet_formula W V hV U D hU r s n a ν ξ)
  rw [he]
  exact contDiff_const.mul (annularCutoffNormTwist_smooth (annularMixedWindow W r s)
    (eulerDerivativeOrder n V) (eulerDerivativeOrder_smooth hV n) _ _)

theorem annularMixedScaleJet_support (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (U D : ℝ) (hU : 0 < U)
    (r s n : ℕ) (a ν ξ : ℝ) :
    Function.support (annularMixedScaleJet W V U D r s n a ν ξ) ⊆ Icc W.lower W.upper := by
  intro y hy
  rw [Function.mem_support, annularMixedScaleJet_formula W V hV U D hU r s n a ν ξ y] at hy
  exact annularCutoffNormTwist_support (annularMixedWindow W r s) _ _ _
    (right_ne_zero_of_mul hy)

theorem annularMixedScaleJet_cutoff_extension (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1) (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (U D : ℝ) (hU : 0 < U) (hD : 0 ≤ D) (r s n : ℕ) (a ν ξ : ℝ) :
    annularMixedScaleJet W V U D r s n a ν ξ =
      annularMixedScaleJet W (cutoffSchwartz V hV hzero) U D r s n a ν ξ := by
  have he (q α v : ℝ) := annularCutoffNormTwist_cutoff_extension W V hV hone hzero
    (D / U ^ (2 * q)) (div_nonneg hD (Real.rpow_pos_of_pos hU _).le)
    ((α : ℂ) + (v : ℂ) * Complex.I)
  funext y
  unfold annularMixedScaleJet
  simp_rw [he]

theorem logScaleFactor_norm (U : ℝ) (n : ℕ) :
    ‖((-2 * Real.log U : ℝ) : ℂ) ^ n‖ = (2 : ℝ) ^ n * |Real.log U| ^ n := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_pow]
  norm_num

/-- All mixed scale derivatives have a finite logarithmic cost, while
the cutoff ratio remains completely independent. -/
theorem annular_mixed_scale_jet_testSeminorm (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1) (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (r s n J : ℕ) (H A : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 0 < U → ∀ D : ℝ, 0 ≤ D →
      ∀ ξ a ν : ℝ, |a| ≤ H →
        testSeminorm (annularMixedScaleJet W V U D r s n a ν ξ) J A ≤
          C * (1 + |Real.log U|) ^ n * (1 + |ν|) ^ J := by
  let V₀ := cutoffSchwartz V hV hzero
  obtain ⟨C, hC, hb⟩ := annular_cutoff_norm_twist_testSeminorm
    (annularMixedWindow W r s) (profileEulerIterCLM n V₀) H hH J A
  refine ⟨C * (2 : ℝ) ^ n, mul_pos hC (by positivity), ?_⟩
  intro U hU D hD ξ a ν ha
  rw [annularMixedScaleJet_cutoff_extension W V hV hone hzero U D hU hD r s n a ν ξ]
  have he : annularMixedScaleJet W V₀ U D r s n a ν ξ =
      fun y => ((-2 * Real.log U : ℝ) : ℂ) ^ n *
        annularCutoffNormTwist (annularMixedWindow W r s) (profileEulerIterCLM n V₀)
          (D / U ^ (2 * ξ)) ((a : ℂ) + (ν : ℂ) * Complex.I) y := by
    funext y
    rw [annularMixedScaleJet_formula W V₀ (V₀.smooth ⊤) U D hU r s n a ν ξ y]
    simp only [annularCutoffNormTwist, profileEulerIterCLM_apply]
  rw [he]
  have hR : 0 ≤ D / U ^ (2 * ξ) := div_nonneg hD (Real.rpow_pos_of_pos hU _).le
  have hbase := hb (D / U ^ (2 * ξ)) hR ((a : ℂ) + (ν : ℂ) * Complex.I)
    (by simpa using ha)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hbase
  have hn : ‖((-2 * Real.log U : ℝ) : ℂ) ^ n‖ ≤
      (2 : ℝ) ^ n * (1 + |Real.log U|) ^ n := by
    rw [logScaleFactor_norm]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |Real.log U| ≤ 1 + |Real.log U|) n)
      (by positivity)
  calc
    _ ≤ ‖((-2 * Real.log U : ℝ) : ℂ) ^ n‖ *
        testSeminorm (annularCutoffNormTwist (annularMixedWindow W r s)
          (profileEulerIterCLM n V₀) (D / U ^ (2 * ξ))
          ((a : ℂ) + (ν : ℂ) * Complex.I)) J A := testSeminorm_const_mul_le _ _ J A
    _ ≤ ‖((-2 * Real.log U : ℝ) : ℂ) ^ n‖ * (C * (1 + |ν|) ^ J) :=
      mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
    _ ≤ ((2 : ℝ) ^ n * (1 + |Real.log U|) ^ n) * (C * (1 + |ν|) ^ J) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by ring

/-- The same actual mixed derivatives retain the original common annulus.
The scalar C is fixed before all moving variables, and the only additional
scale cost is a log power whose order is exactly the ξ₃ derivative order. -/
theorem annular_mixed_scale_jet_slice_control (W : SmoothAnnularTest)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1) (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (r s n J : ℕ) (H M A : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 0 < U → ∀ D : ℝ, 0 ≤ D →
      ∀ T : ℝ, 0 ≤ T → ∀ ξ a ν : ℝ, |a| ≤ H → |ν| ≤ M * (1 + T) →
        SliceControl J A (C * (1 + |Real.log U|) ^ n) (J : ℝ)
          W.lower W.upper T (annularMixedScaleJet W V U D r s n a ν ξ) := by
  obtain ⟨C, hC, hb⟩ := annular_mixed_scale_jet_testSeminorm W V hV hone hzero
    r s n J H A hH
  refine ⟨C * (1 + M) ^ J, mul_pos hC (by positivity), ?_⟩
  intro U hU D hD T hT ξ a ν ha hν
  refine ⟨annularMixedScaleJet_smooth W V hV U D hU r s n a ν ξ,
    annularMixedScaleJet_support W V hV U D hU r s n a ν ξ, ?_⟩
  calc
    _ ≤ C * (1 + |Real.log U|) ^ n * (1 + |ν|) ^ J := hb U hU D hD ξ a ν ha
    _ ≤ C * (1 + |Real.log U|) ^ n * ((1 + M) ^ J * (1 + T) ^ (J : ℝ)) :=
      mul_le_mul_of_nonneg_left (polynomial_twist_height hM hT hν J) (by positivity)
    _ = _ := by ring

end HeckeSkeleton.Moments.UniformAmplify
