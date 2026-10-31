import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MomentProfileScaling
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl

/-!
# Actual Euler-seminorm normalization of all moment profiles

The producer can normalize a child by a positive envelope before its next
recursive call. This file proves the normalization for the literal finite
Euler-integral seminorm, uniformly for both ideal tests and every prime
window. The extracted polynomial energy factor is proved in the independent
low-level `MomentProfileScaling` module. No moment bound or weighted Fourier
mass estimate is assumed or concluded here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped BigOperators Classical ContDiff

/-- Every Euler derivative is complex-linear under a constant scalar. -/
theorem eulerDerivativeOrder_const_mul (f : ℝ → ℂ) (c : ℂ) (j : ℕ) :
    eulerDerivativeOrder j (fun y => c * f y) =
      fun y => c * eulerDerivativeOrder j f y := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hs (g : ℝ → ℂ) : eulerDerivativeOrder (j + 1) g =
        eulerDerivative (eulerDerivativeOrder j g) := by
      unfold eulerDerivativeOrder
      rw [Function.iterate_succ_apply']
    rw [hs, hs, ih]
    funext y
    simp only [eulerDerivative, deriv_const_mul_field]
    ring

/-- The integral is the repository's actual Euler-weighted integral. -/
theorem testIntegral_const_mul (f : ℝ → ℂ) (c : ℂ) (j : ℕ) (A : ℝ) :
    testIntegral (fun y => c * f y) j A = ‖c‖ * testIntegral f j A := by
  unfold testIntegral
  simp_rw [eulerDerivativeOrder_const_mul, norm_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by ring

/-- Constant scaling controls the full finite maximum, including its zero. -/
theorem testSeminorm_const_mul_le (f : ℝ → ℂ) (c : ℂ) (J : ℕ) (A : ℝ) :
    testSeminorm (fun y => c * f y) J A ≤ ‖c‖ * testSeminorm f J A := by
  apply testSeminorm_le_of_integrals _ J A _
    (mul_nonneg (norm_nonneg c) (testSeminorm_nonneg f J A))
  intro j hj
  rw [testIntegral_const_mul]
  exact mul_le_mul_of_nonneg_left (testIntegral_le_testSeminorm f A hj) (norm_nonneg c)

/-- Smoothness and the same annulus are retained for each actual slice. -/
theorem sliceControl_const_mul {f : ℝ → ℂ} {J : ℕ} {A C H a b T : ℝ}
    (h : SliceControl J A C H a b T f) (c : ℂ) :
    SliceControl J A (‖c‖ * C) H a b T (fun y => c * f y) := by
  obtain ⟨hsmooth, hsupport, hbound⟩ := h
  refine ⟨contDiff_const.mul hsmooth,
    fun y hy => hsupport y (right_ne_zero_of_mul hy), ?_⟩
  calc
    _ ≤ ‖c‖ * testSeminorm f J A := testSeminorm_const_mul_le f c J A
    _ ≤ ‖c‖ * (C * (1 + T) ^ H) := mul_le_mul_of_nonneg_left hbound (norm_nonneg c)
    _ = (‖c‖ * C) * (1 + T) ^ H := by ring

variable {K : Type} [Field K] [NumberField K] {omegaChar psiChar : HeckeCharacter K}

/-- The common bound covers all three ideal slices and every prime slice. -/
theorem scaledMomentProfiles_control {d : MomentData K omegaChar psiChar}
    {J : ℕ} {A C H a b T : ℝ}
    (h : ModelProfileControl d J A C H a b T) (r : ℝ) (hr : 0 < r) :
    ModelProfileControl (scaledMomentProfiles d r hr) J A (r * C) H a b T := by
  intro q
  cases q with
  | inverse u =>
    simpa only [modelProfile, scaledMomentProfiles, scaledIdealTest,
      Complex.norm_of_nonneg hr.le] using
      sliceControl_const_mul (modelProfileControl_inverse h u) (r : ℂ)
  | plain₁ u =>
    simpa only [modelProfile, scaledMomentProfiles, scaledIdealTest,
      Complex.norm_of_nonneg hr.le] using
      sliceControl_const_mul (modelProfileControl_plain₁ h u) (r : ℂ)
  | plain₂ u =>
    simpa only [modelProfile, scaledMomentProfiles, scaledIdealTest,
      Complex.norm_of_nonneg hr.le] using
      sliceControl_const_mul (modelProfileControl_plain₂ h u) (r : ℂ)
  | prime j =>
    simpa only [modelProfile, scaledMomentProfiles, scaledGeometry, scaledPrimeWindow,
      Complex.norm_of_nonneg hr.le] using
      sliceControl_const_mul (modelProfileControl_prime h j) (r : ℂ)

/-- A true envelope produces the same literal unit ball for every child
profile. It may depend on a Fourier parameter; the energy factor must then
be included in the common weighted kernel before estimating its mass. -/
theorem normalizedMomentProfiles_unit_control {d : MomentData K omegaChar psiChar}
    {J : ℕ} {A C H a b T E : ℝ}
    (h : ModelProfileControl d J A C H a b T) (hE : 0 < E)
    (henvelope : C * (1 + T) ^ H ≤ E) :
    ModelProfileControl (scaledMomentProfiles d E⁻¹ (inv_pos.mpr hE))
      J A 1 0 a b 0 := by
  have hscaled := scaledMomentProfiles_control h E⁻¹ (inv_pos.mpr hE)
  intro q
  obtain ⟨hsmooth, hsupport, hbound⟩ := hscaled q
  refine ⟨hsmooth, hsupport, ?_⟩
  calc
    _ ≤ (E⁻¹ * C) * (1 + T) ^ H := hbound
    _ = E⁻¹ * (C * (1 + T) ^ H) := by ring
    _ ≤ E⁻¹ * E := mul_le_mul_of_nonneg_left henvelope (inv_nonneg.mpr hE.le)
    _ = 1 * (1 + (0 : ℝ)) ^ (0 : ℝ) := by rw [inv_mul_cancel₀ hE.ne']; norm_num

end HeckeSkeleton.Moments.EngineInduction
