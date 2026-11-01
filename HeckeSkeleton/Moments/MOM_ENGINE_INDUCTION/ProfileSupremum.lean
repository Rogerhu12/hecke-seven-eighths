import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.GeneralBaseTerminal
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import HeckeSkeleton.ThetaKernel.TestMellin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The source Euler-integral control supplies the actual profile supremum

For a smooth test supported in a fixed positive interval, integration of
its derivative from zero gives `‖f y‖ ≤ ∫₀^∞ ‖f'‖`. This integral is
exactly the order-one, weight-zero `Iint` already proved integrable by
`ThetaKernel.TestMellin`. It is bounded by the source's literal
`testSeminorm f 1 0`; no independent supremum hypothesis is introduced.

The last theorem consumes `ModelProfileControl` for every actual ideal
test and prime window and supplies the common absolute-base certificate.
Its coefficient and height degree are fixed before height and node.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory Set Filter NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify
open scoped BigOperators Classical ContDiff Topology

universe v

private theorem firstEuler_integrand (V : SmoothAnnularTest) (y : ℝ) (hy : 0 < y) :
    ‖eul V 1 y‖ * y ^ (-(0 : ℝ) - 1) = ‖deriv V.toFun y‖ := by
  have he : eul V 1 y = (y : ℂ) * deriv V.toFun y := by
    simp [eul, eulerDerivativeOrder, eulerDerivative]
  rw [he, norm_mul, Complex.norm_of_nonneg hy.le]
  simp only [neg_zero, zero_sub, Real.rpow_neg_one]
  field_simp [hy.ne'] <;> ring

private theorem smoothAnnular_norm_le_Iint (V : SmoothAnnularTest) (y : ℝ) :
    ‖V.toFun y‖ ≤ Iint V 1 0 := by
  have hfi : IntegrableOn (fun x : ℝ => ‖deriv V.toFun x‖) (Ioi 0) :=
    (integrableOn_Iint V 1 0).congr_fun
      (fun x hx => firstEuler_integrand V x hx) measurableSet_Ioi
  have hI : Iint V 1 0 = ∫ x in Ioi (0 : ℝ), ‖deriv V.toFun x‖ := by
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => firstEuler_integrand V x hx)
  rw [hI]
  have hz : V.toFun 0 = 0 := (good_toFun V).zero 0 (by
    intro hmem
    exact (not_le.mpr V.lower_pos) hmem.1)
  by_cases hy : 0 ≤ y
  · have hdiff : Differentiable ℝ V.toFun := V.smooth.differentiable (by simp)
    have hdc : Continuous (deriv V.toFun) :=
      (contDiff_infty_iff_deriv.mp V.smooth).2.continuous
    have hn : ‖V.toFun y - V.toFun 0‖ ≤
        ∫ x in (0 : ℝ)..y, ‖deriv V.toFun x‖ := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hy V.smooth.continuous.continuousOn
      · intro x _
        exact (hdiff x).differentiableWithinAt
      · exact Filter.Eventually.of_forall (fun _ _ => le_rfl)
      · exact hdc.norm.intervalIntegrable 0 y
    rw [hz, sub_zero, intervalIntegral.integral_of_le hy] at hn
    apply hn.trans
    exact setIntegral_mono_set hfi
      (Filter.Eventually.of_forall fun x => norm_nonneg (deriv V.toFun x))
      (Filter.Eventually.of_forall fun _ hx => hx.1)
  · have hzero : V.toFun y = 0 := (good_toFun V).zero y (by
      intro hmem
      exact hy (V.lower_pos.le.trans hmem.1))
    rw [hzero, norm_zero]
    exact integral_nonneg (fun x => norm_nonneg (deriv V.toFun x))

/-- The first Euler integral bounds every value of an actual compact
annular test, including values outside its support. -/
theorem smoothAnnular_norm_le_testIntegral (V : SmoothAnnularTest) (y : ℝ) :
    ‖V.toFun y‖ ≤ testIntegral V.toFun 1 0 := by
  have h := smoothAnnular_norm_le_Iint V y
  have hnonneg := Iint_nonneg V 1 (-1 / 4)
  have heq := Iint_add_eq V 1 0
  linarith

/-- Any seminorm containing the first Euler derivative suffices for the
pointwise bound. The weight parameter is genuinely zero. -/
theorem smoothAnnular_norm_le_testSeminorm (V : SmoothAnnularTest)
    (J : ℕ) (hJ : 1 ≤ J) (y : ℝ) :
    ‖V.toFun y‖ ≤ testSeminorm V.toFun J 0 :=
  (smoothAnnular_norm_le_testIntegral V y).trans
    (HeckeSkeleton.ThetaKernel.testIntegral_le_seminorm V 1 J hJ 0)

/-- Consume the literal source `SliceControl`; the supremum bound is a
consequence of its smoothness, positive support interval and Euler norm. -/
theorem sliceControl_norm_le {f : ℝ → ℂ} {J : ℕ} {C H a b T : ℝ}
    (hJ : 1 ≤ J) (ha : 0 < a) (hab : a ≤ b)
    (h : SliceControl J 0 C H a b T f) (y : ℝ) :
    ‖f y‖ ≤ C * (1 + T) ^ H := by
  let V : SmoothAnnularTest := {
    toFun := f
    smooth := h.1
    lower := a
    upper := b
    lower_pos := ha
    upper_ge := hab
    support := fun _ hy => h.2.1 _ hy }
  exact (smoothAnnular_norm_le_testSeminorm V J hJ y).trans h.2.2

variable {K : Type} [Field K] [NumberField K]

/-- Uniform absolute-base components directly from the current #10
profile interface, with no additional pointwise-profile assumption.
The actual row, mask, slot geometry and equal-product rectangles survive. -/
theorem uniform_modelProfileControl_base_components (cap : ℕ)
    (C H a b ρ padding σ boundary : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (ha : 0 < a) (hab : a ≤ b) :
    ∃ D A : ℝ, D = generalBaseConstant K cap b C C C ∧
      A = baseHeightDegree cap H H H ∧ 0 ≤ D ∧ 0 ≤ A ∧
      ∀ T : ℝ, 0 ≤ T → ∀ {omegaCharacter psiCharacter : HeckeCharacter K}
        (n : Node K omegaCharacter psiCharacter)
        (U : ℝ), 1 ≤ U → n.data.geometry.slotCount ≤ cap →
        ModelProfileControl n.data 1 0 C H a b T →
        n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤
          ρ + padding + ρ / 6 →
        Nonempty (TerminalComponents.{v} (n.normalizedEnergy U 0) U T D A
          ρ padding σ boundary) := by
  obtain ⟨D, A, hD, hA, hDn, hAn, hbase⟩ :=
    general_uniform_polynomial_height_base_components (K := K) cap
      b C C C H H H ρ padding σ boundary (ha.trans_le hab)
      hC hC hC hH hH hH
  refine ⟨D, A, hD, hA, hDn, hAn, ?_⟩
  intro T hT omegaCharacter psiCharacter n U hU hcount hprofiles hlength
  apply hbase T hT n U 0 hU hcount
  · intro u _ y hy
    exact ((modelProfileControl_plain₁ hprofiles u).2.1 y hy).2
  · intro u _ y hy
    exact ((modelProfileControl_plain₂ hprofiles u).2.1 y hy).2
  · intro u _ y
    exact sliceControl_norm_le le_rfl ha hab (modelProfileControl_plain₁ hprofiles u) y
  · intro u _ y
    exact sliceControl_norm_le le_rfl ha hab (modelProfileControl_plain₂ hprofiles u) y
  · intro i y hy
    exact ((modelProfileControl_prime hprofiles i).2.1 y hy).2
  · intro i y
    exact sliceControl_norm_le le_rfl ha hab (modelProfileControl_prime hprofiles i) y
  · exact hlength

end HeckeSkeleton.Moments.EngineInduction
